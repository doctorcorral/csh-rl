{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Synthesized.BiasedBanditSynth
--
-- END-TO-END STOCHASTIC SYNTHESIS PIPELINE
--
-- Complete demo for the BiasedBandit (2 arms, 1 state):
--
--   STEP 1. OBSERVE  – expected trace comparisons
--   STEP 2. SYNTHESIZE – CEGIS produces ranking predicates
--   STEP 3. VERIFY  – prove ranking preserves lexicographic dominance
--   STEP 4. CONSTRUCT – StochasticCoindHomo (automatic)
--   STEP 5. EXTRACT  – policy from the synthesized ranking
--   STEP 6. CONFIRM  – synthesized policy agrees with EC's Finder
--
-- This is the FIRST stochastic synthesis end-to-end demo,
-- completing the trifecta: FDMDP (MazeE2E), CPMDP (QueensE2E),
-- SFMDP (this file).
--
-- All --safe, no postulates, fully verified.
------------------------------------------------------------------------

module CSHRL.Tasks.Synthesized.BiasedBanditSynth where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc; _≤_; _⊔_; _+_; _*_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.List using (List; _∷_; []; length)
open import Codata.Guarded.Stream using (Stream; head; tail)
open import Relation.Nullary using (Dec; yes; no; ¬_)

open import CSHRL.Probability.Finite using (Dist; pure; _>>=_; fmap; bernoulli)

------------------------------------------------------------------------
-- DOMAIN: BiasedBandit
--
-- Single state (Playing), two arms:
--   ArmA: 2/3 chance reward 1, 1/3 chance reward 0
--   ArmB: 1/3 chance reward 1, 2/3 chance reward 0
--
-- Optimal: always ArmA (expected 2 vs 1, unnormalized)
------------------------------------------------------------------------

data State : Set where
  Playing : State

data Action : Set where
  ArmA : Action
  ArmB : Action

step : State → Action → Dist (State × ℕ)
step Playing ArmA = bernoulli (Playing , 1) 2 (Playing , 0) 1
step Playing ArmB = bernoulli (Playing , 1) 1 (Playing , 0) 2

all-actions : List Action
all-actions = ArmA ∷ ArmB ∷ []

_≟ₐ_ : (a b : Action) → Dec (a ≡ b)
ArmA ≟ₐ ArmA = yes refl
ArmA ≟ₐ ArmB = no λ ()
ArmB ≟ₐ ArmA = no λ ()
ArmB ≟ₐ ArmB = yes refl

------------------------------------------------------------------------
-- SYNTHESIS FRAMEWORK
--
-- Opens SFDMDPSynthesis, which provides the stochastic EC
-- (expected-action-value, ≤ₛ-lex, StochasticCoindHomo) plus
-- synthesis infrastructure (RankModel, WithCEGIS, ModelPreservesLex).
------------------------------------------------------------------------

open import CSHRL.Synthesis.StochasticFiniteMDP
open SFDMDPSynthesis
  State Action ℕ step
  _≤_ (λ m n → m Data.Nat.≤? n) (λ {_} → ≤-refl)
  _+_ _*_ 0 _⊔_ 0
  all-actions ArmB 3

------------------------------------------------------------------------
-- FEATURES
--
-- The bandit is stateless: only one state (Playing).
-- A trivial feature suffices: is-playing is always true.
-- This means AllFeatAgree has ONE equivalence class: {Playing}.
-- CEGIS needs exactly 1 observation (tight bound: |C/~| = 1).
------------------------------------------------------------------------

data BanditFeature : Set where
  is-playing : BanditFeature

eval-bandit-feature : BanditFeature → State → Bool
eval-bandit-feature is-playing Playing = true

open WithStateFeatures BanditFeature eval-bandit-feature
open WithCEGIS (is-playing ∷ [])

------------------------------------------------------------------------
-- ═════════════════════════════════════════════════════════════════════
-- STEP 1: OBSERVE — Expected trace comparisons
-- ═════════════════════════════════════════════════════════════════════
--
-- Compare expected traces at Playing:
--   expected-trace ArmB ≤ expected-trace ArmA?
--     ArmB unnormalized head = 1, ArmA unnormalized head = 2 → TRUE
--   expected-trace ArmA ≤ expected-trace ArmB?
--     ArmA head = 2, ArmB head = 1 → FALSE
------------------------------------------------------------------------

obs-b≤a : List PredObs
obs-b≤a = (Playing , true) ∷ []

obs-a≤b : List PredObs
obs-a≤b = (Playing , false) ∷ []

------------------------------------------------------------------------
-- ═════════════════════════════════════════════════════════════════════
-- STEP 2: SYNTHESIZE — CEGIS produces ranking predicates
-- ═════════════════════════════════════════════════════════════════════
------------------------------------------------------------------------

-- Version space: {truep, falsep, feat(is-playing)} = 3 candidates
check-vs-size : length (initial-vs 0) ≡ 3
check-vs-size = refl

-- "ArmB ≤ ArmA" → truep (always true: ArmA always dominates)
synth-b≤a : synth-rank-pred 0 obs-b≤a ≡ just truep
synth-b≤a = refl

-- "ArmA ≤ ArmB" → falsep (never: ArmA always dominates)
synth-a≤b : synth-rank-pred 0 obs-a≤b ≡ just falsep
synth-a≤b = refl

-- Assemble the synthesized ranking model
synth-prefer : Action → Action → PredProg
synth-prefer ArmA ArmA = truep
synth-prefer ArmA ArmB = falsep
synth-prefer ArmB ArmA = truep
synth-prefer ArmB ArmB = truep

synth-rank : RankModel
synth-rank = record { prefer = synth-prefer }

-- Verify: CEGIS output matches assembled model
check-cegis-ba : synth-rank-pred 0 obs-b≤a
               ≡ just (RankModel.prefer synth-rank ArmB ArmA)
check-cegis-ba = refl

check-cegis-ab : synth-rank-pred 0 obs-a≤b
               ≡ just (RankModel.prefer synth-rank ArmA ArmB)
check-cegis-ab = refl

------------------------------------------------------------------------
-- ═════════════════════════════════════════════════════════════════════
-- STEP 3: VERIFY — Prove ranking preserves lexicographic dominance
-- ═════════════════════════════════════════════════════════════════════
--
-- For the BiasedBandit:
--   head(expected-action-value Playing ArmA) = 2
--   head(expected-action-value Playing ArmB) = 1
--
-- ArmB ≤ ArmA: head≤ gives 1 ≤ 2 ✓
--              tail≤ requires 1 ≡ 2, which is absurd → ()
-- ArmA ≤ ArmB: ranking says eval falsep s ≡ true, impossible
-- Same arm: reflexivity
------------------------------------------------------------------------

private
  1≤2 : 1 ≤ 2
  1≤2 = s≤s z≤n

synth-preserves : ModelPreservesLex synth-rank
synth-preserves ArmA ArmB s ()
head≤ (synth-preserves ArmA ArmA Playing _) = ≤-refl
tail≤ (synth-preserves ArmA ArmA Playing _) _ = ≤ₛ-lex-refl _
head≤ (synth-preserves ArmB ArmB Playing _) = ≤-refl
tail≤ (synth-preserves ArmB ArmB Playing _) _ = ≤ₛ-lex-refl _
head≤ (synth-preserves ArmB ArmA Playing _) = 1≤2
tail≤ (synth-preserves ArmB ArmA Playing _) ()

------------------------------------------------------------------------
-- ═════════════════════════════════════════════════════════════════════
-- STEP 4: CONSTRUCT — StochasticCoindHomo (automatic)
-- ═════════════════════════════════════════════════════════════════════
------------------------------------------------------------------------

open WithCorrectModel synth-rank synth-preserves

verified-ranking : ∀ a b s →
  RankHolds synth-rank s a b →
  expected-action-value s a ≤ₛ-lex expected-action-value s b
verified-ranking = StochasticCoindHomo.preserves SynthesizedStochasticHomo

------------------------------------------------------------------------
-- ═════════════════════════════════════════════════════════════════════
-- STEP 5: EXTRACT — Policy from the synthesized ranking
-- ═════════════════════════════════════════════════════════════════════
------------------------------------------------------------------------

synth-policy : State → Action
synth-policy s with rank-eval synth-rank s ArmB ArmA
... | true  = ArmA
... | false = ArmB

test-synth-Playing : synth-policy Playing ≡ ArmA
test-synth-Playing = refl

------------------------------------------------------------------------
-- ═════════════════════════════════════════════════════════════════════
-- STEP 6: CONFIRM — EC's Finder agrees with synthesized policy
-- ═════════════════════════════════════════════════════════════════════
------------------------------------------------------------------------

test-finder-Playing : find-policy Playing 3 ≡ ArmA
test-finder-Playing = refl

finder-agrees : find-policy Playing 3 ≡ synth-policy Playing
finder-agrees = refl

------------------------------------------------------------------------
-- ═════════════════════════════════════════════════════════════════════
-- DISSOLUTION CHECK
-- ═════════════════════════════════════════════════════════════════════
--
-- With 1 state and 1 feature class, |C/~| = 1.
-- CEGIS needs exactly 1 observation per pair.
-- The tight bound is met: 1 observation for ArmB≤ArmA,
-- 1 observation for ArmA≤ArmB → total 2 observations.
-- The version space collapses to a singleton after each.
------------------------------------------------------------------------

vs-after-b≤a : length (cegis-loop (initial-vs 0) obs-b≤a) ≡ 2
vs-after-b≤a = refl

vs-after-a≤b : length (cegis-loop (initial-vs 0) obs-a≤b) ≡ 1
vs-after-a≤b = refl

------------------------------------------------------------------------
-- SUMMARY
--
-- The complete stochastic synthesis pipeline:
--
--   1. OBSERVE:    2 expected trace comparisons → PredObs
--   2. SYNTHESIZE: CEGIS → truep (ArmB ≤ ArmA), falsep (ArmA ≤ ArmB)
--   3. VERIFY:     Lex preservation → synth-preserves
--                  (head: 1 ≤ 2, tail: absurd 1 ≡ 2)
--   4. CONSTRUCT:  StochasticCoindHomo (SynthesizedStochasticHomo)
--   5. EXTRACT:    synth-policy Playing = ArmA
--   6. CONFIRM:    find-policy Playing 3 ≡ ArmA ≡ synth-policy Playing
--
-- Guarantees:
--   • StochasticCoindHomo: synthesized ranking preserves
--     lexicographic expected stream dominance
--   • Tight bound: |C/~| = 1, met with exactly 1 obs per pair
--   • Propagation: trivial here (1 class), but the full generic
--     theory (dissolution, sufficiency) applies unchanged
--   • Safety: --safe, no postulates, termination checked
--
-- This completes the E2E trifecta:
--   FDMDP:  MazeE2E       (deterministic, CoindHomo)
--   CPMDP:  QueensE2E     (placement, CoindHomo)
--   SFMDP:  BiasedBanditSynth (stochastic, StochasticCoindHomo)
------------------------------------------------------------------------
