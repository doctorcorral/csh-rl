{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Synthesized.MazeE2E
--
-- END-TO-END VERIFIED PIPELINE: Observations → Policy
--
-- Complete demo for the 1D Maze (P0 → P1 → P2):
--
--   STEP 1. OBSERVE  – trace comparisons from environment interaction
--   STEP 2. SYNTHESIZE – CEGIS produces ranking predicates from observations
--   STEP 3. VERIFY  – prove the synthesized ranking preserves action-values
--   STEP 4. CONSTRUCT – CoindHomo from the verified ranking (automatic)
--   STEP 5. EXTRACT  – policy from the synthesized ranking
--   STEP 6. EXECUTE  – roll out the policy: P0 →Fwd P1 →Fwd P2 (goal!)
--   STEP 7. CONFIRM  – synthesized policy agrees with EC's Finder
--
-- All --safe, no postulates, fully verified.
------------------------------------------------------------------------

module CSHRL.Tasks.Synthesized.MazeE2E where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc; _≤_; _⊔_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; _∷_; []; length)
open import Codata.Guarded.Stream using (Stream; head; tail; tabulate)
open import Function using (_∘_)
open import Relation.Nullary using (Dec; yes; no; ¬_)

------------------------------------------------------------------------
-- DOMAIN: 1D Maze
--
--   P0 ──Fwd──▶ P1 ──Fwd──▶ P2 (goal, reward 1)
--   P0 ◀──Bwd── P1 ◀──Bwd── P2
------------------------------------------------------------------------

data State : Set where
  P0 P1 P2 : State

data Action : Set where
  Fwd Bwd : Action

move : State → Action → State
move P0 Fwd = P1
move P0 Bwd = P0
move P1 Fwd = P2
move P1 Bwd = P0
move P2 Fwd = P2
move P2 Bwd = P1

reward-fn : State → ℕ
reward-fn P2 = 1
reward-fn _  = 0

step : State → Action → State × ℕ
step s a = (move s a , reward-fn (move s a))

all-actions : List Action
all-actions = Fwd ∷ Bwd ∷ []

------------------------------------------------------------------------
-- SYNTHESIS FRAMEWORK
--
-- Opens FDMDPSynthesis, which provides Core (solve, value,
-- action-value, CoindHomo) plus the synthesis infrastructure
-- (RankModel, WithCEGIS, ModelPreserves, WithCorrectModel).
------------------------------------------------------------------------

open import CSHRL.Synthesis.FiniteDeterministicMDP
open FDMDPSynthesis State Action step all-actions

data MazeFeature : Set where
  is-goal : MazeFeature

eval-maze-feature : MazeFeature → State → Bool
eval-maze-feature is-goal P0 = false
eval-maze-feature is-goal P1 = false
eval-maze-feature is-goal P2 = true

open WithStateFeatures MazeFeature eval-maze-feature
open WithCEGIS (is-goal ∷ [])

------------------------------------------------------------------------
-- EC (for Finder comparison only — qualified to avoid name clashes)
------------------------------------------------------------------------

open import CSHRL.EnvironmentClass.FiniteDeterministicMDP as FDMDP-Mod

private
  _≤?ₙ_ : (m n : ℕ) → Dec (m ≤ n)
  zero  ≤?ₙ _     = yes z≤n
  suc _ ≤?ₙ zero  = no λ ()
  suc m ≤?ₙ suc n with m ≤?ₙ n
  ... | yes p  = yes (s≤s p)
  ... | no  np = no λ { (s≤s q) → np q }

module Finder = FDMDP-Mod.FiniteDeterministicMDP
  State Action ℕ step _≤_ _≤?ₙ_ (λ {_} → ≤-refl) _⊔_ 0 all-actions Fwd 2

------------------------------------------------------------------------
-- ═══════════════════════════════════════════════════════════════════
-- STEP 1: OBSERVE — Trace comparisons from environment interaction
-- ═══════════════════════════════════════════════════════════════════
--
-- We interact with the environment and compare action traces:
--   "At state s, is trace(Bwd) ≤ trace(Fwd)?"
--
-- Results:
--   P0: Bwd→P0(0), Fwd→P1(0→P2→1) → Bwd ≤ Fwd = TRUE
--   P1: Bwd→P0(0), Fwd→P2(1)       → Bwd ≤ Fwd = TRUE
--   P2: Bwd→P1(0), Fwd→P2(1)       → Bwd ≤ Fwd = TRUE
--
--   P0: Fwd→P1(0→1), Bwd→P0(0→0)   → Fwd ≤ Bwd = FALSE
--   P1: Fwd→P2(1),   Bwd→P0(0)     → Fwd ≤ Bwd = FALSE
------------------------------------------------------------------------

obs-bwd≤fwd : List PredObs
obs-bwd≤fwd = (P0 , true) ∷ (P1 , true) ∷ (P2 , true) ∷ []

obs-fwd≤bwd : List PredObs
obs-fwd≤bwd = (P0 , false) ∷ (P1 , false) ∷ []

------------------------------------------------------------------------
-- ═══════════════════════════════════════════════════════════════════
-- STEP 2: SYNTHESIZE — CEGIS produces ranking predicates
-- ═══════════════════════════════════════════════════════════════════
--
-- Starting from all PredProg terms (version space of size 3),
-- CEGIS refines by each observation and returns a consistent candidate.
------------------------------------------------------------------------

-- Version space: {truep, falsep, feat(is-goal)} = 3 candidates
check-vs-size : length (initial-vs 0) ≡ 3
check-vs-size = refl

-- CEGIS synthesizes: "Bwd ≤ Fwd" = truep (always true)
synth-bwd≤fwd : synth-rank-pred 0 obs-bwd≤fwd ≡ just truep
synth-bwd≤fwd = refl

-- CEGIS synthesizes: "Fwd ≤ Bwd" = falsep (never true)
synth-fwd≤bwd : synth-rank-pred 0 obs-fwd≤bwd ≡ just falsep
synth-fwd≤bwd = refl

-- Assemble the synthesized ranking model
synth-prefer : Action → Action → PredProg
synth-prefer Fwd Fwd = truep
synth-prefer Fwd Bwd = falsep
synth-prefer Bwd Fwd = truep
synth-prefer Bwd Bwd = truep

synth-rank : RankModel
synth-rank = record { prefer = synth-prefer }

-- Verify: CEGIS output matches the assembled model
check-cegis-bf : synth-rank-pred 0 obs-bwd≤fwd
               ≡ just (RankModel.prefer synth-rank Bwd Fwd)
check-cegis-bf = refl

check-cegis-fb : synth-rank-pred 0 obs-fwd≤bwd
               ≡ just (RankModel.prefer synth-rank Fwd Bwd)
check-cegis-fb = refl

------------------------------------------------------------------------
-- ═══════════════════════════════════════════════════════════════════
-- STEP 3: VERIFY — Prove the synthesized ranking preserves values
-- ═══════════════════════════════════════════════════════════════════
--
-- Domain analysis: all states converge to solve = 1 for n ≥ 1.
-- This makes value streams trivially ordered: every pair (s₁,s₂)
-- satisfies value s₁ ≤ₛ value s₂ whenever solve s₁ 0 ≤ solve s₂ 0.
------------------------------------------------------------------------

≤ₛ-refl′ : ∀ (s : Stream ℕ) → s ≤ₛ s
head≤ (≤ₛ-refl′ s) = ≤-refl
tail≤ (≤ₛ-refl′ s) = ≤ₛ-refl′ (tail s)

private
  iter : ℕ → Stream ℕ → ℕ
  iter zero    s = head s
  iter (suc n) s = iter n (tail s)

  iter-tab : ∀ (f : ℕ → ℕ) n → iter n (tabulate f) ≡ f n
  iter-tab f zero    = refl
  iter-tab f (suc n) = iter-tab (f ∘ suc) n

  mutual
    p2-is-1 : ∀ n → solve P2 n ≡ 1
    p2-is-1 zero = refl
    p2-is-1 (suc n) rewrite p2-is-1 n | p1-is-1 n = refl

    p1-is-1 : ∀ n → solve P1 n ≡ 1
    p1-is-1 zero = refl
    p1-is-1 (suc zero) rewrite p2-is-1 zero = refl
    p1-is-1 (suc (suc n)) rewrite p2-is-1 (suc n) | p0-suc-is-1 n = refl

    p0-suc-is-1 : ∀ n → solve P0 (suc n) ≡ 1
    p0-suc-is-1 zero rewrite p1-is-1 zero = refl
    p0-suc-is-1 (suc n) rewrite p1-is-1 (suc n) | p0-suc-is-1 n = refl

  build-≤ₛ : ∀ (s₁ s₂ : Stream ℕ) →
    (∀ n → iter n s₁ ≤ iter n s₂) → s₁ ≤ₛ s₂
  head≤ (build-≤ₛ s₁ s₂ g) = g 0
  tail≤ (build-≤ₛ s₁ s₂ g) =
    build-≤ₛ (tail s₁) (tail s₂) (λ n → g (suc n))

  gen : ∀ s₁ s₂ →
    (solve s₁ 0 ≤ solve s₂ 0) →
    ∀ n → iter n (value s₁) ≤ iter n (value s₂)
  gen s₁ s₂ base zero
    rewrite iter-tab (solve s₁) 0 | iter-tab (solve s₂) 0 = base
  gen P0 s₂ _ (suc n)
    rewrite iter-tab (solve P0) (suc n) | p0-suc-is-1 n
    with s₂
  ... | P0 rewrite iter-tab (solve P0) (suc n) | p0-suc-is-1 n = ≤-refl
  ... | P1 rewrite iter-tab (solve P1) (suc n) | p1-is-1 (suc n) = ≤-refl
  ... | P2 rewrite iter-tab (solve P2) (suc n) | p2-is-1 (suc n) = ≤-refl
  gen P1 s₂ _ (suc n)
    rewrite iter-tab (solve P1) (suc n) | p1-is-1 (suc n)
    with s₂
  ... | P0 rewrite iter-tab (solve P0) (suc n) | p0-suc-is-1 n = ≤-refl
  ... | P1 rewrite iter-tab (solve P1) (suc n) | p1-is-1 (suc n) = ≤-refl
  ... | P2 rewrite iter-tab (solve P2) (suc n) | p2-is-1 (suc n) = ≤-refl
  gen P2 s₂ _ (suc n)
    rewrite iter-tab (solve P2) (suc n) | p2-is-1 (suc n)
    with s₂
  ... | P0 rewrite iter-tab (solve P0) (suc n) | p0-suc-is-1 n = ≤-refl
  ... | P1 rewrite iter-tab (solve P1) (suc n) | p1-is-1 (suc n) = ≤-refl
  ... | P2 rewrite iter-tab (solve P2) (suc n) | p2-is-1 (suc n) = ≤-refl

value-≤ : ∀ s₁ s₂ → solve s₁ 0 ≤ solve s₂ 0 → value s₁ ≤ₛ value s₂
value-≤ s₁ s₂ base =
  build-≤ₛ (value s₁) (value s₂) (gen s₁ s₂ base)

-- The preservation proof for the CEGIS-synthesized ranking.
-- Fwd Bwd is absurd: eval falsep s ≡ true is impossible.
synth-preserves : ModelPreserves synth-rank
head≤ (synth-preserves Fwd Fwd s _) = ≤-refl
tail≤ (synth-preserves Fwd Fwd s _) = ≤ₛ-refl′ _
head≤ (synth-preserves Bwd Fwd P0 _) = z≤n
tail≤ (synth-preserves Bwd Fwd P0 _) = value-≤ P0 P1 z≤n
head≤ (synth-preserves Bwd Fwd P1 _) = z≤n
tail≤ (synth-preserves Bwd Fwd P1 _) = value-≤ P0 P2 z≤n
head≤ (synth-preserves Bwd Fwd P2 _) = z≤n
tail≤ (synth-preserves Bwd Fwd P2 _) = value-≤ P1 P2 ≤-refl
head≤ (synth-preserves Bwd Bwd s _) = ≤-refl
tail≤ (synth-preserves Bwd Bwd s _) = ≤ₛ-refl′ _

------------------------------------------------------------------------
-- ═══════════════════════════════════════════════════════════════════
-- STEP 4: CONSTRUCT — CoindHomo from verified ranking (automatic)
-- ═══════════════════════════════════════════════════════════════════
--
-- The synthesized ranking + preservation proof give us a
-- Coinductive Homomorphism: the ranking is formally correct.
------------------------------------------------------------------------

open WithCorrectModel synth-rank synth-preserves

verified-ranking : ∀ a b s →
  RankHolds synth-rank s a b →
  action-value s a ≤ₛ action-value s b
verified-ranking = CoindHomo.preserves SynthesizedHomo

------------------------------------------------------------------------
-- ═══════════════════════════════════════════════════════════════════
-- STEP 5: EXTRACT — Policy from the synthesized ranking
-- ═══════════════════════════════════════════════════════════════════
--
-- The synthesized ranking tells us: at every state, Fwd ≥ Bwd.
-- So the optimal action is always Fwd.
------------------------------------------------------------------------

synth-policy : State → Action
synth-policy s with rank-eval synth-rank s Bwd Fwd
... | true  = Fwd
... | false = Bwd

test-synth-P0 : synth-policy P0 ≡ Fwd
test-synth-P0 = refl

test-synth-P1 : synth-policy P1 ≡ Fwd
test-synth-P1 = refl

test-synth-P2 : synth-policy P2 ≡ Fwd
test-synth-P2 = refl

------------------------------------------------------------------------
-- ═══════════════════════════════════════════════════════════════════
-- STEP 6: EXECUTE — Roll out the synthesized policy
-- ═══════════════════════════════════════════════════════════════════
------------------------------------------------------------------------

run-synth : State → ℕ → List (Action × State)
run-synth _ zero = []
run-synth s (suc n) =
  let a  = synth-policy s
      s' = proj₁ (step s a)
  in (a , s') ∷ run-synth s' n

-- Starting from P0, the policy reaches the goal in 2 steps
test-trajectory : run-synth P0 3
  ≡ (Fwd , P1) ∷ (Fwd , P2) ∷ (Fwd , P2) ∷ []
test-trajectory = refl

-- Rewards along the trajectory
collect-rewards : State → ℕ → List ℕ
collect-rewards _ zero = []
collect-rewards s (suc n) =
  let a = synth-policy s
      (s' , r) = step s a
  in r ∷ collect-rewards s' n

test-rewards : collect-rewards P0 4 ≡ 0 ∷ 1 ∷ 1 ∷ 1 ∷ []
test-rewards = refl

------------------------------------------------------------------------
-- ═══════════════════════════════════════════════════════════════════
-- STEP 7: CONFIRM — EC's Finder agrees with the synthesized policy
-- ═══════════════════════════════════════════════════════════════════
--
-- The Environment Class computes find-policy from raw traces
-- (independent of synthesis). The synthesized policy matches.
------------------------------------------------------------------------

test-finder-P0 : Finder.find-policy P0 2 ≡ Fwd
test-finder-P0 = refl

test-finder-P1 : Finder.find-policy P1 2 ≡ Fwd
test-finder-P1 = refl

test-finder-P2 : Finder.find-policy P2 2 ≡ Fwd
test-finder-P2 = refl

-- Finder agrees with synthesized policy at every state
finder-agrees : ∀ s → Finder.find-policy s 2 ≡ synth-policy s
finder-agrees P0 = refl
finder-agrees P1 = refl
finder-agrees P2 = refl

------------------------------------------------------------------------
-- SUMMARY
--
-- The complete pipeline, from raw data to verified policy:
--
--   1. OBSERVE:    5 trace comparisons → PredObs lists
--   2. SYNTHESIZE: CEGIS → truep (Bwd ≤ Fwd), falsep (Fwd ≤ Bwd)
--   3. VERIFY:     Preservation proof → synth-preserves (domain-specific)
--   4. CONSTRUCT:  CoindHomo (SynthesizedHomo) — automatic from (2)+(3)
--   5. EXTRACT:    synth-policy s = Fwd (at every state)
--   6. EXECUTE:    P0 →Fwd P1 →Fwd P2 →Fwd P2 → ... (goal reached!)
--   7. CONFIRM:    Finder.find-policy ≡ synth-policy (independent check)
--
-- Guarantees:
--   • CoindHomo: the synthesized ranking preserves action-value ordering
--   • Policy correctness: synth-policy picks the action ranked highest
--   • Agreement: synthesis matches the EC's Finder (cross-validation)
--   • Safety: --safe, no postulates, termination/productivity checked
------------------------------------------------------------------------
