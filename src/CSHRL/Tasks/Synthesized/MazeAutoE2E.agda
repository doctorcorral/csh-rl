{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Synthesized.MazeAutoE2E
--
-- 1D MAZE WITHOUT HAND-CRAFTED FEATURES
--
-- The hand-crafted MazeE2E provides is-goal as a domain feature.
-- This demo discovers it from dynamics:
--
--   is-self-loop Fwd  ≡  is-goal  (at every state)
--
-- Pipeline:
--   1. ENUMERATE   4 dynamics-derived features (2 per action)
--   2. FILTER      Remove trivial (constant) features → 3 survive
--   3. SYNTHESIZE  CEGIS → truep / falsep (same as hand-crafted)
--   4. VERIFY      Preservation proof (feature-independent)
--   5. EXTRACT     Policy = Fwd everywhere
--   6. CONFIRM     Finder agrees
--
-- All --safe, no postulates.
------------------------------------------------------------------------

module CSHRL.Tasks.Synthesized.MazeAutoE2E where

open import Data.Bool using (Bool; true; false; not; if_then_else_; _∧_; _∨_)
open import Data.Nat using (ℕ; zero; suc; _≤_; _⊔_; z≤n; s≤s; _≡ᵇ_)
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
-- DOMAIN: 1D Maze (same as MazeE2E)
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

all-states : List State
all-states = P0 ∷ P1 ∷ P2 ∷ []

------------------------------------------------------------------------
-- ═══════════════════════════════════════════════════════════════════
-- FEATURE DISCOVERY from dynamics
-- ═══════════════════════════════════════════════════════════════════
------------------------------------------------------------------------

_≟ₛ_ : State → State → Bool
P0 ≟ₛ P0 = true
P1 ≟ₛ P1 = true
P2 ≟ₛ P2 = true
_  ≟ₛ _  = false

pos-reward? : State → Action → Bool
pos-reward? s a = not (reward-fn (move s a) ≡ᵇ 0)

open import CSHRL.Synthesis.DynFeatureTemplate
open DynFTL move pos-reward? _≟ₛ_ all-actions all-states

-- 4 candidates: has-pos-reward Fwd/Bwd + is-self-loop Fwd/Bwd
test-candidates : length enumerate-dyn ≡ 4
test-candidates = refl

discovered : List DynFeature
discovered = filter-nontrivial enumerate-dyn

-- has-pos-reward Bwd is trivial (always false) → eliminated
-- 3 non-trivial features survive
test-discovered : length discovered ≡ 3
test-discovered = refl

-- is-self-loop Fwd evaluates IDENTICALLY to hand-crafted is-goal
test-loop-P0 : eval-dyn (is-self-loop Fwd) P0 ≡ false
test-loop-P0 = refl

test-loop-P1 : eval-dyn (is-self-loop Fwd) P1 ≡ false
test-loop-P1 = refl

test-loop-P2 : eval-dyn (is-self-loop Fwd) P2 ≡ true
test-loop-P2 = refl

-- Feature vectors distinguish all 3 states
test-fv-P0 : feature-vector discovered P0
  ≡ false ∷ false ∷ true ∷ []
test-fv-P0 = refl

test-fv-P1 : feature-vector discovered P1
  ≡ true ∷ false ∷ false ∷ []
test-fv-P1 = refl

test-fv-P2 : feature-vector discovered P2
  ≡ true ∷ true ∷ false ∷ []
test-fv-P2 = refl

------------------------------------------------------------------------
-- ═══════════════════════════════════════════════════════════════════
-- SYNTHESIS with discovered features
-- ═══════════════════════════════════════════════════════════════════
------------------------------------------------------------------------

open import CSHRL.Synthesis.FiniteDeterministicMDP
open FDMDPSynthesis State Action step all-actions

open WithStateFeatures DynFeature eval-dyn
open WithCEGIS discovered

-- Observations (same as MazeE2E)
obs-bwd≤fwd : List PredObs
obs-bwd≤fwd = (P0 , true) ∷ (P1 , true) ∷ (P2 , true) ∷ []

obs-fwd≤bwd : List PredObs
obs-fwd≤bwd = (P0 , false) ∷ (P1 , false) ∷ []

-- CEGIS synthesizes: same ranking as hand-crafted
synth-bwd≤fwd : synth-rank-pred 0 obs-bwd≤fwd ≡ just truep
synth-bwd≤fwd = refl

synth-fwd≤bwd : synth-rank-pred 0 obs-fwd≤bwd ≡ just falsep
synth-fwd≤bwd = refl

synth-prefer : Action → Action → PredProg
synth-prefer Fwd Fwd = truep
synth-prefer Fwd Bwd = falsep
synth-prefer Bwd Fwd = truep
synth-prefer Bwd Bwd = truep

synth-rank : RankModel
synth-rank = record { prefer = synth-prefer }

------------------------------------------------------------------------
-- ═══════════════════════════════════════════════════════════════════
-- VERIFY — Preservation proof (feature-independent)
-- ═══════════════════════════════════════════════════════════════════
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
-- CONSTRUCT + EXTRACT + EXECUTE
-- ═══════════════════════════════════════════════════════════════════
------------------------------------------------------------------------

open WithCorrectModel synth-rank synth-preserves

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

run-synth : State → ℕ → List (Action × State)
run-synth _ zero = []
run-synth s (suc n) =
  let a  = synth-policy s
      s' = proj₁ (step s a)
  in (a , s') ∷ run-synth s' n

test-trajectory : run-synth P0 3
  ≡ (Fwd , P1) ∷ (Fwd , P2) ∷ (Fwd , P2) ∷ []
test-trajectory = refl

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
-- CONFIRM — EC's Finder agrees
-- ═══════════════════════════════════════════════════════════════════
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

test-finder-P0 : Finder.find-policy P0 2 ≡ Fwd
test-finder-P0 = refl

test-finder-P1 : Finder.find-policy P1 2 ≡ Fwd
test-finder-P1 = refl

test-finder-P2 : Finder.find-policy P2 2 ≡ Fwd
test-finder-P2 = refl

finder-agrees : ∀ s → Finder.find-policy s 2 ≡ synth-policy s
finder-agrees P0 = refl
finder-agrees P1 = refl
finder-agrees P2 = refl

------------------------------------------------------------------------
-- SUMMARY
--
-- Feature discovery for FDMDP:
--
--   4 dynamics-derived features → 3 non-trivial after filtering
--
-- Key discovery: is-self-loop Fwd ≡ is-goal (at every state)
--
-- The concept of "goal state" emerges from dynamics: P2 is the only
-- state where Fwd is a self-loop.  No domain-specific MazeFeature
-- type was defined.
--
-- CEGIS produces the same ranking (truep/falsep) and the same
-- policy (Fwd everywhere) as the hand-crafted MazeE2E, confirmed
-- by the EC's Finder.
--
-- All --safe, no postulates.
------------------------------------------------------------------------
