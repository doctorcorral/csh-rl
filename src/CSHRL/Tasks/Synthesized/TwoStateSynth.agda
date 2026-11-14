{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- TwoState via Synthesis: Parametrized Policy Demo
--
-- Demonstrates the synthesis pipeline on TwoState:
--   1. Define observations from the true environment
--   2. Build a decision tree ranking over state features
--   3. Prove feature coherence (identity features → trivial)
--   4. Prove preservation at representative states
--   5. Get verified CoindHomo via preservation transfer
--
-- The tree ranking generalizes: verifying at Start and Goal
-- gives correctness at ANY state with the same features.
-- For identity features this is just the two states, but the
-- infrastructure scales to richer feature abstractions.
------------------------------------------------------------------------

module CSHRL.Tasks.Synthesized.TwoStateSynth where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _≤_; _⊔_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; subst; cong; sym; trans)
open import Codata.Guarded.Stream using (Stream; head; tail; tabulate)
open import Function using (_∘_)
open import Data.List using (List; _∷_; [])
open import Data.Unit using (⊤; tt)

------------------------------------------------------------------------
-- Domain (reused from TwoState)
------------------------------------------------------------------------

data State : Set where
  Start : State
  Goal  : State

data Action : Set where
  Go   : Action
  Stay : Action

step : State → Action → State × ℕ
step Start Go   = (Goal  , 1)
step Start Stay = (Start , 0)
step Goal  Go   = (Goal  , 1)
step Goal  Stay = (Goal  , 1)

all-actions : List Action
all-actions = Go ∷ Stay ∷ []

------------------------------------------------------------------------
-- Open Synthesis Infrastructure
------------------------------------------------------------------------

open import CSHRL.Synthesis.Core
open SynthesisCore State Action step all-actions

------------------------------------------------------------------------
-- Step 1: OBSERVATIONS
--
-- Record transitions from the true environment.
-- In a real synthesis scenario, these come from exploration.
------------------------------------------------------------------------

observations : List Observation
observations =
  obs Start Go   Goal  1 ∷
  obs Start Stay Start 0 ∷
  obs Goal  Go   Goal  1 ∷
  obs Goal  Stay Goal  1 ∷ []

-- All observations are valid (they match the true step function)
observations-valid : AllValid observations
observations-valid = refl , refl , refl , refl , tt

-- The true model is consistent with these observations
observations-consistent : step ⊨all observations
observations-consistent = true-model-all-consistent observations observations-valid

------------------------------------------------------------------------
-- Step 2: FEATURE ABSTRACTION
--
-- Feature = State (identity abstraction).
-- Every state is its own feature class.
-- This is the simplest case; richer abstractions reduce the
-- number of representatives needed.
------------------------------------------------------------------------

Feature : Set
Feature = State

extract : State → Feature
extract s = s

open WithFeatures Feature extract

------------------------------------------------------------------------
-- Step 3: DECISION TREE RANKING
--
-- A constant tree: Go ≥ Stay at all states.
-- Convention: rank a b = true means "a ≤ b" (b dominates a).
------------------------------------------------------------------------

rank-cmp : Action → Action → Bool
rank-cmp Go   Go   = true   -- Go ≤ Go (reflexive)
rank-cmp Go   Stay = false  -- Go is NOT dominated by Stay
rank-cmp Stay Go   = true   -- Stay IS dominated by Go
rank-cmp Stay Stay = true   -- Stay ≤ Stay (reflexive)

ranking-tree : RankTree
ranking-tree = rleaf rank-cmp

-- Test: the tree assigns correct rankings
test-tree-start : tree-rank ranking-tree Start Stay Go ≡ true
test-tree-start = refl

test-tree-goal : tree-rank ranking-tree Goal Stay Go ≡ true
test-tree-goal = refl

------------------------------------------------------------------------
-- Step 4: FEATURE COHERENCE
--
-- For identity features: extract s₁ ≡ extract s₂ implies s₁ ≡ s₂.
-- So coherence is trivial: same state → same action-values.
------------------------------------------------------------------------

coherent : FeatureCoherent
coherent s₁ .s₁ a b refl av-ord = av-ord

------------------------------------------------------------------------
-- Step 5: PRESERVATION AT REPRESENTATIVES
--
-- Prove that the tree ranking preserves action-value ordering
-- at each representative state (here: Start and Goal).
------------------------------------------------------------------------

-- Helper: stream reflexivity
≤ₛ-refl : ∀ (s : Stream ℕ) → s ≤ₛ s
head≤ (≤ₛ-refl s) = ≤-refl
tail≤ (≤ₛ-refl s) = ≤ₛ-refl (tail s)

-- solve is always 1 for this MDP
solve-Goal-is-1 : ∀ n → solve Goal n ≡ 1
solve-Goal-is-1 zero    = refl
solve-Goal-is-1 (suc n) = cong (λ x → x ⊔ (x ⊔ 0)) (solve-Goal-is-1 n)

solve-Start-is-1 : ∀ n → solve Start n ≡ 1
solve-Start-is-1 zero    = refl
solve-Start-is-1 (suc n) =
  subst (λ x → x ⊔ (solve Start n ⊔ 0) ≡ 1)
        (sym (solve-Goal-is-1 n))
        (subst (λ x → 1 ⊔ (x ⊔ 0) ≡ 1)
               (sym (solve-Start-is-1 n))
               refl)

solve-is-1 : ∀ s n → solve s n ≡ 1
solve-is-1 Start = solve-Start-is-1
solve-is-1 Goal  = solve-Goal-is-1

-- iter-head for accessing stream elements
iter-head : ℕ → Stream ℕ → ℕ
iter-head zero    s = head s
iter-head (suc n) s = iter-head n (tail s)

iter-head-tabulate : ∀ (f : ℕ → ℕ) n → iter-head n (tabulate f) ≡ f n
iter-head-tabulate f zero    = refl
iter-head-tabulate f (suc n) = iter-head-tabulate (f ∘ suc) n

iter-head-value : ∀ s n → iter-head n (value s) ≡ solve s n
iter-head-value s n = iter-head-tabulate (solve s) n

iter-head-is-1 : ∀ s n → iter-head n (value s) ≡ 1
iter-head-is-1 s n =
  subst (λ x → x ≡ 1) (sym (iter-head-value s n)) (solve-is-1 s n)

-- HeadGen pattern for building stream orderings
HeadGen : Stream ℕ → Stream ℕ → Set
HeadGen s₁ s₂ = ∀ n → iter-head n s₁ ≤ iter-head n s₂

shift-gen : ∀ {s₁ s₂} → HeadGen s₁ s₂ → HeadGen (tail s₁) (tail s₂)
shift-gen gen n = gen (suc n)

build-≤ₛ : ∀ (s₁ s₂ : Stream ℕ) → HeadGen s₁ s₂ → s₁ ≤ₛ s₂
head≤ (build-≤ₛ s₁ s₂ gen) = gen 0
tail≤ (build-≤ₛ s₁ s₂ gen) = build-≤ₛ (tail s₁) (tail s₂) (shift-gen gen)

-- value Start ≤ₛ value Goal
Start-≤-Goal : value Start ≤ₛ value Goal
Start-≤-Goal = build-≤ₛ (value Start) (value Goal) gen
  where
    gen : HeadGen (value Start) (value Goal)
    gen n = subst (λ x → x ≤ iter-head n (value Goal))
                  (sym (iter-head-is-1 Start n))
                  (subst (λ x → 1 ≤ x)
                         (sym (iter-head-is-1 Goal n))
                         ≤-refl)

-- PRESERVATION AT GOAL
-- All action-values from Goal have head=1, tail=value Goal
-- so everything is ≤ₛ-refl
preserves-at-Goal : PreservesAt ranking-tree Goal
preserves-at-Goal Go   Go   _ = ≤ₛ-refl (action-value Goal Go)
head≤ (preserves-at-Goal Stay Go _) = ≤-refl
tail≤ (preserves-at-Goal Stay Go _) = ≤ₛ-refl (value Goal)
preserves-at-Goal Stay Stay _ = ≤ₛ-refl (action-value Goal Stay)

-- PRESERVATION AT START
-- Three ranked pairs: Go≤Go (refl), Stay≤Go (the interesting case), Stay≤Stay (refl)
preserves-at-Start : PreservesAt ranking-tree Start
preserves-at-Start Go   Go   _ = ≤ₛ-refl (action-value Start Go)
preserves-at-Start Stay Go   _ = stay-go-proof
  where
    stay-go-proof : action-value Start Stay ≤ₛ action-value Start Go
    head≤ stay-go-proof = z≤n
    tail≤ stay-go-proof = Start-≤-Goal
preserves-at-Start Stay Stay _ = ≤ₛ-refl (action-value Start Stay)

------------------------------------------------------------------------
-- Step 6: ASSEMBLE THE CoindHomo VIA PRESERVATION TRANSFER
--
-- The WithRepresentatives module takes:
--   - the tree
--   - feature coherence
--   - a representative function
--   - preservation at representatives
-- and produces a verified CoindHomo.
------------------------------------------------------------------------

representative : State → State
representative s = s

rep-feat : ∀ s → extract (representative s) ≡ extract s
rep-feat _ = refl

rep-preserves : ∀ s → PreservesAt ranking-tree (representative s)
rep-preserves Start = preserves-at-Start
rep-preserves Goal  = preserves-at-Goal

open WithRepresentatives ranking-tree coherent representative rep-feat rep-preserves

------------------------------------------------------------------------
-- RESULT: SynthesizedHomo is now in scope as an instance of CoindHomo.
--
-- This was built WITHOUT manually enumerating all (state, action, action)
-- triples. The decision tree + feature coherence + representative
-- preservation gave us a verified CoindHomo for ALL states.
--
-- For TwoState this is modest (2 states). For richer domains with
-- coarser features, this approach verifies at O(|Features|) states
-- instead of O(|States|) — exponential savings when |Features| ≪ |States|.
------------------------------------------------------------------------

-- Verify the instance is in scope
test-homo : CoindHomo
test-homo = SynthesizedHomo
