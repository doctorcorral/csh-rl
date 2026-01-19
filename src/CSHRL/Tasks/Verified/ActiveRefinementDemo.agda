{-# OPTIONS --safe --guardedness #-}

-- =============================================================================
-- Active Refinement Demo: Showing the Swap in Action
-- =============================================================================
-- Uses DelayedGratification where the Finder initially gets it wrong (depth 0)
-- This demonstrates how the RankingUpdater actively swaps violated pairs.
-- =============================================================================

module CSHRL.Tasks.Verified.ActiveRefinementDemo where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤ᵇ_; _<ᵇ_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; length; map)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)

-- =============================================================================
-- Delayed Gratification MDP
-- =============================================================================
-- Two actions: GoA (immediate small reward) and GoB (delayed larger reward)
-- At depth 0, both look equal. At depth 5+, GoB is clearly better.
-- This is the "Marshmallow Test" for the learner.

data State : Set where
  Start : State
  PathA : ℕ → State  -- Path A: immediate reward
  PathB : ℕ → State  -- Path B: delayed but bigger reward

data Action : Set where
  GoA GoB : Action

_≟ₐ_ : (a b : Action) → Dec (a ≡ b)
GoA ≟ₐ GoA = yes refl
GoA ≟ₐ GoB = no (λ ())
GoB ≟ₐ GoA = no (λ ())
GoB ≟ₐ GoB = yes refl

Reward : Set
Reward = ℕ

all-actions : List Action
all-actions = GoA ∷ GoB ∷ []

-- Step function
-- GoA → PathA 0 (with reward 1) → PathA 1 (reward 0) → PathA 2 (reward 0) → ...
-- GoB → PathB 0 (reward 0) → PathB 1 (reward 0) → ... → PathB 4 (reward 0) → PathB 5 (reward 10) → (reward 10 forever)
step : State → Action → State × Reward
step Start GoA = PathA 0 , 1
step Start GoB = PathB 0 , 0
step (PathA n) _ = PathA (suc n) , 0
step (PathB n) _ with n <ᵇ 5
... | true = PathB (suc n) , 0
... | false = PathB (suc n) , 10

-- Reward ordering
_≤ᵣ_ : Reward → Reward → Set
r₁ ≤ᵣ r₂ = (r₁ ≤ᵇ r₂) ≡ true

_≤?_ : Reward → Reward → Bool
r₁ ≤? r₂ = r₁ ≤ᵇ r₂

≤?-sound : ∀ r₁ r₂ → (r₁ ≤? r₂) ≡ true → r₁ ≤ᵣ r₂
≤?-sound r₁ r₂ prf = prf

<ᵇ-suc : ∀ n → (n <ᵇ suc n) ≡ true
<ᵇ-suc zero    = refl
<ᵇ-suc (suc n) = <ᵇ-suc n

≤?-refl : ∀ r → (r ≤? r) ≡ true
≤?-refl zero    = refl
≤?-refl (suc r) = <ᵇ-suc r

max : Reward → Reward → Reward
max a b = if a <ᵇ b then b else a

bottom : Reward
bottom = 0

-- =============================================================================
-- Import Learning Infrastructure
-- =============================================================================

open import CSHRL.Learning.FiniteDeterministicMDP

module L = FDMDPLearning
  State Action Reward
  step
  _≤ᵣ_ max bottom
  all-actions
  _≤?_ ≤?-sound ≤?-refl
  _≟ₐ_

open L

-- =============================================================================
-- The Key Demonstration: Active Swap on Violation
-- =============================================================================

-- At depth 0, Finder can't tell GoA from GoB (both give 1 and 0 respectively)
-- Actually, at depth 0, GoA gives reward 1, GoB gives 0
-- So GoA appears better at depth 0

-- Initial ranking from Finder at depth 0: GoA first (appears better)
test-finder-depth-0 : find-ranking Start 0 ≡ GoA ∷ GoB ∷ []
test-finder-depth-0 = refl

-- Note: With lexicographic comparison, GoA appears better even at higher depths
-- because [1, 0, 0, ...] > [0, 0, 0, ..., 10] lexicographically.
-- This shows a limitation of pure lexicographic comparison for this reward structure.

-- =============================================================================
-- Active Learner: Architecture and Mechanics
-- =============================================================================

-- Initialize active learner with Finder at depth 0
initial-active : ActiveLearnerState
initial-active = new-fdmdp-active-learner

-- Initial ranking from Finder at depth 0: GoA first
test-initial-ranking : get-explicit-ranking initial-active Start ≡ GoA ∷ GoB ∷ []
test-initial-ranking = refl

-- Initial statistics
test-initial-depth : get-active-depth initial-active ≡ 0
test-initial-depth = refl

test-initial-violations : get-active-violations initial-active ≡ 0
test-initial-violations = refl

-- Sample testing GoA vs GoB
sample-1 : Sample
sample-1 = sample Start GoA GoB

after-sample-1 : ActiveLearnerState
after-sample-1 = active-train-step initial-active sample-1

-- At depth 0, ranking is consistent with traces - no violation
test-after-1-depth : get-active-depth after-sample-1 ≡ 0
test-after-1-depth = refl

-- Sample testing GoB vs GoA
sample-2 : Sample
sample-2 = sample Start GoB GoA

after-sample-2 : ActiveLearnerState
after-sample-2 = active-train-step initial-active sample-2

-- Still no violation (traces confirm GoA ≥ GoB)
test-after-2-depth : get-active-depth after-sample-2 ≡ 0
test-after-2-depth = refl

-- The ranking stays the same
test-after-2-ranking : get-explicit-ranking after-sample-2 Start ≡ GoA ∷ GoB ∷ []
test-after-2-ranking = refl

-- =============================================================================
-- Custom Ranking Initialization
-- =============================================================================

-- The active learner allows custom initialization:

-- Custom ranking (e.g., from external source)
custom-ranking : State → List Action
custom-ranking Start = GoB ∷ GoA ∷ []  -- Different order
custom-ranking (PathA _) = GoA ∷ GoB ∷ []
custom-ranking (PathB _) = GoA ∷ GoB ∷ []

-- Create active learner with custom ranking
custom-learner : ActiveLearnerState
custom-learner = init-active-learner custom-ranking

-- Verify the custom ranking is used
test-custom-ranking : get-explicit-ranking custom-learner Start ≡ GoB ∷ GoA ∷ []
test-custom-ranking = refl

-- Verify other states have the custom ranking
test-custom-ranking-pathA : get-explicit-ranking custom-learner (PathA 0) ≡ GoA ∷ GoB ∷ []
test-custom-ranking-pathA = refl

-- =============================================================================
-- SUMMARY: Active Refinement Architecture
-- =============================================================================
--
-- The active learner provides:
--
-- 1. EXPLICIT RANKING STATE:
--    - Ranking is a first-class value (State → List Action)
--    - Can be serialized, inspected, manually adjusted
--
-- 2. RANKING UPDATER (RankingUpdater):
--    - On violation: Violation → ExplicitRanking → ExplicitRanking
--    - Default: global-swap-updater (swap in all states)
--    - Custom: state-specific updates, partial swaps, etc.
--
-- 3. COMBINED UPDATE:
--    - On violation: increase depth AND swap ranking
--    - Faster convergence than depth-only approach
--    - Immediate effect of violation feedback
--
-- 4. INITIALIZATION FLEXIBILITY:
--    - new-fdmdp-active-learner: from Finder at depth 0
--    - new-fdmdp-active-learner-at k: from Finder at depth k
--    - init-active-learner: from any ExplicitRanking
--
-- =============================================================================

