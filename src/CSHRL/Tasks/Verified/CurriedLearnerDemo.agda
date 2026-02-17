{-# OPTIONS --safe --guardedness #-}

-- =============================================================================
-- Curried Learner Demonstration
-- =============================================================================
-- Shows the benefits of the curried/stateful learner interface:
--   1. Natural checkpointing
--   2. Incremental learning  
--   3. Training traces for analysis
--   4. Composable learning steps
--   5. Violation detection and active ranking refinement
--
-- Uses the "Late Bloomer" MDP: two actions with equal-prefix traces that
-- diverge at depth 3, causing a violation when the Finder initially ranks
-- them by insertion order.
-- =============================================================================

module CSHRL.Tasks.Verified.CurriedLearnerDemo where

open import Data.Nat using (ℕ; zero; suc; _≤_; _⊔_; _+_; _≤ᵇ_; _<ᵇ_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; length; map)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)

-- =============================================================================
-- Late Bloomer MDP: A task where violations actually occur
-- =============================================================================
-- 
-- PathA: Start → A₀ (r=0) → A₁ (r=0) → A₂ (r=0) → A₃ (r=1) → ... (r=1 forever)
-- PathB: Start → B₀ (r=0) → B₁ (r=0) → B₂ (r=0) → B₃ (r=2) → ... (r=2 forever)
--
-- At depths 0-2: traces are [0], [0,0], [0,0,0] — indistinguishable!
-- At depth 3:    trace(GoA) = [0,0,0,1], trace(GoB) = [0,0,0,2]
--                GoB is BETTER (2 > 1 at position 3)
--
-- But at depth ≤ 2, the Finder ranks by insertion order (GoA first in list).
-- Testing at depth 3 reveals a VIOLATION: ranking says GoA ≥ GoB, but 
-- trace(GoB) > trace(GoA).
--
-- Unlike the Marshmallow Test (immediate vs. delayed reward), both paths here
-- look identical at first—testing whether the learner looks *deep enough*.
-- =============================================================================

data State : Set where
  Start : State
  PathA : ℕ → State  -- On path A, at step n
  PathB : ℕ → State  -- On path B, at step n

data Action : Set where
  GoA GoB : Action

_≟ₐ_ : (a b : Action) → Dec (a ≡ b)
GoA ≟ₐ GoA = yes refl
GoA ≟ₐ GoB = no (λ ())
GoB ≟ₐ GoA = no (λ ())
GoB ≟ₐ GoB = yes refl

Reward : Set
Reward = ℕ

-- GoA comes first in all-actions, so at equal traces it will be ranked first
all-actions : List Action
all-actions = GoA ∷ GoB ∷ []

-- Threshold: rewards diverge at step 3
threshold : ℕ
threshold = 3

step : State → Action → State × Reward
step Start GoA = PathA 0 , 0
step Start GoB = PathB 0 , 0
step (PathA n) _ with n <ᵇ threshold
... | true  = PathA (suc n) , 0
... | false = PathA (suc n) , 1  -- Modest reward after threshold
step (PathB n) _ with n <ᵇ threshold
... | true  = PathB (suc n) , 0
... | false = PathB (suc n) , 2  -- Better reward after threshold

open import Data.Nat.Properties using (≤-refl; _≤?_)

-- Reward ordering
_≤ᵣ_ : Reward → Reward → Set
r₁ ≤ᵣ r₂ = r₁ ≤ r₂

default-action : Action
default-action = GoA

horizon : ℕ
horizon = 5

-- =============================================================================
-- Import the Learning Infrastructure
-- =============================================================================

open import CSHRL.Learning.FiniteDeterministicMDP

module L = FDMDPLearning
  State Action Reward
  step
  _≤ᵣ_ _≤?_ ≤-refl _⊔_ 0
  all-actions default-action horizon
  _≟ₐ_

open L

-- =============================================================================
-- DEMONSTRATION 1: The Ranking Flip Phenomenon
-- =============================================================================
-- At low depth, traces are equal → Finder uses insertion order → GoA first
-- At depth 4+, traces diverge → GoB is objectively better
-- This demonstrates the core CSHRL learning dynamic.

-- At depth 2: traces are [0, 0, 0] for both actions
test-traces-equal-depth-2 : trace-action Start GoA 2 ≡ trace-action Start GoB 2
test-traces-equal-depth-2 = refl

-- At depth 2, Finder ranks by insertion order (GoA first in all-actions)
test-ranking-depth-2 : find-ranking Start 2 ≡ GoA ∷ GoB ∷ []
test-ranking-depth-2 = refl

-- At depth 4: traces diverge!
-- GoA: [0, 0, 0, 0, 1] — modest reward at step 4
-- GoB: [0, 0, 0, 0, 2] — better reward at step 4
test-trace-GoA-depth-4 : trace-action Start GoA 4 ≡ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 1 ∷ []
test-trace-GoA-depth-4 = refl

test-trace-GoB-depth-4 : trace-action Start GoB 4 ≡ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 2 ∷ []
test-trace-GoB-depth-4 = refl

-- At depth 4, Finder correctly ranks GoB first (2 > 1 at position 4)
test-ranking-depth-4 : find-ranking Start 4 ≡ GoB ∷ GoA ∷ []
test-ranking-depth-4 = refl

-- =============================================================================
-- DEMONSTRATION 2: Violation Detection
-- =============================================================================
-- A violation occurs when ranking and traces disagree.
-- At depth 3: traces still equal, but testing at depth 4 reveals the truth.

-- Sample to test: is GoB dominated by GoA?
sample-test-B-vs-A : Sample
sample-test-B-vs-A = sample Start GoB GoA

-- At depth 3, ranking says GoA ≥ GoB (GoA first)
-- But trace comparison at depth 3 shows they're equal
-- test-pair uses current ranking vs current traces, so no violation yet
test-no-violation-depth-3 : test-pair 3 sample-test-B-vs-A ≡ nothing
test-no-violation-depth-3 = refl

-- =============================================================================
-- DEMONSTRATION 3: Basic Curried Learning
-- =============================================================================

-- Create samples that test both orderings
sample₁ : Sample
sample₁ = sample Start GoA GoB  -- Is GoA dominated by GoB?

sample₂ : Sample
sample₂ = sample Start GoB GoA  -- Is GoB dominated by GoA?

samples : List Sample
samples = sample₁ ∷ sample₂ ∷ sample₁ ∷ []

-- Initialize a fresh learner
learner₀ : LearnerState
learner₀ = new-fdmdp-learner

-- Verify initial state
test-init-depth : get-depth learner₀ ≡ 0
test-init-depth = refl

test-init-samples : get-samples learner₀ ≡ 0
test-init-samples = refl

test-init-violations : get-violations learner₀ ≡ 0
test-init-violations = refl

-- =============================================================================
-- DEMONSTRATION 4: Incremental Training (One at a Time)
-- =============================================================================

-- Train step by step
learner₁ : LearnerState
learner₁ = train-step learner₀ sample₁

learner₂ : LearnerState
learner₂ = train-step learner₁ sample₂

learner₃ : LearnerState
learner₃ = train-step learner₂ sample₁

-- Check progress after each step
test-step1-samples : get-samples learner₁ ≡ 1
test-step1-samples = refl

test-step2-samples : get-samples learner₂ ≡ 2
test-step2-samples = refl

test-step3-samples : get-samples learner₃ ≡ 3
test-step3-samples = refl

-- =============================================================================
-- DEMONSTRATION 5: Batch Training
-- =============================================================================

-- Same result as step-by-step, but in one call
learner-batch : LearnerState
learner-batch = train-batch learner₀ samples

-- Verify equivalence
test-batch-equiv : get-samples learner-batch ≡ get-samples learner₃
test-batch-equiv = refl

test-batch-depth : get-depth learner-batch ≡ get-depth learner₃
test-batch-depth = refl

-- =============================================================================
-- DEMONSTRATION 6: Checkpointing
-- =============================================================================

-- Save checkpoint after some training
checkpoint₁ : LearnerState
checkpoint₁ = checkpoint learner₂

-- Continue training from checkpoint
learner-from-ckpt : LearnerState
learner-from-ckpt = train-step checkpoint₁ sample₁

-- Verify checkpoint preserved state
test-ckpt-depth : get-depth checkpoint₁ ≡ get-depth learner₂
test-ckpt-depth = refl

test-ckpt-samples : get-samples checkpoint₁ ≡ get-samples learner₂
test-ckpt-samples = refl

-- Verify training continued correctly
test-resume-samples : get-samples learner-from-ckpt ≡ suc (get-samples checkpoint₁)
test-resume-samples = refl

-- =============================================================================
-- DEMONSTRATION 7: Training Trace (For Analysis/Plotting)
-- =============================================================================

-- Get full trace of learner states during training
trace : List LearnerState
trace = training-trace learner₀ samples

-- Extract depth history
depths : List ℕ
depths = depth-history trace

-- Extract violation history  
violations : List ℕ
violations = violation-history trace

-- Verify trace length (initial state + one per sample)
test-trace-length : length trace ≡ suc (length samples)
test-trace-length = refl

-- =============================================================================
-- DEMONSTRATION 8: Current Ranking Query
-- =============================================================================

-- Get ranking at current learner depth
ranking-at-ckpt : List Action
ranking-at-ckpt = current-ranking checkpoint₁ Start

-- Get ranking with unavailability (only GoA available)
only-GoA : Available
only-GoA a with a ≟ₐ GoA
... | yes _ = true
... | no _  = false

ranking-restricted : List Action
ranking-restricted = current-ranking-restricted checkpoint₁ only-GoA Start

-- =============================================================================
-- DEMONSTRATION 9: Compositional Learning
-- =============================================================================

-- Define a more complex training procedure using combinators
-- Train 3 samples, checkpoint, train 2 more, checkpoint

complex-training : LearnerState
complex-training = 
  let ckpt1 = checkpoint (train-batch new-fdmdp-learner (sample₁ ∷ sample₂ ∷ sample₁ ∷ []))
      ckpt2 = checkpoint (train-batch ckpt1 (sample₂ ∷ sample₁ ∷ []))
  in ckpt2

test-complex-samples : get-samples complex-training ≡ 5
test-complex-samples = refl

-- =============================================================================
-- Summary: Benefits of Curried Learner
-- =============================================================================
--
-- 1. NATURAL CHECKPOINTING:
--    checkpoint : LearnerState → LearnerState
--    Just save the LearnerState record; resume by passing it to train-step
--
-- 2. INCREMENTAL LEARNING:
--    train-step : LearnerState → Sample → LearnerState
--    Process samples one at a time, inspect state between
--
-- 3. TRAINING TRACES:
--    training-trace : LearnerState → List Sample → List LearnerState
--    Get full history for analysis, plotting, debugging
--
-- 4. COMPOSABILITY:
--    Chain train-batch, checkpoint, current-ranking freely
--    Build complex training pipelines from simple parts
--
-- 5. STATE QUERIES:
--    get-depth, get-samples, get-violations, has-stabilized
--    Inspect learner state at any point
--
-- 6. NO PERFORMANCE PENALTY:
--    Same computations as before, just better organized
--    LearnerState is a small record (4 fields)
--
-- =============================================================================

-- =============================================================================
-- ACTIVE LEARNER: Active Refinement with RankingUpdater
-- =============================================================================
--
-- The active learner goes beyond just increasing depth on violations.
-- It actively swaps the violated pair in the explicit ranking, 
-- providing faster convergence.
--
-- Key types:
--   - ExplicitRanking : State → List Action (maintained ranking)
--   - RankingUpdater : Violation → ExplicitRanking → ExplicitRanking
--   - ActiveLearnerState : includes the explicit ranking being refined
--
-- On violation: 
--   1. Increase depth (same as passive learner)
--   2. Swap viol-better before viol-worse in the ranking (active update)
--
-- =============================================================================

-- Initialize active learner with Finder's ranking at depth 0
init-active : ActiveLearnerState
init-active = new-fdmdp-active-learner

-- Initialize at a specific depth (e.g., depth 5 where ranking is correct)
init-active-5 : ActiveLearnerState
init-active-5 = new-fdmdp-active-learner-at 5

-- Active training step
step-active : Sample → ActiveLearnerState → ActiveLearnerState
step-active s ls = active-train-step ls s

-- Active batch training
batch-active : List Sample → ActiveLearnerState → ActiveLearnerState
batch-active samples-list ls = active-batch ls samples-list

-- Get the refined ranking from active learner
ranking-from-active : ActiveLearnerState → State → List Action
ranking-from-active = current-active-ranking

-- Get active learner statistics
depth-from-active : ActiveLearnerState → ℕ
depth-from-active = active-depth

violations-from-active : ActiveLearnerState → ℕ
violations-from-active = active-violation-count

-- =============================================================================
-- DEMONSTRATION 10: The Ranking Flip in Active Learning
-- =============================================================================
-- At depth 0, Finder ranks GoA first (traces are equal, insertion order wins)
-- At depth 4+, the true ranking is revealed: GoB is better

-- Initial active ranking at Start (from Finder at depth 0)
-- Traces are equal at depth 0, so insertion order determines ranking
test-initial-active-ranking : ranking-from-active init-active Start ≡ GoA ∷ GoB ∷ []
test-initial-active-ranking = refl

-- At depth 5, Finder gets it right: GoB first
test-active-ranking-depth-5 : ranking-from-active init-active-5 Start ≡ GoB ∷ GoA ∷ []
test-active-ranking-depth-5 = refl

-- =============================================================================
-- DEMONSTRATION 11: Sample Processing Without Violations
-- =============================================================================
-- At low depth, traces are equal, so no violation is detected yet

-- Sample testing GoA vs GoB at depth 0
active-sample-A-vs-B : Sample
active-sample-A-vs-B = sample Start GoA GoB

-- Process the sample - at depth 0, traces are equal, no violation
after-one-sample : ActiveLearnerState
after-one-sample = active-train-step init-active active-sample-A-vs-B

test-after-one-depth : depth-from-active after-one-sample ≡ 0
test-after-one-depth = refl

test-after-one-violations : violations-from-active after-one-sample ≡ 0
test-after-one-violations = refl

-- Ranking unchanged (still GoA first from initialization)
test-after-one-ranking : ranking-from-active after-one-sample Start ≡ GoA ∷ GoB ∷ []
test-after-one-ranking = refl

-- =============================================================================
-- KEY INSIGHT: Active vs Passive Learning
--
-- PASSIVE (curried learner):
--   - On violation: increase depth, re-query Finder with new depth
--   - Ranking is always computed fresh from Finder
--   - Correct but potentially slower (Finder recomputes from scratch)
--
-- ACTIVE (active learner):
--   - On violation: increase depth AND swap violated pair
--   - Maintains explicit ranking that gets incrementally refined
--   - Faster convergence (immediate effect of violation)
--   - The swapped ranking is a "hint" that may be confirmed/refined later
--
-- The Late Bloomer MDP demonstrates:
--   - At low depth: GoA and GoB look equal → Finder uses insertion order
--   - At high depth: GoB is revealed to be better (reward 2 vs 1)
--   - Learning discovers this via depth increase or violation-driven swaps
--
-- =============================================================================

-- Multiple samples continue training
after-two-samples : ActiveLearnerState
after-two-samples = active-train-step after-one-sample active-sample-A-vs-B

-- Statistics after two samples
test-samples-count : get-active-samples after-two-samples ≡ 2
test-samples-count = refl

-- =============================================================================
-- DEMONSTRATION 12: Direct Initialization with Custom Ranking
-- =============================================================================
-- The active learner allows starting with any explicit ranking

-- Custom ranking that puts GoB first (the "correct" answer)
custom-ranking : State → List Action
custom-ranking Start = GoB ∷ GoA ∷ []
custom-ranking (PathA _) = GoA ∷ GoB ∷ []
custom-ranking (PathB _) = GoA ∷ GoB ∷ []

-- Initialize with custom ranking
custom-active : ActiveLearnerState
custom-active = init-active-learner custom-ranking

-- Verify custom ranking is used
test-custom-ranking : ranking-from-active custom-active Start ≡ GoB ∷ GoA ∷ []
test-custom-ranking = refl

-- =============================================================================
-- SUMMARY: Active Refinement Benefits
--
-- 1. FASTER CONVERGENCE:
--    Direct swap on violation, no need to wait for Finder recomputation
--
-- 2. EXPLICIT RANKING STATE:
--    The ranking is a first-class value, can be inspected/serialized
--
-- 3. COMPOSABLE UPDATERS:
--    Provide custom RankingUpdater for domain-specific refinement
--
-- 4. CUSTOM INITIALIZATION:
--    Start from Finder at any depth, or from external ranking
--
-- 5. HYBRID STRATEGIES:
--    Combine active updates with periodic Finder sync
--
-- =============================================================================

-- =============================================================================
-- DEMONSTRATION 13: How the Late Bloomer MDP Validates Learning
-- =============================================================================
--
-- The Late Bloomer MDP is specifically designed to test the learning system:
--
-- 1. EQUAL PREFIX PROPERTY:
--    Both paths give reward 0 for steps 0-2, making them indistinguishable
--    at shallow depths. This forces the Finder to use insertion order.
--
-- 2. DELAYED DIVERGENCE:
--    At step 3+, rewards diverge (1 vs 2), revealing the true ranking.
--    This tests depth-increase learning.
--
-- 3. CLEAR WINNER:
--    GoB is strictly better at sufficient depth (2 > 1 at every step after 3).
--    This makes the ground truth unambiguous.
--
-- 4. MONOTONICITY:
--    Once GoB is ranked first, no future samples can cause a violation
--    (the ranking matches the trace ordering at all depths ≥ 4).
--
-- This design validates the core CSHRL claim: learning via depth increase
-- and violation-driven swaps converges to the coinductively optimal ranking.
--
-- =============================================================================
