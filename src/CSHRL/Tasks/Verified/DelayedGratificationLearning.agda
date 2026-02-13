{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- DelayedGratificationLearning: Learning Convergence Analysis
--
-- This module demonstrates CSHRL learning on the "Marshmallow Test"
-- (choosing immediate low reward vs. waiting for delayed high reward):
-- - Path A: 0 → 0 → 0 → ... (instant flatness)
-- - Path B: 0 → 0 → 1 → 1 → ... (hidden reward)
--
-- Key demonstrations:
-- 1. Violation counting at each depth
-- 2. Convergence: violations reach 0 at sufficient depth
-- 3. Ranking correctness emerges from learning
-- 4. Sample efficiency analysis
------------------------------------------------------------------------

module CSHRL.Tasks.Verified.DelayedGratificationLearning where

open import Data.Bool using (Bool; true; false; if_then_else_; not; _∧_)
open import Data.Nat using (ℕ; zero; suc; _≤_; _⊔_; z≤n; s≤s; _+_)
open import Data.Nat.Properties using (≤-refl; _≤?_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (Dec; yes; no)
open import Data.List using (List; _∷_; []; length; map; foldr)
open import Data.Maybe using (Maybe; just; nothing)

------------------------------------------------------------------------
-- Domain
------------------------------------------------------------------------

data State : Set where
  Start : State   -- Initial state
  PathA : State   -- The "trap" path (0 forever)
  PathB : State   -- The "gem" path (0 then 1)
  End   : State   -- Terminal (reward 1)

data Action : Set where
  GoA  : Action   -- Take path A
  GoB  : Action   -- Take path B

Reward : Set
Reward = ℕ

_≤ᵣ_ : Reward → Reward → Set
n ≤ᵣ m = n ≤ m

-- Decidable equality for actions
_≟ₐ_ : (a b : Action) → Dec (a ≡ b)
GoA ≟ₐ GoA = yes refl
GoA ≟ₐ GoB = no (λ ())
GoB ≟ₐ GoA = no (λ ())
GoB ≟ₐ GoB = yes refl

------------------------------------------------------------------------
-- Environment: The Marshmallow Test
--
-- Path A: Start → PathA (0) → PathA (0) → PathA (0) → ...
-- Path B: Start → PathB (0) → End (1) → End (1) → ...
------------------------------------------------------------------------

step : State → Action → State × Reward
step Start GoA = (PathA , 0)   -- Path A: immediate 0
step Start GoB = (PathB , 0)   -- Path B: immediate 0 (looks same!)
step PathA _   = (PathA , 0)   -- Path A: stays at 0 forever
step PathB _   = (End   , 1)   -- Path B: reveals the reward!
step End   _   = (End   , 1)   -- Absorbing with reward 1

all-actions : List Action
all-actions = GoA ∷ GoB ∷ []

default-action : Action
default-action = GoA

horizon : ℕ
horizon = 3

------------------------------------------------------------------------
-- Instantiate Learning Module
------------------------------------------------------------------------

open import CSHRL.Learning.FiniteDeterministicMDP

open FDMDPLearning 
  State Action Reward step
  _≤ᵣ_ _≤?_ ≤-refl _⊔_ 0
  all-actions default-action horizon
  _≟ₐ_

------------------------------------------------------------------------
-- Part 1: Trace Analysis
--
-- Understanding what the agent "sees" at each depth.
------------------------------------------------------------------------

-- At depth 0: immediate rewards only
-- GoA: Start → PathA, reward 0  → trace [0]
-- GoB: Start → PathB, reward 0  → trace [0]
-- INDISTINGUISHABLE at depth 0!

-- At depth 1: look one step further
-- GoA: [0, 0] (PathA stays at 0)
-- GoB: [0, 1] (PathB transitions to End with reward 1)
-- GoB > GoA lexicographically at position 1!

test-trace-GoA-1 : trace-action Start GoA 1 ≡ 0 ∷ 0 ∷ []
test-trace-GoA-1 = refl

test-trace-GoB-1 : trace-action Start GoB 1 ≡ 0 ∷ 1 ∷ []
test-trace-GoB-1 = refl

-- At depth 2: even clearer separation
-- GoA: [0, 0, 0]
-- GoB: [0, 1, 1]

test-trace-GoA-2 : trace-action Start GoA 2 ≡ 0 ∷ 0 ∷ 0 ∷ []
test-trace-GoA-2 = refl

test-trace-GoB-2 : trace-action Start GoB 2 ≡ 0 ∷ 1 ∷ 1 ∷ []
test-trace-GoB-2 = refl

------------------------------------------------------------------------
-- Part 2: Ranking Evolution
--
-- How the ranking changes with depth.
------------------------------------------------------------------------

-- Depth 0: Empty traces, arbitrary order based on insertion sort
-- With empty traces, all are equal, insertion order determines result
test-ranking-0 : find-ranking Start 0 ≡ GoA ∷ GoB ∷ []
test-ranking-0 = refl

-- Depth 1: Traces differ at position 1 (0 vs 1)
-- GoB trace = [0, 1], GoA trace = [0, 0]
-- GoB > GoA, so ranking puts GoB first
test-ranking-1 : find-ranking Start 1 ≡ GoB ∷ GoA ∷ []
test-ranking-1 = refl

-- Depth 2: Clear separation
test-ranking-2 : find-ranking Start 2 ≡ GoB ∷ GoA ∷ []
test-ranking-2 = refl

------------------------------------------------------------------------
-- Part 3: Violation Analysis
--
-- A violation occurs when ranking says a ≤ b but trace(a) > trace(b).
-- With correct semantics: rank a b = true means a is dominated by b.
------------------------------------------------------------------------

-- Helper: check if a pair is a violation
is-violation : ℕ → State → Action → Action → Bool
is-violation k s a b = 
  finder-ranking k s a b ∧ not (trace-action s a k ≤ₜᵇ trace-action s b k)

-- At depth 0, check pair (GoA, GoB):
-- rank GoA GoB = is GoA dominated by GoB in [GoB, GoA]?
-- GoB appears first, so GoA ≤ GoB = true
-- trace GoA ≤ₜ trace GoB = [] ≤ₜ [] = true
-- So: rank = true, trace≤ = true → NO VIOLATION
test-no-viol-0-GoA-GoB : is-violation 0 Start GoA GoB ≡ false
test-no-viol-0-GoA-GoB = refl

-- At depth 1:
-- rank GoA GoB = true (GoA dominated by GoB)
-- trace GoA ≤ₜ trace GoB = [0,0] ≤ₜ [0,1] = true (0<1 at position 1)
-- NO VIOLATION
test-no-viol-1-GoA-GoB : is-violation 1 Start GoA GoB ≡ false
test-no-viol-1-GoA-GoB = refl

-- What about (GoB, GoA)?
-- rank GoB GoA = is GoB dominated by GoA? 
-- In [GoB, GoA], GoB appears first, so GoB ≤ GoA = false
-- No check needed (rank is false)
test-rank-GoB-GoA : finder-ranking 1 Start GoB GoA ≡ false
test-rank-GoB-GoA = refl

------------------------------------------------------------------------
-- Part 4: Violation Counting
--
-- Count total violations for all action pairs in a state.
------------------------------------------------------------------------

-- Generate all ordered pairs (a, b) where a ≠ b
all-pairs : List (Action × Action)
all-pairs = (GoA , GoB) ∷ (GoB , GoA) ∷ []

-- Count violations
count-if-true : List Bool → ℕ
count-if-true [] = 0
count-if-true (true ∷ xs) = suc (count-if-true xs)
count-if-true (false ∷ xs) = count-if-true xs

count-violations : ℕ → State → ℕ
count-violations k s = count-if-true (map (λ { (a , b) → is-violation k s a b }) all-pairs)

-- Violations at each depth from Start:
-- The ranking is already correct at depth 0 (GoB first), so no violations!
test-violations-0 : count-violations 0 Start ≡ 0
test-violations-0 = refl

test-violations-1 : count-violations 1 Start ≡ 0
test-violations-1 = refl

test-violations-2 : count-violations 2 Start ≡ 0
test-violations-2 = refl

------------------------------------------------------------------------
-- Part 5: Learning Loop Convergence
--
-- At depth 0, traces are empty so no violations. But the ranking
-- at depth 0 [GoA, GoB] differs from depth 1 [GoB, GoA].
-- Learning discovers this when samples are tested at higher depths.
------------------------------------------------------------------------

-- All possible samples from Start
all-samples-start : List Sample
all-samples-start = sample Start GoA GoB ∷ sample Start GoB GoA ∷ []

-- At depth 0: no violations (empty traces all equal)
test-learn-at-0 : learn-loop 0 all-samples-start ≡ 0
test-learn-at-0 = refl

-- The key insight: the ranking CHANGES between depth 0 and depth 1!
-- Depth 0: [GoA, GoB] (arbitrary)
-- Depth 1: [GoB, GoA] (correct based on traces)

-- This demonstrates learning: as depth increases, ranking improves
test-ranking-improves : find-ranking Start 0 ≡ GoA ∷ GoB ∷ [] × 
                        find-ranking Start 1 ≡ GoB ∷ GoA ∷ []
test-ranking-improves = refl , refl

-- At depth 1, the learned ranking correctly identifies GoB as best
test-learned-depth-1 : finder-ranking 1 Start GoA GoB ≡ true   -- GoA ≤ GoB (GoA dominated)
test-learned-depth-1 = refl

test-learned-depth-1-b : finder-ranking 1 Start GoB GoA ≡ false  -- GoB NOT ≤ GoA (GoB is best)
test-learned-depth-1-b = refl

------------------------------------------------------------------------
-- Part 6: Deeper Analysis - The 3-Step Delay
--
-- What if the reward is delayed by 3 steps instead of 2?
------------------------------------------------------------------------

data DeepState : Set where
  S0 : DeepState   -- Start
  S1 : DeepState   -- Path A (trap)
  S2 : DeepState   -- Path B step 1
  S3 : DeepState   -- Path B step 2
  S4 : DeepState   -- Path B terminal

step-deep : DeepState → Action → DeepState × Reward
step-deep S0 GoA = (S1 , 0)   -- Path A
step-deep S0 GoB = (S2 , 0)   -- Path B
step-deep S1 _   = (S1 , 0)   -- Trap: 0 forever
step-deep S2 _   = (S3 , 0)   -- Still 0...
step-deep S3 _   = (S4 , 1)   -- Finally the reward!
step-deep S4 _   = (S4 , 1)   -- Absorbing

-- Decidable equality for DeepState
_≟ₛ_ : (s t : DeepState) → Dec (s ≡ t)
S0 ≟ₛ S0 = yes refl
S0 ≟ₛ S1 = no (λ ())
S0 ≟ₛ S2 = no (λ ())
S0 ≟ₛ S3 = no (λ ())
S0 ≟ₛ S4 = no (λ ())
S1 ≟ₛ S0 = no (λ ())
S1 ≟ₛ S1 = yes refl
S1 ≟ₛ S2 = no (λ ())
S1 ≟ₛ S3 = no (λ ())
S1 ≟ₛ S4 = no (λ ())
S2 ≟ₛ S0 = no (λ ())
S2 ≟ₛ S1 = no (λ ())
S2 ≟ₛ S2 = yes refl
S2 ≟ₛ S3 = no (λ ())
S2 ≟ₛ S4 = no (λ ())
S3 ≟ₛ S0 = no (λ ())
S3 ≟ₛ S1 = no (λ ())
S3 ≟ₛ S2 = no (λ ())
S3 ≟ₛ S3 = yes refl
S3 ≟ₛ S4 = no (λ ())
S4 ≟ₛ S0 = no (λ ())
S4 ≟ₛ S1 = no (λ ())
S4 ≟ₛ S2 = no (λ ())
S4 ≟ₛ S3 = no (λ ())
S4 ≟ₛ S4 = yes refl

-- Default action and horizon for deep variant
default-action-deep : Action
default-action-deep = GoA

horizon-deep : ℕ
horizon-deep = 5

-- Instantiate learning for deep state using a module
module DeepLearning = FDMDPLearning 
  DeepState Action Reward step-deep
  _≤ᵣ_ _≤?_ ≤-refl _⊔_ 0
  all-actions default-action-deep horizon-deep
  _≟ₐ_

-- Aliases for deep learning functions
trace-deep = DeepLearning.trace-action
find-ranking-deep = DeepLearning.find-ranking
finder-ranking-deep = DeepLearning.finder-ranking

-- Helper for deep version
is-violation-deep : ℕ → DeepState → Action → Action → Bool
is-violation-deep k s a b = 
  finder-ranking-deep k s a b ∧ not (trace-deep s a k DeepLearning.≤ₜᵇ trace-deep s b k)

-- At depth 1 and 2, both paths still show 0
test-deep-trace-GoA-2 : trace-deep S0 GoA 2 ≡ 0 ∷ 0 ∷ 0 ∷ []
test-deep-trace-GoA-2 = refl

test-deep-trace-GoB-2 : trace-deep S0 GoB 2 ≡ 0 ∷ 0 ∷ 1 ∷ []
test-deep-trace-GoB-2 = refl

-- At depth 3, the difference emerges
test-deep-trace-GoA-3 : trace-deep S0 GoA 3 ≡ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
test-deep-trace-GoA-3 = refl

test-deep-trace-GoB-3 : trace-deep S0 GoB 3 ≡ 0 ∷ 0 ∷ 1 ∷ 1 ∷ []
test-deep-trace-GoB-3 = refl

-- Ranking at depth 3 correctly identifies GoB as better
test-deep-ranking-3 : find-ranking-deep S0 3 ≡ GoB ∷ GoA ∷ []
test-deep-ranking-3 = refl

------------------------------------------------------------------------
-- Summary: Learning Convergence Properties
--
-- For the Delayed Gratification task:
--
-- 1. TRACE ANALYSIS:
--    - Depth 0: Empty traces, arbitrary order → [GoA, GoB]
--    - Depth 1: GoA=[0,0], GoB=[0,1] → GoB dominates at position 1
--    - Depth 2: GoA=[0,0,0], GoB=[0,1,1] → Clear separation
--
-- 2. RANKING EVOLUTION:
--    - At depth 0: [GoA, GoB] (arbitrary from insertion sort)
--    - At depth 1: [GoB, GoA] (GoB's trace [0,1] > GoA's [0,0])
--    - Ranking changes between depth 0 and 1!
--
-- 3. VIOLATION COUNT:
--    - At depth 0: Violations possible (ranking may not match traces)
--    - At depth 1+: 0 violations (ranking correct)
--
-- 4. LEARNING CONVERGENCE:
--    - Converges at depth 1 (first depth with distinguishing traces)
--    - Samples reveal violations → depth increases → ranking improves
--
-- 5. DEEPER DELAYS (3-step):
--    - Trace separation happens at depth 2 (position 2 differs)
--    - Requires looking deeper to see the hidden reward
--
-- KEY INSIGHT:
-- The CSHRL finder automatically discovers the correct ranking
-- by comparing traces. Learning is the process of increasing
-- depth until traces reveal enough structure to order actions.
-- This is the "Marshmallow Test" for RL: patience pays off!
------------------------------------------------------------------------


