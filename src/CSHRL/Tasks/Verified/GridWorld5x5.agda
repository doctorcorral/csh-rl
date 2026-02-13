{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- GridWorld5x5: A Complex Navigation Task
--
-- A 5x5 grid world where the agent must navigate from Start (0,0)
-- to Goal (4,4). Tests CSHRL learning on a larger state space.
--
-- States: 25 (5×5 grid)
-- Actions: 4 (Up, Down, Left, Right)
-- Horizon: ~8 steps (Manhattan distance)
--
-- This demonstrates:
-- 1. Learning scales to larger state spaces
-- 2. Ranking evolves as depth captures longer paths
-- 3. Trace comparison efficiently prunes suboptimal actions
------------------------------------------------------------------------

module CSHRL.Tasks.Verified.GridWorld5x5 where

open import Data.Bool using (Bool; true; false; if_then_else_; not; _∧_; _∨_)
open import Data.Nat using (ℕ; zero; suc; _≤_; _⊔_; _<_; z≤n; s≤s; _+_; _∸_; _≤ᵇ_; _<ᵇ_)
open import Data.Nat.Properties using (≤-refl; _≤?_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (Dec; yes; no)
open import Data.List using (List; _∷_; []; length; map)
open import Data.Maybe using (Maybe; just; nothing)

------------------------------------------------------------------------
-- Grid Configuration
------------------------------------------------------------------------

Size : ℕ
Size = 5

GoalX : ℕ
GoalX = 4

GoalY : ℕ
GoalY = 4

------------------------------------------------------------------------
-- State: Position on the grid
------------------------------------------------------------------------

record Position : Set where
  constructor pos
  field
    x : ℕ
    y : ℕ

open Position

-- State is just a position (could extend with obstacles, keys, etc.)
State : Set
State = Position

-- Start and Goal positions
start : State
start = pos 0 0

goal : State
goal = pos GoalX GoalY

-- Check if at goal
at-goal : State → Bool
at-goal (pos px py) = (px ≡ᵇ GoalX) ∧ (py ≡ᵇ GoalY)
  where
    _≡ᵇ_ : ℕ → ℕ → Bool
    zero  ≡ᵇ zero  = true
    zero  ≡ᵇ suc _ = false
    suc _ ≡ᵇ zero  = false
    suc m ≡ᵇ suc n = m ≡ᵇ n

------------------------------------------------------------------------
-- Actions
------------------------------------------------------------------------

data Action : Set where
  Up    : Action
  Down  : Action
  Left  : Action
  Right : Action

all-actions : List Action
all-actions = Up ∷ Down ∷ Left ∷ Right ∷ []

-- Decidable equality for actions
_≟ₐ_ : (a b : Action) → Dec (a ≡ b)
Up    ≟ₐ Up    = yes refl
Up    ≟ₐ Down  = no (λ ())
Up    ≟ₐ Left  = no (λ ())
Up    ≟ₐ Right = no (λ ())
Down  ≟ₐ Up    = no (λ ())
Down  ≟ₐ Down  = yes refl
Down  ≟ₐ Left  = no (λ ())
Down  ≟ₐ Right = no (λ ())
Left  ≟ₐ Up    = no (λ ())
Left  ≟ₐ Down  = no (λ ())
Left  ≟ₐ Left  = yes refl
Left  ≟ₐ Right = no (λ ())
Right ≟ₐ Up    = no (λ ())
Right ≟ₐ Down  = no (λ ())
Right ≟ₐ Left  = no (λ ())
Right ≟ₐ Right = yes refl

------------------------------------------------------------------------
-- Reward
------------------------------------------------------------------------

Reward : Set
Reward = ℕ

_≤ᵣ_ : Reward → Reward → Set
n ≤ᵣ m = n ≤ m

------------------------------------------------------------------------
-- Transition Function
--
-- Move in the grid, clamping at boundaries.
-- Reward = 10 at goal, 0 elsewhere.
------------------------------------------------------------------------

-- Clamp to grid bounds
clamp : ℕ → ℕ
clamp n = if n <ᵇ Size then n else (Size ∸ 1)

-- Move function
move : State → Action → State
move (pos px py) Up    = pos px (clamp (suc py))
move (pos px py) Down  = pos px (py ∸ 1)
move (pos px py) Left  = pos (px ∸ 1) py
move (pos px py) Right = pos (clamp (suc px)) py

-- Reward function
reward : State → Reward
reward s = if at-goal s then 10 else 0

-- Step function
step : State → Action → State × Reward
step s a = let s' = move s a in (s' , reward s')

default-action : Action
default-action = Up

horizon : ℕ
horizon = 10

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
-- Test 1: Basic Movement
------------------------------------------------------------------------

-- From start (0,0), moving Right goes to (1,0)
test-move-right : move start Right ≡ pos 1 0
test-move-right = refl

-- From start (0,0), moving Up goes to (0,1)
test-move-up : move start Up ≡ pos 0 1
test-move-up = refl

-- At boundary, movement is clamped
test-move-left-boundary : move start Left ≡ pos 0 0
test-move-left-boundary = refl

test-move-down-boundary : move start Down ≡ pos 0 0
test-move-down-boundary = refl

------------------------------------------------------------------------
-- Test 2: Goal Detection
------------------------------------------------------------------------

test-not-at-goal-start : at-goal start ≡ false
test-not-at-goal-start = refl

test-at-goal : at-goal goal ≡ true
test-at-goal = refl

------------------------------------------------------------------------
-- Test 3: Ranking at Various Depths
--
-- From start (0,0), Right and Up move toward goal (4,4).
-- Left and Down move away (or stay at boundary).
-- At sufficient depth, Right/Up should be ranked higher.
------------------------------------------------------------------------

-- At depth 0, traces are empty, ranking is arbitrary
test-ranking-depth-0 : find-ranking start 0 ≡ Up ∷ Down ∷ Left ∷ Right ∷ []
test-ranking-depth-0 = refl

-- At depth 1, immediate rewards are 0 (not at goal yet)
test-trace-right-1 : trace-action start Right 1 ≡ 0 ∷ 0 ∷ []
test-trace-right-1 = refl

-- At higher depths, ranking should favor goal-directed actions
-- Let's check depth 8 (Manhattan distance to goal)
-- Note: Up and Right are equally good from (0,0), but insertion sort order matters
test-ranking-depth-8 : find-ranking start 8 ≡ Up ∷ Right ∷ Down ∷ Left ∷ []
test-ranking-depth-8 = refl

------------------------------------------------------------------------
-- Test 4: Middle of Grid
--
-- From (2,2), all directions are valid moves.
-- Right and Up should be preferred (toward goal).
------------------------------------------------------------------------

middle : State
middle = pos 2 2

test-ranking-middle-8 : find-ranking middle 8 ≡ Up ∷ Right ∷ Down ∷ Left ∷ []
test-ranking-middle-8 = refl

------------------------------------------------------------------------
-- Test 5: Near Goal
--
-- From (3,4), only Right leads to goal.
-- From (4,3), only Up leads to goal.
------------------------------------------------------------------------

near-goal-x : State
near-goal-x = pos 3 4

near-goal-y : State
near-goal-y = pos 4 3

-- One step from goal in X direction
test-ranking-near-x : find-ranking near-goal-x 2 ≡ Right ∷ Up ∷ Down ∷ Left ∷ []
test-ranking-near-x = refl

-- One step from goal in Y direction
test-ranking-near-y : find-ranking near-goal-y 2 ≡ Up ∷ Right ∷ Down ∷ Left ∷ []
test-ranking-near-y = refl

------------------------------------------------------------------------
-- Test 6: At Goal (Absorbing)
--
-- At goal, reward is 10. All actions stay at goal (absorbing behavior
-- due to boundary clamping at (4,4)).
------------------------------------------------------------------------

test-at-goal-stays : move goal Up ≡ goal
test-at-goal-stays = refl

test-at-goal-reward : reward goal ≡ 10
test-at-goal-reward = refl

-- All actions from goal have same trace (all give 10 forever)
test-trace-goal : trace-action goal Up 2 ≡ 10 ∷ 10 ∷ 10 ∷ []
test-trace-goal = refl

------------------------------------------------------------------------
-- Test 7: Learning Convergence
--
-- Samples from start state should not cause depth increases
-- once ranking is correct.
------------------------------------------------------------------------

sample-start-right-left : Sample
sample-start-right-left = sample start Right Left

sample-start-up-down : Sample
sample-start-up-down = sample start Up Down

-- At depth 8, the ranking is stable (no violations)
test-no-violation-8 : test-pair 8 sample-start-right-left ≡ nothing
test-no-violation-8 = refl

------------------------------------------------------------------------
-- Test 8: Trace Values at Goal Path
--
-- Following optimal path: (0,0) → (1,0) → ... → (4,0) → (4,1) → ... → (4,4)
-- First reward appears at step 8 (when reaching goal).
------------------------------------------------------------------------

-- After 8 Right moves from (0,0), we'd be at (4,0) then need 4 Up moves
-- Total: 8 steps to reach goal. Trace at depth 8 should show reward.

-- Simpler test: from (4,3), one Up reaches goal
test-trace-near-goal : trace-action near-goal-y Up 1 ≡ 10 ∷ 10 ∷ []
test-trace-near-goal = refl

-- Compare with Down (moves to (4,2), away from goal)
test-trace-away-goal : trace-action near-goal-y Down 1 ≡ 0 ∷ 0 ∷ []
test-trace-away-goal = refl

------------------------------------------------------------------------
-- Summary
--
-- GridWorld5x5 demonstrates:
-- 1. ✓ 25 states, 4 actions scale efficiently
-- 2. ✓ Ranking evolves: depth 0 arbitrary → depth 8 correct
-- 3. ✓ Goal-directed actions (Right, Up) ranked higher
-- 4. ✓ Position-dependent ranking (near-x vs near-y)
-- 5. ✓ Absorbing goal state (constant high reward)
-- 6. ✓ Trace comparison correctly orders actions
--
-- The CSHRL finder discovers the optimal policy by comparing traces
-- to depth 8 (the horizon for this task). No violations at convergence.
------------------------------------------------------------------------


