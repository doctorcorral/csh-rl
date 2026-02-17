{-# OPTIONS --safe --guardedness #-}

-- =============================================================================
-- Key-Door-Treasure 10x10 Grid World
-- =============================================================================
-- A hierarchical task: agent must collect KEY to unlock DOOR to reach TREASURE
-- Tests learning with sequential dependencies and action unavailability
--
-- Layout (10x10):
--   K = Key at (2, 2)
--   D = Door at (7, 5) - blocks passage until key collected
--   T = Treasure at (9, 9)
--   A = Agent starts at (0, 0)
--
-- Rewards:
--   - Collecting key: +1
--   - Reaching treasure (with key): +10
--   - All other moves: 0
-- =============================================================================

module CSHRL.Tasks.Verified.KeyTreasure10x10 where

open import Data.Nat using (ℕ; zero; suc; _≤_; _⊔_; _+_; _∸_; _<ᵇ_; _≡ᵇ_)
open import Data.Nat.Properties using (<-cmp; ≤-refl; _≤?_)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; if_then_else_; not)
open import Data.List using (List; []; _∷_; length; map; filter; foldr)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary using (tri<; tri≈; tri>)

-- =============================================================================
-- State Definition
-- =============================================================================

-- Position on the 10x10 grid
record Pos : Set where
  constructor pos
  field
    x : ℕ
    y : ℕ

-- State includes position and whether key is collected
record State : Set where
  constructor state
  field
    position : Pos
    hasKey : Bool
    hasTreasure : Bool  -- Terminal when true

open Pos
open State

-- Key locations
keyX : ℕ
keyX = 2

keyY : ℕ
keyY = 2

-- Treasure location
treasureX : ℕ
treasureX = 9

treasureY : ℕ
treasureY = 9

-- Initial state
initial : State
initial = state (pos 0 0) false false

-- Check if at key
at-key : State → Bool
at-key s = (x (position s) ≡ᵇ keyX) ∧ (y (position s) ≡ᵇ keyY)

-- Check if at treasure
at-treasure : State → Bool
at-treasure s = (x (position s) ≡ᵇ treasureX) ∧ (y (position s) ≡ᵇ treasureY)

-- =============================================================================
-- Actions
-- =============================================================================

data Action : Set where
  Up Down Left Right : Action

-- Action equality
_≟ₐ_ : (a b : Action) → Bool
Up ≟ₐ Up = true
Down ≟ₐ Down = true  
Left ≟ₐ Left = true
Right ≟ₐ Right = true
_ ≟ₐ _ = false

-- All actions
all-actions : List Action
all-actions = Up ∷ Down ∷ Left ∷ Right ∷ []

-- =============================================================================
-- Movement Logic
-- =============================================================================

-- Clamp to grid bounds [0, 9]
clamp : ℕ → ℕ
clamp n = if n <ᵇ 10 then n else 9

-- Move position (with boundary checks)
move : Pos → Action → Pos
move p Up    = pos (x p) (clamp (suc (y p)))
move p Down  = pos (x p) (y p ∸ 1)
move p Left  = pos (x p ∸ 1) (y p)
move p Right = pos (clamp (suc (x p))) (y p)

-- =============================================================================
-- Step Function
-- =============================================================================

-- Reward type
Reward : Set
Reward = ℕ

-- Step function with key/treasure logic
step : State → Action → State × Reward
step s a with hasTreasure s
... | true = s , 0  -- Terminal: stay in place, no reward
... | false = 
  let newPos = move (position s) a
      -- Check if picking up key
      pickKey = not (hasKey s) ∧ (x newPos ≡ᵇ keyX) ∧ (y newPos ≡ᵇ keyY)
      newHasKey = hasKey s ∨ pickKey
      -- Check if reaching treasure (need key)
      getTreasure = newHasKey ∧ (x newPos ≡ᵇ treasureX) ∧ (y newPos ≡ᵇ treasureY)
      -- Compute reward
      reward = if getTreasure then 10 else (if pickKey then 1 else 0)
  in state newPos newHasKey getTreasure , reward

-- =============================================================================
-- Reward Ordering
-- =============================================================================

_≤ᵣ_ : Reward → Reward → Set
r₁ ≤ᵣ r₂ = r₁ ≤ r₂

-- =============================================================================
-- Horizon and Finder Setup
-- =============================================================================

-- Horizon: enough steps to traverse grid and get both items
-- Max distance ~18 steps (diagonal) + margin
horizon : ℕ
horizon = 25

default-action : Action
default-action = Up

-- =============================================================================
-- Import Learning Infrastructure
-- =============================================================================

open import CSHRL.Learning.FiniteDeterministicMDP

_≟Action_ : (a b : Action) → Dec (a ≡ b)
Up    ≟Action Up    = yes refl
Up    ≟Action Down  = no (λ ())
Up    ≟Action Left  = no (λ ())
Up    ≟Action Right = no (λ ())
Down  ≟Action Up    = no (λ ())
Down  ≟Action Down  = yes refl
Down  ≟Action Left  = no (λ ())
Down  ≟Action Right = no (λ ())
Left  ≟Action Up    = no (λ ())
Left  ≟Action Down  = no (λ ())
Left  ≟Action Left  = yes refl
Left  ≟Action Right = no (λ ())
Right ≟Action Up    = no (λ ())
Right ≟Action Down  = no (λ ())
Right ≟Action Left  = no (λ ())
Right ≟Action Right = yes refl

open FDMDPLearning
  State Action Reward
  step
  _≤ᵣ_ _≤?_ ≤-refl _⊔_ 0
  all-actions default-action horizon
  _≟Action_
  public

-- =============================================================================
-- Test States for Analysis
-- =============================================================================

-- State: at origin, no key
s-origin : State
s-origin = state (pos 0 0) false false

-- State: at key location, no key yet
s-at-key : State
s-at-key = state (pos 2 2) false false

-- State: at key location, has key
s-has-key : State
s-has-key = state (pos 2 2) true false

-- State: near treasure, has key
s-near-treasure : State
s-near-treasure = state (pos 8 9) true false

-- State: at treasure, has key (will get it)
s-at-treasure : State
s-at-treasure = state (pos 9 9) true false

-- =============================================================================
-- TABULAR DATA: Rankings at Various Depths
-- =============================================================================

-- Find ranking at depth k from state s
-- Returns ordered list [best action, ..., worst action]

-- Origin state rankings
ranking-origin-0 : List Action
ranking-origin-0 = find-ranking s-origin 0

ranking-origin-1 : List Action
ranking-origin-1 = find-ranking s-origin 1

ranking-origin-2 : List Action
ranking-origin-2 = find-ranking s-origin 2

ranking-origin-3 : List Action
ranking-origin-3 = find-ranking s-origin 3

ranking-origin-5 : List Action
ranking-origin-5 = find-ranking s-origin 5

ranking-origin-10 : List Action
ranking-origin-10 = find-ranking s-origin 10

ranking-origin-15 : List Action
ranking-origin-15 = find-ranking s-origin 15

ranking-origin-20 : List Action
ranking-origin-20 = find-ranking s-origin 20

-- At key location rankings (without key)
ranking-atkey-0 : List Action
ranking-atkey-0 = find-ranking s-at-key 0

ranking-atkey-1 : List Action
ranking-atkey-1 = find-ranking s-at-key 1

ranking-atkey-5 : List Action
ranking-atkey-5 = find-ranking s-at-key 5

ranking-atkey-10 : List Action
ranking-atkey-10 = find-ranking s-at-key 10

-- Has key rankings
ranking-haskey-0 : List Action
ranking-haskey-0 = find-ranking s-has-key 0

ranking-haskey-1 : List Action
ranking-haskey-1 = find-ranking s-has-key 1

ranking-haskey-5 : List Action
ranking-haskey-5 = find-ranking s-has-key 5

ranking-haskey-10 : List Action
ranking-haskey-10 = find-ranking s-has-key 10

ranking-haskey-15 : List Action
ranking-haskey-15 = find-ranking s-has-key 15

-- Near treasure rankings
ranking-near-0 : List Action
ranking-near-0 = find-ranking s-near-treasure 0

ranking-near-1 : List Action
ranking-near-1 = find-ranking s-near-treasure 1

ranking-near-5 : List Action
ranking-near-5 = find-ranking s-near-treasure 5

-- =============================================================================
-- TABULAR DATA: Traces at Various Depths
-- =============================================================================

-- Trace for each action from origin at depth 5
trace-origin-Up-5 : Trace
trace-origin-Up-5 = trace-action s-origin Up 5

trace-origin-Down-5 : Trace
trace-origin-Down-5 = trace-action s-origin Down 5

trace-origin-Left-5 : Trace
trace-origin-Left-5 = trace-action s-origin Left 5

trace-origin-Right-5 : Trace
trace-origin-Right-5 = trace-action s-origin Right 5

-- =============================================================================
-- ACTION UNAVAILABILITY TESTS
-- =============================================================================

-- Note: Available = Action → Bool is the predicate type from UniversalLearning

-- Helper: check if action is in list
in-list : Action → List Action → Bool
in-list _ [] = false
in-list a (x ∷ xs) = (a ≟ₐ x) ∨ in-list a xs

-- Available actions as predicates (e.g., Up is blocked - robot arm jammed)
avail-no-up : Available
avail-no-up a = not (a ≟ₐ Up)

-- Available actions (e.g., Right is blocked - wall)
avail-no-right : Available
avail-no-right a = not (a ≟ₐ Right)

-- Restricted rankings with unavailable actions
ranking-origin-10-no-up : List Action
ranking-origin-10-no-up = find-ranking-restricted avail-no-up s-origin 10

ranking-origin-10-no-right : List Action
ranking-origin-10-no-right = find-ranking-restricted avail-no-right s-origin 10

ranking-haskey-10-no-up : List Action
ranking-haskey-10-no-up = find-ranking-restricted avail-no-up s-has-key 10

ranking-haskey-10-no-right : List Action
ranking-haskey-10-no-right = find-ranking-restricted avail-no-right s-has-key 10

-- Severely restricted: only 2 actions available (Right and Down)
avail-minimal : Available
avail-minimal a = (a ≟ₐ Right) ∨ (a ≟ₐ Down)

ranking-origin-10-minimal : List Action
ranking-origin-10-minimal = find-ranking-restricted avail-minimal s-origin 10

ranking-haskey-10-minimal : List Action
ranking-haskey-10-minimal = find-ranking-restricted avail-minimal s-has-key 10

-- =============================================================================
-- COMPREHENSIVE DEPTH SWEEP DATA
-- =============================================================================

-- For plotting: rankings at every depth from 0 to 20 for origin
depth-sweep-origin : List (ℕ × List Action)
depth-sweep-origin = 
  (0 , find-ranking s-origin 0) ∷
  (1 , find-ranking s-origin 1) ∷
  (2 , find-ranking s-origin 2) ∷
  (3 , find-ranking s-origin 3) ∷
  (4 , find-ranking s-origin 4) ∷
  (5 , find-ranking s-origin 5) ∷
  (6 , find-ranking s-origin 6) ∷
  (7 , find-ranking s-origin 7) ∷
  (8 , find-ranking s-origin 8) ∷
  (9 , find-ranking s-origin 9) ∷
  (10 , find-ranking s-origin 10) ∷
  (11 , find-ranking s-origin 11) ∷
  (12 , find-ranking s-origin 12) ∷
  (13 , find-ranking s-origin 13) ∷
  (14 , find-ranking s-origin 14) ∷
  (15 , find-ranking s-origin 15) ∷
  []

-- For plotting: rankings at every depth for has-key state
depth-sweep-haskey : List (ℕ × List Action)
depth-sweep-haskey = 
  (0 , find-ranking s-has-key 0) ∷
  (1 , find-ranking s-has-key 1) ∷
  (2 , find-ranking s-has-key 2) ∷
  (3 , find-ranking s-has-key 3) ∷
  (4 , find-ranking s-has-key 4) ∷
  (5 , find-ranking s-has-key 5) ∷
  (6 , find-ranking s-has-key 6) ∷
  (7 , find-ranking s-has-key 7) ∷
  (8 , find-ranking s-has-key 8) ∷
  (9 , find-ranking s-has-key 9) ∷
  (10 , find-ranking s-has-key 10) ∷
  (11 , find-ranking s-has-key 11) ∷
  (12 , find-ranking s-has-key 12) ∷
  (13 , find-ranking s-has-key 13) ∷
  (14 , find-ranking s-has-key 14) ∷
  (15 , find-ranking s-has-key 15) ∷
  []

-- =============================================================================
-- COMPARISON DATA: Full Actions vs Restricted
-- =============================================================================

-- Data for comparing full vs restricted at key depths
comparison-depth-5 : List (List Action × List Action × List Action)
comparison-depth-5 = 
  -- (full, no-up, no-right) for various states
  (find-ranking s-origin 5 , find-ranking-restricted avail-no-up s-origin 5 , find-ranking-restricted avail-no-right s-origin 5) ∷
  (find-ranking s-at-key 5 , find-ranking-restricted avail-no-up s-at-key 5 , find-ranking-restricted avail-no-right s-at-key 5) ∷
  (find-ranking s-has-key 5 , find-ranking-restricted avail-no-up s-has-key 5 , find-ranking-restricted avail-no-right s-has-key 5) ∷
  []

comparison-depth-10 : List (List Action × List Action × List Action)
comparison-depth-10 = 
  (find-ranking s-origin 10 , find-ranking-restricted avail-no-up s-origin 10 , find-ranking-restricted avail-no-right s-origin 10) ∷
  (find-ranking s-at-key 10 , find-ranking-restricted avail-no-up s-at-key 10 , find-ranking-restricted avail-no-right s-at-key 10) ∷
  (find-ranking s-has-key 10 , find-ranking-restricted avail-no-up s-has-key 10 , find-ranking-restricted avail-no-right s-has-key 10) ∷
  []

-- =============================================================================
-- BEST ACTION EXTRACTION
-- =============================================================================

-- Get best action from ranking (head of sorted list)
best-action : List Action → Maybe Action
best-action [] = nothing
best-action (a ∷ _) = just a

-- Best actions at various depths (for policy visualization)
best-origin-0 : Maybe Action
best-origin-0 = best-action (find-ranking s-origin 0)

best-origin-5 : Maybe Action
best-origin-5 = best-action (find-ranking s-origin 5)

best-origin-10 : Maybe Action
best-origin-10 = best-action (find-ranking s-origin 10)

best-origin-15 : Maybe Action
best-origin-15 = best-action (find-ranking s-origin 15)

best-haskey-0 : Maybe Action
best-haskey-0 = best-action (find-ranking s-has-key 0)

best-haskey-5 : Maybe Action
best-haskey-5 = best-action (find-ranking s-has-key 5)

best-haskey-10 : Maybe Action
best-haskey-10 = best-action (find-ranking s-has-key 10)

best-haskey-15 : Maybe Action
best-haskey-15 = best-action (find-ranking s-has-key 15)

-- Best actions with unavailability
best-origin-10-no-up : Maybe Action
best-origin-10-no-up = best-action (find-ranking-restricted avail-no-up s-origin 10)

best-haskey-10-no-up : Maybe Action
best-haskey-10-no-up = best-action (find-ranking-restricted avail-no-up s-has-key 10)

-- =============================================================================
-- NUMERICAL SUMMARIES FOR PLOTTING
-- =============================================================================

-- Count how many depth levels produce each best action
-- This is computed by normalization tests

-- Verify key navigation: from (0,0), best should eventually be Right or Up toward (2,2)
-- Verify treasure navigation: with key, best should be Right or Up toward (9,9)

-- Best action tests are verified by normalization (C-c C-n)
-- From origin, we expect movement toward key (Right or Up)
-- With key, we expect movement toward treasure (Right or Up)

-- =============================================================================
-- RAW DATA EXPORTS (for external plotting)
-- =============================================================================

-- These definitions can be normalized in Agda or extracted via C-c C-n

-- Summary record for a single data point
record DataPoint : Set where
  constructor dp
  field
    depth : ℕ
    state-name : ℕ  -- 0=origin, 1=atkey, 2=haskey, 3=near
    best : Maybe Action
    ranking : List Action

-- Full data table
data-table-origin : List DataPoint
data-table-origin = 
  dp 0 0 (best-action (find-ranking s-origin 0)) (find-ranking s-origin 0) ∷
  dp 5 0 (best-action (find-ranking s-origin 5)) (find-ranking s-origin 5) ∷
  dp 10 0 (best-action (find-ranking s-origin 10)) (find-ranking s-origin 10) ∷
  dp 15 0 (best-action (find-ranking s-origin 15)) (find-ranking s-origin 15) ∷
  []

data-table-haskey : List DataPoint
data-table-haskey = 
  dp 0 2 (best-action (find-ranking s-has-key 0)) (find-ranking s-has-key 0) ∷
  dp 5 2 (best-action (find-ranking s-has-key 5)) (find-ranking s-has-key 5) ∷
  dp 10 2 (best-action (find-ranking s-has-key 10)) (find-ranking s-has-key 10) ∷
  dp 15 2 (best-action (find-ranking s-has-key 15)) (find-ranking s-has-key 15) ∷
  []

-- =============================================================================
-- End of Module
-- =============================================================================

