{-# OPTIONS --safe --guardedness #-}

-- =============================================================================
-- Key-Treasure 10x10: Violation Counting for Learning Analysis
-- =============================================================================
-- Counts ranking violations at each depth to demonstrate monotonic improvement
-- =============================================================================

module CSHRL.Tasks.Verified.KeyTreasureViolations where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Bool using (Bool; true; false; if_then_else_; not; _∧_)
open import Data.List using (List; []; _∷_; length; map; filter; foldr)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import CSHRL.Tasks.Verified.KeyTreasure10x10

-- =============================================================================
-- Violation Detection
-- =============================================================================

-- A violation occurs when the finder ranking at depth k 
-- disagrees with the ranking at depth k+1 (or final converged ranking)
-- This measures "not yet converged" pairs

-- Reference ranking (depth 10 - assumed converged for this task)
reference-ranking-origin : List Action
reference-ranking-origin = Up ∷ Right ∷ Down ∷ Left ∷ []

-- Find position of action in ranking (0 = best)
find-pos : List Action → Action → ℕ → ℕ
find-pos [] _ n = n
find-pos (x ∷ xs) a n = if (x ≟ₐ a) then n else find-pos xs a (suc n)

open import Data.Nat using (_≤ᵇ_)

-- XOR for booleans
xor : Bool → Bool → Bool
xor true true = false
xor false false = false
xor _ _ = true

-- Check if two rankings agree on which action is better
rankings-agree : List Action → List Action → Action → Action → Bool
rankings-agree r1 r2 a b = 
  let pos1-a = find-pos r1 a 0
      pos1-b = find-pos r1 b 0
      pos2-a = find-pos r2 a 0
      pos2-b = find-pos r2 b 0
      order1 = pos1-a ≤ᵇ pos1-b
      order2 = pos2-a ≤ᵇ pos2-b
      -- Both agree on ordering (both true or both false)
  in not (xor order1 order2)

-- Count disagreements between a ranking and reference
count-violations : List Action → List Action → ℕ
count-violations ranking reference = 
  count-pairs (Up ∷ Down ∷ Left ∷ Right ∷ [])
  where
    check-pair : Action → Action → ℕ
    check-pair a b = if rankings-agree ranking reference a b then 0 else 1
    
    count-pairs : List Action → ℕ
    count-pairs [] = 0
    count-pairs (a ∷ rest) = foldr (λ b acc → check-pair a b + acc) 0 rest + count-pairs rest

-- =============================================================================
-- Violation Counts at Each Depth (Origin State)
-- =============================================================================

-- These will be normalized to get actual counts
violations-d0 : ℕ
violations-d0 = count-violations (find-ranking s-origin 0) reference-ranking-origin

violations-d1 : ℕ
violations-d1 = count-violations (find-ranking s-origin 1) reference-ranking-origin

violations-d2 : ℕ
violations-d2 = count-violations (find-ranking s-origin 2) reference-ranking-origin

violations-d3 : ℕ
violations-d3 = count-violations (find-ranking s-origin 3) reference-ranking-origin

violations-d4 : ℕ
violations-d4 = count-violations (find-ranking s-origin 4) reference-ranking-origin

violations-d5 : ℕ
violations-d5 = count-violations (find-ranking s-origin 5) reference-ranking-origin

-- =============================================================================
-- Tests to Extract Violation Counts
-- =============================================================================

-- Depth 0: Up,Down,Left,Right vs Up,Right,Down,Left
-- Disagreements: (Down,Right), (Down,Left), (Right,Left) positions differ
-- Actually need to check systematically

-- For 4 actions, there are C(4,2) = 6 pairs to check:
-- (Up,Down), (Up,Left), (Up,Right), (Down,Left), (Down,Right), (Left,Right)

-- At depth 0: Up,Down,Left,Right (positions: Up=0, Down=1, Left=2, Right=3)
-- Reference:  Up,Right,Down,Left (positions: Up=0, Right=1, Down=2, Left=3)
-- 
-- Pair (Up,Down): d0 says Up<Down (0<1), ref says Up<Down (0<2) ✓ AGREE
-- Pair (Up,Left): d0 says Up<Left (0<2), ref says Up<Left (0<3) ✓ AGREE  
-- Pair (Up,Right): d0 says Up<Right (0<3), ref says Up<Right (0<1) ✓ AGREE
-- Pair (Down,Left): d0 says Down<Left (1<2), ref says Down<Left (2<3) ✓ AGREE
-- Pair (Down,Right): d0 says Down<Right (1<3), ref says Down>Right (2>1) ✗ DISAGREE
-- Pair (Left,Right): d0 says Left<Right (2<3), ref says Left>Right (3>1) ✗ DISAGREE
--
-- So depth 0 has 2 violations

test-violations-d0 : violations-d0 ≡ 2
test-violations-d0 = refl

-- Depth 3: Up,Right,Down,Left - same as reference
test-violations-d3 : violations-d3 ≡ 0
test-violations-d3 = refl

-- Depth 5: should also be 0
test-violations-d5 : violations-d5 ≡ 0
test-violations-d5 = refl

-- =============================================================================
-- Ranking Correctness (as percentage of correct pairs)
-- =============================================================================

-- Total pairs = 6 for 4 actions
total-pairs : ℕ
total-pairs = 6

-- Correct pairs = total - violations
correct-d0 : ℕ
correct-d0 = 6 ∸ violations-d0
  where open import Data.Nat using (_∸_)

correct-d3 : ℕ
correct-d3 = 6 ∸ violations-d3
  where open import Data.Nat using (_∸_)

-- Tests
test-correct-d0 : correct-d0 ≡ 4
test-correct-d0 = refl

test-correct-d3 : correct-d3 ≡ 6
test-correct-d3 = refl

-- =============================================================================
-- Summary Data for Plotting
-- =============================================================================
-- 
-- Depth | Ranking                  | Violations | Correct | %Correct
-- ------|--------------------------|------------|---------|----------
-- 0     | Up,Down,Left,Right       | 2          | 4       | 66.7%
-- 1     | Up,Down,Left,Right       | 2          | 4       | 66.7%
-- 2     | Up,Down,Left,Right       | 2          | 4       | 66.7%
-- 3     | Up,Right,Down,Left       | 0          | 6       | 100%
-- 4     | Up,Right,Down,Left       | 0          | 6       | 100%
-- 5     | Up,Right,Down,Left       | 0          | 6       | 100%
-- 8     | Up,Right,Down,Left       | 0          | 6       | 100%
-- 10    | Up,Right,Down,Left       | 0          | 6       | 100%
--
-- Key observation: Monotonic improvement - violations never increase!
-- Convergence at depth 3 (when key reward becomes visible)
-- =============================================================================

