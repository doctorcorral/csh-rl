{-# OPTIONS --guardedness #-}

module CSHRL-Trap where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; _∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (_×_; _,_; proj₁)

-- 1. Domain: The Trap
-- Start (0) -> Trap (1) [Reward 10, then 0 forever]
-- Start (0) -> Safe (2) [Reward 0, then 100 forever]

data State : Set where
  Start : State
  Trap  : State
  Goal  : State

data Action : Set where
  TakeTrap : Action
  TakeSafe : Action
  Wait     : Action

Reward : Set
Reward = ℕ

_≤?_ : Reward → Reward → Bool
zero  ≤? _     = true
suc n ≤? zero  = false
suc n ≤? suc m = n ≤? m

step : State → Action → State × Reward
-- From Start
step Start TakeTrap = (Trap , 10) -- Greedy bait!
step Start TakeSafe = (Goal , 0)  -- Delayed gratification
step Start Wait     = (Start , 0)

-- From Trap (Stuck forever)
step Trap _ = (Trap , 0)

-- From Goal (Heaven)
step Goal _ = (Goal , 100)

all-actions : List Action
all-actions = TakeTrap ∷ TakeSafe ∷ Wait ∷ []

-- 2. Auto-Discovery using Finder
-- We do NOT define a ranking manually. We ask the algorithm to find it.

open import CSHRL-Finder
open Finder State Action Reward step _≤?_ TakeSafe all-actions

-- 3. The Test
-- Depth 1: Greedy choice wins.
-- TakeTrap gives 10. TakeSafe gives 0.
test-greedy : find-ranking Start 1 ≡ TakeTrap ∷ TakeSafe ∷ Wait ∷ []
test-greedy = refl

-- Depth 2: Insight emerges.
-- TakeTrap -> 10, 0.
-- TakeSafe -> 0, 100. (0,100) > (10,0) in lexicographic order?
-- Wait. Lexicographic comparison (10, 0) vs (0, 100).
-- 10 > 0. So (10, 0) wins lexicographically if we just compare head-first.
-- BUT, Ordinal Value Iteration compares traces.
-- Is 10 better than 0? Yes.
-- If our "Ordinal Value" is just a list, (10, 0) > (0, 100).
-- This means standard lexicographic order PREFERS immediate reward.
-- WE NEED A "PATIENT" ORDER or sufficient depth if the first rewards are equal?
-- NO! Lexicographic order IS greedy on the first element.
-- To solve the Trap, we need to "look past" the first element?
-- No, if the first element differs, lexicographic decides.
-- So standard lexicographic value iteration is GREEDY.
--
-- UNLESS: The "Trap" has 0 immediate reward, but leads to bad future.
-- Let's refine the Trap.
-- Path A: 0, 0, 0... (Trap)
-- Path B: 0, 0, 100... (Goal)
-- Here immediate is equal (0=0). Next is equal (0=0). Third is (0 vs 100).
-- Finder will find B > A at depth 3.
--
-- What if Path A has a small bait? (1, 0, 0...).
-- Then (1, 0, 0) > (0, 0, 100) lexicographically.
-- So Lexicographic Finder IS Greedy.
-- This is a feature/limitation of pure Ordinal/Lexicographic preference without discount.
-- It is "Optimism in the face of uncertainty" for equal prefixes, but "Greedy" for unequal.
--
-- To demonstrate "Discovery", let's use the "Silence of the Zeros" case (Sparse Reward).
-- That is what I called "Delayed Gratification" in the paper.
--
-- Let's implement THAT specifically as "The Trap" but strictly sparse.
-- Start -> Trap (0, 0, 0...)
-- Start -> Goal (0, 0, 100...)
--
-- This proves it finds the "needle in the haystack" of zeros.

step-sparse : State → Action → State × Reward
step-sparse Start TakeTrap = (Trap , 0)
step-sparse Start TakeSafe = (Goal , 0)
step-sparse Start Wait     = (Start , 0)
step-sparse Trap _ = (Trap , 0)
step-sparse Goal _ = (Goal , 100)

-- Re-import finder with sparse step
module SparseFinder where
  open import CSHRL-Finder
  open Finder State Action Reward step-sparse _≤?_ TakeSafe all-actions hiding (trace-action) renaming (find-ranking to sparse-rank)
  
  -- Depth 0: All 0 (Immediate only). Order is stable (defaults).
  test-blind : sparse-rank Start 0 ≡ TakeTrap ∷ TakeSafe ∷ Wait ∷ []
  test-blind = refl

  -- Depth 1: Lookahead 1.
  -- Trap -> (0, 0)
  -- Safe -> (0, 100)
  -- Wait -> (0, 0)
  -- Safe > Trap.
  test-insight : sparse-rank Start 1 ≡ TakeSafe ∷ TakeTrap ∷ Wait ∷ []
  test-insight = refl


