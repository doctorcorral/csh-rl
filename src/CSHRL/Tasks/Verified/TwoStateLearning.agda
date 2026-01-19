{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- TwoStateLearning: Demonstrating Learning with TwoState MDP
--
-- This module instantiates CSHRL.Learning.FiniteDeterministicMDP
-- with the TwoState task and demonstrates:
--   1. Learning loop convergence
--   2. Ranking discovery
--   3. Action unavailability handling
------------------------------------------------------------------------

module CSHRL.Tasks.Verified.TwoStateLearning where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _≤_; _⊔_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (Dec; yes; no)
open import Data.List using (List; _∷_; [])
open import Data.Maybe using (Maybe; just; nothing)

------------------------------------------------------------------------
-- Domain (same as TwoState)
------------------------------------------------------------------------

data State : Set where
  Start : State
  Goal  : State

data Action : Set where
  Go   : Action
  Stay : Action

Reward : Set
Reward = ℕ

_≤ᵣ_ : Reward → Reward → Set
n ≤ᵣ m = n ≤ m

_≤?_ : Reward → Reward → Bool
zero  ≤? _     = true
suc n ≤? zero  = false
suc n ≤? suc m = n ≤? m

≤?-sound : ∀ r s → r ≤? s ≡ true → r ≤ᵣ s
≤?-sound zero    _       _  = z≤n
≤?-sound (suc r) (suc s) p  = s≤s (≤?-sound r s p)

≤?-refl : ∀ r → r ≤? r ≡ true
≤?-refl zero    = refl
≤?-refl (suc r) = ≤?-refl r

-- Decidable equality for actions
_≟ₐ_ : (a b : Action) → Dec (a ≡ b)
Go   ≟ₐ Go   = yes refl
Go   ≟ₐ Stay = no (λ ())
Stay ≟ₐ Go   = no (λ ())
Stay ≟ₐ Stay = yes refl

move : State → Action → State
move Start Go   = Goal
move Start Stay = Start
move Goal  _    = Goal

reward-fn : State → Reward
reward-fn Goal  = 1
reward-fn Start = 0

step : State → Action → State × Reward
step s a = (move s a , reward-fn (move s a))

all-actions : List Action
all-actions = Go ∷ Stay ∷ []

------------------------------------------------------------------------
-- Instantiate Learning Module
------------------------------------------------------------------------

open import CSHRL.Learning.FiniteDeterministicMDP

open FDMDPLearning 
  State Action Reward step
  _≤ᵣ_ _⊔_ 0 all-actions
  _≤?_ ≤?-sound ≤?-refl
  _≟ₐ_

------------------------------------------------------------------------
-- Test 1: Ranking Discovery
--
-- At depth 0: Both actions give immediate reward (0 from Start, 1 from Goal)
-- At depth 1: Go from Start → Goal (reward 1), Stay from Start → Start (reward 0)
--             Go should be ranked higher than Stay
------------------------------------------------------------------------

-- The ranking at depth 1 should put Go first (better trace)
test-ranking-depth-1 : find-ranking Start 1 ≡ Go ∷ Stay ∷ []
test-ranking-depth-1 = refl

-- From Goal, both actions loop back to Goal with reward 1
test-ranking-goal : find-ranking Goal 1 ≡ Go ∷ Stay ∷ []
test-ranking-goal = refl

------------------------------------------------------------------------
-- Test 2: Trace Comparison
--
-- trace-action Start Go 1 = [1, 1]  (Go→Goal, reward 1, then best from Goal is 1)
-- trace-action Start Stay 1 = [0, 1]  (Stay→Start, reward 0, then best from Start is 1)
-- So Go > Stay lexicographically
------------------------------------------------------------------------

test-trace-go : trace-action Start Go 1 ≡ 1 ∷ 1 ∷ []
test-trace-go = refl

test-trace-stay : trace-action Start Stay 1 ≡ 0 ∷ 1 ∷ []
test-trace-stay = refl

-- Go's trace dominates Stay's trace
test-trace-comparison : (trace-action Start Stay 1 ≤ₜ trace-action Start Go 1) ≡ true
test-trace-comparison = refl

------------------------------------------------------------------------
-- Test 3: Violation Detection
--
-- With corrected semantics:
-- - Ranking list [Go, Stay] means Go is best
-- - rank a b = true means a ≤ b (a is dominated by b)
-- - So: Stay ≤ Go = true (Stay is dominated by Go)
--       Go ≤ Stay = false (Go is NOT dominated by Stay)
------------------------------------------------------------------------

-- finder-ranking 1 Start Stay Go: Is Stay ≤ Go? 
-- In [Go, Stay], Go appears first (is best), so Stay ≤ Go = true
test-finder-ranking-stay-go : finder-ranking 1 Start Stay Go ≡ true
test-finder-ranking-stay-go = refl

-- finder-ranking 1 Start Go Stay: Is Go ≤ Stay?
-- In [Go, Stay], Go appears first (is best), so Go ≤ Stay = false
test-finder-ranking-go-stay : finder-ranking 1 Start Go Stay ≡ false
test-finder-ranking-go-stay = refl

-- Test for violations:
-- test-pair checks: if rank a b = true but trace a ≤ₜ trace b = false, then violation

-- (Stay, Go): rank = true, trace(Stay) ≤ₜ trace(Go) = [0,1] ≤ₜ [1,1] = true (0 < 1)
-- No violation! The ranking correctly reflects trace ordering.
test-no-violation-stay-go : test-pair 1 (sample Start Stay Go) ≡ nothing
test-no-violation-stay-go = refl

-- (Go, Stay): rank = false, so no check needed
test-no-violation-go-stay : test-pair 1 (sample Start Go Stay) ≡ nothing
test-no-violation-go-stay = refl

-- At depth 0:
test-ranking-depth-0 : find-ranking Start 0 ≡ Go ∷ Stay ∷ []
test-ranking-depth-0 = refl

-- trace(Stay) ≤ₜ trace(Go) at depth 0: [0] ≤ₜ [1] = true
-- So no violation at depth 0 either!
test-no-violation-depth-0 : test-pair 0 (sample Start Stay Go) ≡ nothing
test-no-violation-depth-0 = refl

------------------------------------------------------------------------
-- Test 4: Learning Loop
--
-- With correct semantics, no violations means learning converges immediately.
------------------------------------------------------------------------

-- Sample definitions
sample-start-stay-go : Sample
sample-start-stay-go = sample Start Stay Go

sample-start-go-stay : Sample
sample-start-go-stay = sample Start Go Stay

-- Traces at depth 0
test-trace-go-0 : trace-action Start Go 0 ≡ 1 ∷ []
test-trace-go-0 = refl

test-trace-stay-0 : trace-action Start Stay 0 ≡ 0 ∷ []
test-trace-stay-0 = refl

-- With correct semantics, no violations at any depth!
-- (Stay, Go): rank = true, trace ≤ = true → no violation
-- (Go, Stay): rank = false → no check needed

-- Learning step doesn't increase depth when no violation
test-learn-step-no-change : learn-step 0 sample-start-stay-go ≡ 0
test-learn-step-no-change = refl

test-learn-step-no-change-2 : learn-step 1 sample-start-go-stay ≡ 1
test-learn-step-no-change-2 = refl

-- Learning loop over multiple samples
test-learn-loop : learn-loop 0 (sample-start-stay-go ∷ sample-start-go-stay ∷ []) ≡ 0
test-learn-loop = refl

-- The learned ranking is the same as finder at depth 0
test-learned-ranking : learned-ranking 0 (sample-start-stay-go ∷ []) Start Stay Go ≡ true
test-learned-ranking = refl

------------------------------------------------------------------------
-- Test 5: Totality
--
-- The finder ranking is always total.
------------------------------------------------------------------------

open import Data.Sum using (_⊎_; inj₁; inj₂)

-- Totality at Start
test-totality-start : ∀ a b → finder-ranking 1 Start a b ≡ true ⊎ finder-ranking 1 Start b a ≡ true
test-totality-start = finder-ranking-total 1 Start

------------------------------------------------------------------------
-- Test 6: Action Unavailability
--
-- If Go becomes unavailable, the restricted ranking only contains Stay.
------------------------------------------------------------------------

-- Make Go unavailable
go-unavailable : Available
go-unavailable = make-unavailable Go all-available

-- Check that Go is filtered out
test-go-unavailable : go-unavailable Go ≡ false
test-go-unavailable = refl

test-stay-available : go-unavailable Stay ≡ true
test-stay-available = refl

-- Restricted ranking only has Stay
test-restricted-ranking : find-ranking-restricted go-unavailable Start 1 ≡ Stay ∷ []
test-restricted-ranking = refl

-- Adapted ranking for unavailability
test-adapt : adapt-to-unavailability go-unavailable 1 Start Stay Stay ≡ true
test-adapt = refl

------------------------------------------------------------------------
-- Summary
--
-- This module demonstrates:
-- 1. Ranking discovery via traces
-- 2. Trace computation and comparison
-- 3. Violation detection with correct semantics
-- 4. Learning loop converges when ranking is correct
-- 5. Totality of finder rankings
-- 6. Action unavailability handling
--
-- Semantics:
-- - Ranking list [best, ..., worst] with best first
-- - rank a b = true means "a ≤ b" (a is dominated by b)
-- - So if b appears before a in list, then a ≤ b = true
-- - Violations: rank a b = true but trace(a) > trace(b)
------------------------------------------------------------------------


