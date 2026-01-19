{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CoinFlip: A Simple Stochastic MDP Example
--
-- This is the simplest non-trivial stochastic environment:
-- - An agent can FLIP a fair coin or STAY
-- - FLIP leads to WIN (reward 1) or LOSE (reward 0) with equal probability
-- - STAY keeps the agent in the current state with reward 0
--
-- Demonstrates:
-- - Stochastic step function as distribution
-- - Expected trace computation
-- - Ranking based on expected value
------------------------------------------------------------------------

module CSHRL.Tasks.Stochastic.CoinFlip where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; _≤?_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)

open import CSHRL.Probability.Finite using (Dist; pure; _>>=_; fmap; bernoulli)

------------------------------------------------------------------------
-- MDP Definition
------------------------------------------------------------------------

-- States: Ready (can flip), Won (terminal), Lost (terminal)
data State : Set where
  Ready : State
  Won   : State
  Lost  : State

-- Actions: Flip the coin or Stay
data Action : Set where
  Flip : Action
  Stay : Action

-- Rewards are natural numbers
Reward : Set
Reward = ℕ

-- Stochastic step function
-- FLIP from Ready: 50% → Won (reward 1), 50% → Lost (reward 0)
-- STAY from Ready: 100% → Ready (reward 0)
-- From terminal states: always stay in same state (reward 0)
step : State → Action → Dist (State × Reward)
step Ready Flip = bernoulli (Won , 1) 1 (Lost , 0) 1   -- Fair coin
step Ready Stay = pure (Ready , 0)                      -- Stay put
step Won   _    = pure (Won , 0)                        -- Terminal
step Lost  _    = pure (Lost , 0)                       -- Terminal

------------------------------------------------------------------------
-- Reward Structure
------------------------------------------------------------------------

_≤ᵣ_ : Reward → Reward → Set
_≤ᵣ_ = _≤_

≤ᵣ-dec : (r s : Reward) → Dec (r ≤ᵣ s)
≤ᵣ-dec = _≤?_

≤ᵣ-refl : ∀ {r} → r ≤ᵣ r
≤ᵣ-refl = ≤-refl

_+ᵣ_ : Reward → Reward → Reward
_+ᵣ_ = _+_

-- Scalar multiplication: k * r
_*ᵣ_ : ℕ → Reward → Reward
_*ᵣ_ = _*_

zeroᵣ : Reward
zeroᵣ = 0

max : Reward → Reward → Reward
max m n with m ≤? n
... | yes _ = n
... | no  _ = m

bottom : Reward
bottom = 0

------------------------------------------------------------------------
-- Finiteness Requirements
------------------------------------------------------------------------

all-actions : List Action
all-actions = Flip ∷ Stay ∷ []

default-action : Action
default-action = Stay

horizon : ℕ
horizon = 3

------------------------------------------------------------------------
-- Import Stochastic EC
------------------------------------------------------------------------

open import CSHRL.EnvironmentClass.StochasticFiniteMDP

open StochasticFiniteMDP 
  State Action Reward step 
  _≤ᵣ_ ≤ᵣ-dec ≤ᵣ-refl max bottom 
  _+ᵣ_ _*ᵣ_ zeroᵣ 
  all-actions default-action horizon

------------------------------------------------------------------------
-- Expected Values (Manual Verification)
------------------------------------------------------------------------

-- From Ready state with Flip action:
-- E[immediate] = (1 * 1 + 0 * 1) / 2 = 0.5 (as rational)
-- In our unnormalized representation: weighted sum = 1, total weight = 2

-- From Ready state with Stay action:
-- E[immediate] = 0

-- So Flip has higher expected value than Stay from Ready state.

------------------------------------------------------------------------
-- Ranking Verification
------------------------------------------------------------------------

-- The expected trace for Flip should dominate Stay
-- This validates that our stochastic homomorphism correctly captures
-- the intuition that Flip is the better action from Ready.

-- Test: Compute expected traces at various depths
test-trace-flip-1 : List Reward
test-trace-flip-1 = expected-trace-action Ready Flip 1

test-trace-stay-1 : List Reward
test-trace-stay-1 = expected-trace-action Ready Stay 1

-- The ranking should put Flip above Stay from Ready
test-ranking : List Action
test-ranking = find-ranking Ready horizon

-- The policy should select Flip from Ready
test-policy : Action
test-policy = find-policy Ready horizon

------------------------------------------------------------------------
-- Notes on Verification
--
-- Full preservation proof requires showing:
-- 1. head-expected-≤: expected immediate reward respects ranking
-- 2. tail-expected-≤ₛ: expected continuation respects ranking
--
-- For this simple example, the proof is straightforward:
-- - From terminal states (Won, Lost), all actions are equivalent
-- - From Ready, Flip dominates Stay in expected value
--
-- The key insight is that the stochastic extension preserves the
-- CSHRL philosophy: rankings mirror expected stream dominance.
------------------------------------------------------------------------
