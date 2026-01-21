{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- RandomWalk: A 1D Stochastic Random Walk
--
-- A simple random walk on three positions: Left, Center, Right.
-- The agent starts at Center and can WALK or STAY:
-- - WALK: 50% step left, 50% step right
-- - STAY: remain in current position
--
-- Terminal states: Left (fail, reward 0) or Right (goal, reward 1)
--
-- This differs from CoinFlip/GamblersRuin in that:
-- - The walk can go either direction from Center
-- - There's genuine uncertainty about which terminal state is reached
--
-- OPTIMAL POLICY: Walk (gives 50% chance of reaching goal vs 0% for Stay)
------------------------------------------------------------------------

module CSHRL.Tasks.Stochastic.RandomWalk where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; _≤?_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Codata.Guarded.Stream using (head; tail)

open import CSHRL.Probability.Finite using (Dist; pure; _>>=_; fmap; bernoulli)

------------------------------------------------------------------------
-- MDP Definition
------------------------------------------------------------------------

-- States: Three positions on a line
data State : Set where
  Left   : State   -- Terminal (fail)
  Center : State   -- Starting position
  Right  : State   -- Terminal (goal)

-- Actions: Walk or Stay
data Action : Set where
  Walk : Action   -- Take a random step
  Stay : Action   -- Remain in place

Reward : Set
Reward = ℕ

-- Stochastic step function
-- WALK from Center: 50% → Left (reward 0), 50% → Right (reward 1)
-- STAY from Center: 100% → Center (reward 0)
-- From terminals: stay with reward 0
step : State → Action → Dist (State × Reward)
step Center Walk = bernoulli (Right , 1) 1 (Left , 0) 1   -- Fair coin
step Center Stay = pure (Center , 0)                       -- Stay put
step Left   _    = pure (Left , 0)                         -- Terminal
step Right  _    = pure (Right , 0)                        -- Terminal

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
all-actions = Walk ∷ Stay ∷ []

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
-- Expected Values Analysis
------------------------------------------------------------------------

-- From Center with Walk:
-- E[immediate] = (1 * 1 + 0 * 1) / 2 = 0.5 (unnormalized: 1, weight 2)

-- From Center with Stay:
-- E[immediate] = 0

-- Walk dominates Stay in expected immediate reward.

------------------------------------------------------------------------
-- Ranking Tests
------------------------------------------------------------------------

test-trace-walk : List Reward
test-trace-walk = expected-trace-action Center Walk 1

test-trace-stay : List Reward
test-trace-stay = expected-trace-action Center Stay 1

test-ranking : List Action
test-ranking = find-ranking Center horizon

test-policy : Action
test-policy = find-policy Center horizon

------------------------------------------------------------------------
-- LEXICOGRAPHIC PRESERVATION PROOFS
------------------------------------------------------------------------

1≤0-absurd : 1 ≤ 0 → ∀ {A : Set} → A
1≤0-absurd ()

------------------------------------------------------------------------
-- Head Preservation
------------------------------------------------------------------------

walk-head-lex-≤ : ∀ s a b →
                  s ranks a ≤ b →
                  head (expected-action-value s a) ≤ᵣ head (expected-action-value s b)

-- Terminal states
walk-head-lex-≤ Left Walk Walk _ = ≤ᵣ-refl
walk-head-lex-≤ Left Walk Stay p = proj₁ p
walk-head-lex-≤ Left Stay Walk p = proj₁ p
walk-head-lex-≤ Left Stay Stay _ = ≤ᵣ-refl
walk-head-lex-≤ Right Walk Walk _ = ≤ᵣ-refl
walk-head-lex-≤ Right Walk Stay p = proj₁ p
walk-head-lex-≤ Right Stay Walk p = proj₁ p
walk-head-lex-≤ Right Stay Stay _ = ≤ᵣ-refl

-- Center state
walk-head-lex-≤ Center Walk Walk _ = ≤ᵣ-refl
walk-head-lex-≤ Center Stay Stay _ = ≤ᵣ-refl
walk-head-lex-≤ Center Stay Walk _ = z≤n  -- 0 ≤ 1
walk-head-lex-≤ Center Walk Stay (h≤ , _) = 1≤0-absurd h≤

------------------------------------------------------------------------
-- Tail Preservation (Conditional)
------------------------------------------------------------------------

walk-tail-lex-≤ : ∀ s a b →
                  s ranks a ≤ b →
                  head (expected-action-value s a) ≡ head (expected-action-value s b) →
                  tail (expected-action-value s a) ≤ₛ-lex tail (expected-action-value s b)

-- Terminal states: reflexivity
walk-tail-lex-≤ Left _ _ _ _ = ≤ₛ-lex-refl _
walk-tail-lex-≤ Right _ _ _ _ = ≤ₛ-lex-refl _

-- Center with same action
walk-tail-lex-≤ Center Walk Walk _ _ = ≤ₛ-lex-refl _
walk-tail-lex-≤ Center Stay Stay _ _ = ≤ₛ-lex-refl _

-- Center, Stay ≤ Walk: 0 ≡ 1 absurd
walk-tail-lex-≤ Center Stay Walk _ ()

-- Center, Walk ≤ Stay: impossible ranking
walk-tail-lex-≤ Center Walk Stay (h≤ , _) _ = 1≤0-absurd h≤

------------------------------------------------------------------------
-- Verified CoindHomo Instance
------------------------------------------------------------------------

open WithLexPreservation walk-head-lex-≤ walk-tail-lex-≤ public

------------------------------------------------------------------------
-- Policy Verification
------------------------------------------------------------------------

test-policy-is-walk : test-policy ≡ Walk
test-policy-is-walk = refl

------------------------------------------------------------------------
-- Interpretation
--
-- The random walk is structurally identical to CoinFlip and GamblersRuin
-- for CSHRL's purposes: the key property is that one action (Walk/Flip/Bet)
-- gives positive expected immediate reward while the other (Stay/Quit)
-- gives zero.
--
-- The lexicographic preservation works the same way:
-- - Stay ≤ Walk requires comparing tails only when 0 ≡ 1 (absurd)
-- - Walk ≤ Stay is impossible (would need 1 ≤ 0 in ranking)
--
-- This pattern generalizes: any MDP where one action strictly dominates
-- in expected immediate reward will have a trivial lexicographic proof.
------------------------------------------------------------------------
