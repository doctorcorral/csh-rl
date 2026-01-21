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
-- - POSTULATE-FREE preservation via lexicographic ordering
--
-- KEY INSIGHT: Lexicographic coinductive comparison is the correct
-- notion for stochastic MDPs. The tail comparison is only required
-- when expected heads are equal, which correctly captures the
-- semantics of "earlier rewards break ties."
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
open import Codata.Guarded.Stream using (head; tail)

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
-- LEXICOGRAPHIC PRESERVATION PROOFS (Postulate-Free!)
------------------------------------------------------------------------

-- The key insight: lexicographic comparison has CONDITIONAL tail comparison.
-- When head(a) < head(b), we don't need to prove anything about tails!
-- This is exactly what makes the CoinFlip proof work without postulates.

-- Helper: 1 ≤ 0 is absurd (no constructor for suc n ≤ zero)
1≤0-absurd : 1 ≤ 0 → ∀ {A : Set} → A
1≤0-absurd ()

------------------------------------------------------------------------
-- Head Preservation
------------------------------------------------------------------------

-- For lexicographic ordering, we need:
-- s ranks a ≤ b → head(expected-action-value s a) ≤ᵣ head(expected-action-value s b)

coinflip-head-lex-≤ : ∀ s a b →
                      s ranks a ≤ b →
                      head (expected-action-value s a) ≤ᵣ head (expected-action-value s b)

-- Terminal states: both actions give 0 immediate reward
coinflip-head-lex-≤ Won Flip Flip _ = ≤ᵣ-refl
coinflip-head-lex-≤ Won Flip Stay p = proj₁ p
coinflip-head-lex-≤ Won Stay Flip p = proj₁ p
coinflip-head-lex-≤ Won Stay Stay _ = ≤ᵣ-refl
coinflip-head-lex-≤ Lost Flip Flip _ = ≤ᵣ-refl
coinflip-head-lex-≤ Lost Flip Stay p = proj₁ p
coinflip-head-lex-≤ Lost Stay Flip p = proj₁ p
coinflip-head-lex-≤ Lost Stay Stay _ = ≤ᵣ-refl

-- Ready state: the interesting case
coinflip-head-lex-≤ Ready Flip Flip _ = ≤ᵣ-refl
coinflip-head-lex-≤ Ready Stay Stay _ = ≤ᵣ-refl
coinflip-head-lex-≤ Ready Stay Flip _ = z≤n  -- 0 ≤ 1 ✓
coinflip-head-lex-≤ Ready Flip Stay (h≤ , _) = 1≤0-absurd h≤  -- 1 ≤ 0 is absurd

------------------------------------------------------------------------
-- Tail Preservation (Conditional!)
------------------------------------------------------------------------

-- For lexicographic ordering, tail preservation is CONDITIONAL:
-- s ranks a ≤ b → head(a) ≡ head(b) → tail(a) ≤ₛ-lex tail(b)
--
-- The crucial case Stay ≤ Flip at Ready:
-- - head(Stay) = 0, head(Flip) = 1
-- - The condition head(Stay) ≡ head(Flip) requires 0 ≡ 1, which is FALSE!
-- - Therefore, the tail proof obligation is TRIVIALLY satisfied.

coinflip-tail-lex-≤ : ∀ s a b →
                      s ranks a ≤ b →
                      head (expected-action-value s a) ≡ head (expected-action-value s b) →
                      tail (expected-action-value s a) ≤ₛ-lex tail (expected-action-value s b)

-- Terminal states: all actions give same stream, reflexivity
coinflip-tail-lex-≤ Won _ _ _ _ = ≤ₛ-lex-refl _
coinflip-tail-lex-≤ Lost _ _ _ _ = ≤ₛ-lex-refl _

-- Ready state with same action: reflexivity
coinflip-tail-lex-≤ Ready Flip Flip _ _ = ≤ₛ-lex-refl _
coinflip-tail-lex-≤ Ready Stay Stay _ _ = ≤ₛ-lex-refl _

-- Ready state, Stay ≤ Flip:
-- head(Stay) = 0, head(Flip) = 1
-- The condition 0 ≡ 1 is FALSE, so this case is impossible!
coinflip-tail-lex-≤ Ready Stay Flip _ ()

-- Ready state, Flip ≤ Stay:
-- This ranking is impossible (would require 1 ≤ 0 in the ranking hypothesis)
coinflip-tail-lex-≤ Ready Flip Stay (h≤ , _) _ = 1≤0-absurd h≤

------------------------------------------------------------------------
-- Verified CoindHomo Instance (Postulate-Free!)
------------------------------------------------------------------------

open WithLexPreservation coinflip-head-lex-≤ coinflip-tail-lex-≤ public

-- Now we have the verified instance:
-- StochasticMDPHomo : StochasticCoindHomo

------------------------------------------------------------------------
-- Tests that the instance works
------------------------------------------------------------------------

-- The policy from Ready should be Flip (higher expected value)
test-policy-is-flip : test-policy ≡ Flip
test-policy-is-flip = refl  -- Will typecheck if Flip is indeed selected
