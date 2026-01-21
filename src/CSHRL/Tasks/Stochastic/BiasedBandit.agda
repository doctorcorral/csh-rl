{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- BiasedBandit: A Two-Armed Bandit with Different Payoffs
--
-- A simple stateless bandit where the agent repeatedly chooses between
-- two arms with different success probabilities:
-- - Arm A: 2/3 chance of reward 1, 1/3 chance of reward 0
-- - Arm B: 1/3 chance of reward 1, 2/3 chance of reward 0
--
-- This is a STATELESS bandit: the state never changes, and the agent
-- just accumulates rewards over time. The optimal policy is always
-- to pull Arm A.
--
-- INTERESTING PROPERTY: Unlike CoinFlip/GamblersRuin/RandomWalk,
-- this example has NO terminal states. The agent plays forever.
-- Both arms give positive expected reward, but A is strictly better.
--
-- OPTIMAL POLICY: Always pull Arm A (expected reward 2 vs 1 per pull)
------------------------------------------------------------------------

module CSHRL.Tasks.Stochastic.BiasedBandit where

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

-- Single state: the agent just pulls arms forever
data State : Set where
  Playing : State

-- Actions: Pull arm A or arm B
data Action : Set where
  ArmA : Action   -- Better arm (2/3 success)
  ArmB : Action   -- Worse arm (1/3 success)

Reward : Set
Reward = ℕ

-- Stochastic step function
-- Arm A: 2/3 chance reward 1, 1/3 chance reward 0 (stay in Playing)
-- Arm B: 1/3 chance reward 1, 2/3 chance reward 0 (stay in Playing)
step : State → Action → Dist (State × Reward)
step Playing ArmA = bernoulli (Playing , 1) 2 (Playing , 0) 1   -- 2:1 odds
step Playing ArmB = bernoulli (Playing , 1) 1 (Playing , 0) 2   -- 1:2 odds

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
all-actions = ArmA ∷ ArmB ∷ []

default-action : Action
default-action = ArmB

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

-- Arm A: E[immediate] = (1 * 2 + 0 * 1) / 3 = 2/3
-- Unnormalized: weighted sum = 2, total weight = 3

-- Arm B: E[immediate] = (1 * 1 + 0 * 2) / 3 = 1/3
-- Unnormalized: weighted sum = 1, total weight = 3

-- Arm A has strictly higher expected immediate reward.
-- Since the state never changes, this dominance persists forever:
-- the expected stream for A is (2, 2, 2, ...) * scaling
-- the expected stream for B is (1, 1, 1, ...) * scaling

------------------------------------------------------------------------
-- Ranking Tests
------------------------------------------------------------------------

test-trace-armA : List Reward
test-trace-armA = expected-trace-action Playing ArmA 1

test-trace-armB : List Reward
test-trace-armB = expected-trace-action Playing ArmB 1

test-ranking : List Action
test-ranking = find-ranking Playing horizon

test-policy : Action
test-policy = find-policy Playing horizon

------------------------------------------------------------------------
-- LEXICOGRAPHIC PRESERVATION PROOFS
------------------------------------------------------------------------

-- Helper: 2 ≤ 1 is absurd
2≤1-absurd : 2 ≤ 1 → ∀ {A : Set} → A
2≤1-absurd (s≤s ())

-- Helper: 1 ≤ 2 is trivial
1≤2 : 1 ≤ 2
1≤2 = s≤s z≤n

------------------------------------------------------------------------
-- Head Preservation
------------------------------------------------------------------------

bandit-head-lex-≤ : ∀ s a b →
                    s ranks a ≤ b →
                    head (expected-action-value s a) ≤ᵣ head (expected-action-value s b)

-- Same arm: reflexivity
bandit-head-lex-≤ Playing ArmA ArmA _ = ≤ᵣ-refl
bandit-head-lex-≤ Playing ArmB ArmB _ = ≤ᵣ-refl

-- ArmB ≤ ArmA: expected 1 ≤ expected 2 ✓
bandit-head-lex-≤ Playing ArmB ArmA _ = 1≤2

-- ArmA ≤ ArmB: requires 2 ≤ 1 in ranking, which is absurd
bandit-head-lex-≤ Playing ArmA ArmB (h≤ , _) = 2≤1-absurd h≤

------------------------------------------------------------------------
-- Tail Preservation (Conditional)
------------------------------------------------------------------------

bandit-tail-lex-≤ : ∀ s a b →
                    s ranks a ≤ b →
                    head (expected-action-value s a) ≡ head (expected-action-value s b) →
                    tail (expected-action-value s a) ≤ₛ-lex tail (expected-action-value s b)

-- Same arm: reflexivity
bandit-tail-lex-≤ Playing ArmA ArmA _ _ = ≤ₛ-lex-refl _
bandit-tail-lex-≤ Playing ArmB ArmB _ _ = ≤ₛ-lex-refl _

-- ArmB ≤ ArmA: expected 1 ≡ expected 2 is absurd
bandit-tail-lex-≤ Playing ArmB ArmA _ ()

-- ArmA ≤ ArmB: impossible ranking (2 ≤ 1)
bandit-tail-lex-≤ Playing ArmA ArmB (h≤ , _) _ = 2≤1-absurd h≤

------------------------------------------------------------------------
-- Verified CoindHomo Instance
------------------------------------------------------------------------

open WithLexPreservation bandit-head-lex-≤ bandit-tail-lex-≤ public

------------------------------------------------------------------------
-- Policy Verification
------------------------------------------------------------------------

test-policy-is-armA : test-policy ≡ ArmA
test-policy-is-armA = refl

------------------------------------------------------------------------
-- Key Insight: Non-Terminal Stochastic MDPs
--
-- This example demonstrates that CSHRL's stochastic extension works
-- even for MDPs without terminal states. The bandit runs forever,
-- but the lexicographic preservation proof still works because:
--
-- 1. Arm A has strictly higher expected immediate reward (2 > 1)
-- 2. The conditional tail comparison requires 1 ≡ 2, which is absurd
-- 3. Therefore, no actual tail proof is needed
--
-- The infinite streams are:
-- - Arm A: (2, 2, 2, ...) in unnormalized expected values
-- - Arm B: (1, 1, 1, ...) in unnormalized expected values
--
-- Arm A pointwise dominates Arm B, and lexicographic dominance follows.
-- This is a case where both orderings (lex and pointwise) coincide.
------------------------------------------------------------------------
