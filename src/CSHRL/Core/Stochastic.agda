{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Core.Stochastic
--
-- Stochastic extension of CSHRL via finite distributions (Giry monad).
-- 
-- Key insight: The coinductive homomorphism property lifts through
-- probability distributions. If action a is ranked below action b,
-- then the EXPECTED reward stream from a is dominated by b's.
--
-- This module defines:
-- 1. Stochastic step functions
-- 2. Distributions over reward streams
-- 3. Expected stream dominance
-- 4. StochasticCoindHomo (the stochastic preservation property)
------------------------------------------------------------------------

module CSHRL.Core.Stochastic where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.List using (List; []; _∷_; map; foldr; concatMap)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Codata.Guarded.Stream using (Stream; head; tail; _∷_; tabulate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (_∘_; id)

-- Import the finite distribution monad
open import CSHRL.Probability.Finite using (Dist; pure; _>>=_; fmap; scale; total-weight)

------------------------------------------------------------------------
-- Stochastic Core Module
------------------------------------------------------------------------

module StochasticCore
  (State Action Reward : Set)
  
  -- Stochastic transition: returns a distribution over (State × Reward)
  (step : State → Action → Dist (State × Reward))
  
  -- Reward ordering
  (_≤ᵣ_ : Reward → Reward → Set)
  
  -- Reward arithmetic (required for expected values)
  (_+ᵣ_ : Reward → Reward → Reward)
  (_*ᵣ_ : ℕ → Reward → Reward)  -- Scalar multiplication by weight
  (zeroᵣ : Reward)
  
  -- Requirements for supremum calculation
  (max : Reward → Reward → Reward)
  (bottom : Reward)
  (all-actions : List Action)
  where

  ------------------------------------------------------------------------
  -- Basic Types
  ------------------------------------------------------------------------

  StreamR : Set
  StreamR = Stream Reward

  -- Distribution over reward streams
  DistStreamR : Set
  DistStreamR = Dist StreamR

  ------------------------------------------------------------------------
  -- Expected Value over Distributions
  ------------------------------------------------------------------------

  -- Weighted sum of rewards (unnormalized expected value)
  𝔼ᵣ : Dist Reward → Reward
  𝔼ᵣ = foldr (λ { (r , w) acc → (w *ᵣ r) +ᵣ acc }) zeroᵣ

  ------------------------------------------------------------------------
  -- Stochastic Value Functions
  ------------------------------------------------------------------------

  -- For stochastic environments, we compute expected values
  -- at each depth (Bellman expectation equation).

  -- Helper: max over a list of rewards
  max-list : List Reward → Reward
  max-list = foldr max bottom

  -- Extract expected immediate reward from a distribution
  expected-immediate : Dist (State × Reward) → Reward
  expected-immediate d = 𝔼ᵣ (fmap proj₂ d)

  -- Finite-horizon expected value (simplified version)
  -- Full treatment requires lifting through distributions at each step
  solve-expected : State → ℕ → Reward
  solve-expected s zero = 
    max-list (map (λ a → expected-immediate (step s a)) all-actions)
  solve-expected s (suc n) = 
    max-list (map (λ a → 
      𝔼ᵣ (fmap (λ { (s' , _) → solve-expected s' n }) (step s a))) 
      all-actions)

  -- Expected value stream: tabulate expected rewards at each depth
  expected-value : State → StreamR
  expected-value s = tabulate (solve-expected s)

  ------------------------------------------------------------------------
  -- Expected Action-Value
  ------------------------------------------------------------------------

  -- Expected action-value: do action a, then follow optimal expected policy
  -- Head: expected immediate reward from action a
  -- Tail: expected optimal value from successor states
  
  expected-action-value : State → Action → StreamR
  head (expected-action-value s a) = expected-immediate (step s a)
  tail (expected-action-value s a) = 
    -- Weighted average of successor values
    -- Simplified: take expected value from a "representative" successor
    -- Full version requires convolving the distribution
    tabulate (λ n → 𝔼ᵣ (fmap (λ { (s' , _) → solve-expected s' n }) (step s a)))

  ------------------------------------------------------------------------
  -- Expected Stream Dominance
  ------------------------------------------------------------------------

  -- Pointwise expected dominance: at every timestep,
  -- E[reward_a] ≤ E[reward_b]
  -- 
  -- This is the natural lifting of stream dominance to distributions.
  
  record _≤ₛ-expected_ (x y : StreamR) : Set where
    coinductive
    field
      head≤ : head x ≤ᵣ head y
      tail≤ : tail x ≤ₛ-expected tail y

  open _≤ₛ-expected_ public

  ------------------------------------------------------------------------
  -- Stochastic Coinductive Homomorphism
  ------------------------------------------------------------------------

  -- The key insight: rankings should preserve EXPECTED stream dominance.
  -- If action a is ranked below action b, then at every future timestep,
  -- the expected reward from a is dominated by b's expected reward.

  record StochasticCoindHomo : Set₁ where
    field
      -- The ranking relation (same as deterministic case)
      _≤ₐ_ : State → Action → Action → Set

      -- Preservation: ranking mirrors expected stream dominance
      preserves : ∀ a b s → _≤ₐ_ s a b →
                  expected-action-value s a ≤ₛ-expected expected-action-value s b

  open StochasticCoindHomo public

  ------------------------------------------------------------------------
  -- Relationship to Deterministic Core
  ------------------------------------------------------------------------

  -- Key theorem (sketch): If the stochastic step is deterministic
  -- (i.e., returns singleton distributions), then StochasticCoindHomo
  -- reduces exactly to the deterministic CoindHomo.
  --
  -- This justifies the stochastic extension as a proper generalization.

  -- Helper: check if a distribution is deterministic
  is-deterministic : ∀ {A} → Dist A → Set
  is-deterministic d = foldr (λ _ acc → suc acc) 0 d ≡ 1

  ------------------------------------------------------------------------
  -- Stochastic Dominance (Alternative - Stronger Condition)
  ------------------------------------------------------------------------

  -- First-order stochastic dominance: for all thresholds t,
  -- P(X ≥ t) ≤ P(Y ≥ t)
  --
  -- This is stronger than expected dominance and requires more infrastructure.
  -- We state the type signature for future implementation.

  -- StochasticDominance : Dist Reward → Dist Reward → Set
  -- StochasticDominance d₁ d₂ = ∀ threshold → P(d₁ ≥ threshold) ≤ P(d₂ ≥ threshold)

  -- For finite distributions, this is decidable given:
  -- - Decidable equality on rewards
  -- - Total ordering on rewards
  -- - Enumeration of all possible reward values
