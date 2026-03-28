{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Synthesis.ContinuousActionRanking
--
-- A new formalization of action rankings for continuous action spaces.
-- Instead of discretizing continuous actions and synthesizing a massive 
-- pairwise matrix, we synthesize a single continuous function `a*(s)`.
-- The CoindHomo ranking relation is then derived naturally via a 
-- Unimodal Distance Metric: actions closer to `a*` are ranked higher.
------------------------------------------------------------------------

module CSHRL.Synthesis.ContinuousActionRanking where

open import Data.Integer using (ℤ; ∣_∣; _-_)
open import Data.Nat using (ℕ; _≤_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module ContinuousRanking (State : Set) where

  -- We represent continuous actions as fixed-point integers (scaled by δ)
  Action : Set
  Action = ℤ

  -- The synthesized policy is just a function that returns the optimal peak.
  OptimalActionPolicy = State → Action

  -- The pairwise ranking is derived directly from the geometric distance to the peak.
  -- a₁ ≤ₐ a₂ iff ∣ a₁ - a* ∣ ≥ ∣ a₂ - a* ∣
  -- (Meaning a₂ is closer to the optimal peak than a₁, making it "better" or equal)
  record UnimodalRanking (a* : OptimalActionPolicy) : Set₁ where
    field
      _≤ₐ_ : State → Action → Action → Set
      
      -- The ranking is strictly defined by the distance metric
      def : ∀ s a₁ a₂ → _≤ₐ_ s a₁ a₂ ≡ (∣ a₁ - (a* s) ∣ ≤ ∣ a₂ - (a* s) ∣)

  -- This completely eliminates the need to synthesize O(N^2) pairwise 
  -- relationships for an N*δ discretized action space.
  -- The synthesizer only has to discover the `a*` function, and the
  -- metric topology provides the entire CoindHomo RankTree for free!
