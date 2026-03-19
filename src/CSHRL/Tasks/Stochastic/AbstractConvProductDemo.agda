{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Stochastic.AbstractConvProductDemo
--
-- Demonstrates abstract-conv-product: the full pipeline
--   abstraction + convolution + lifting
--
-- Two independent Regional Policy environments (each: ℕ states,
-- abstracted to Bool, Invest|Conserve).  The product has state ℕ × ℕ
-- and action (Invest|Conserve) × (Invest|Conserve).  Rewards combine
-- by convolution (independent sum).
--
-- The demo:
--   1. Uses density-abstraction for both components (from AbstractionDemo)
--   2. Verifies FOSD rankings on each 2-state abstract system
--   3. Composes via conv-product (convolution of marginals)
--   4. Lifts to the full (ℕ × ℕ) concrete product via abstract-lift
--
-- Result: a VerifiedRanking on an infinite product state space,
-- verified by checking only 2 × 2 = 4 abstract state pairs.
--
-- All --safe, no postulates.
------------------------------------------------------------------------

module CSHRL.Tasks.Stochastic.AbstractConvProductDemo where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym)

open import CSHRL.Core.Compose using (VerifiedRanking)
open import CSHRL.Core.Abstraction using (StateAbstraction; abstract-conv-product)
open import CSHRL.Probability.Finite using (total-weight)
open import CSHRL.Probability.Convolution using (conv)

import CSHRL.Tasks.Stochastic.AbstractionDemo as RP

------------------------------------------------------------------------
-- Total-weight equality for Regional Policy marginals
--
-- All marginals have total weight 2; the convolution FOSD theorem
-- requires this for the first component when comparing actions.
------------------------------------------------------------------------

private
  tw≡2 : ∀ (s : Bool) (a : RP.Action) n →
    total-weight (RP.marginal (StateAbstraction.embed RP.density-abstraction s) a n) ≡ 2
  tw≡2 false RP.Invest   n = refl
  tw≡2 false RP.Conserve n = refl
  tw≡2 true  RP.Invest   n = refl
  tw≡2 true  RP.Conserve n = refl

total-weight-eq : ∀ s a b n →
  total-weight (RP.marginal (StateAbstraction.embed RP.density-abstraction s) a n) ≡
  total-weight (RP.marginal (StateAbstraction.embed RP.density-abstraction s) b n)
total-weight-eq s a b n = trans (tw≡2 s a n) (sym (tw≡2 s b n))

------------------------------------------------------------------------
-- Product ranking: Regional Policy × Regional Policy
--
-- abstract-conv-product composes:
--   - Two abstractions (both density-abstraction)
--   - Two invariance proofs (marginal-invariant)
--   - Total-weight equality
--   - Two abstract VerifiedRankings
--
-- State  = ℕ × ℕ  (infinite)
-- Action = (Invest|Conserve) × (Invest|Conserve)
-- Marginal = conv (m₁ s₁ a₁ n) (m₂ s₂ a₂ n)
------------------------------------------------------------------------

product-ranking : VerifiedRanking (ℕ × ℕ) (RP.Action × RP.Action)
  (λ { (s₁ , s₂) (a₁ , a₂) n →
    conv (RP.marginal s₁ a₁ n) (RP.marginal s₂ a₂ n) }) 0
product-ranking =
  abstract-conv-product
    RP.density-abstraction RP.density-abstraction
    RP.marginal-invariant RP.marginal-invariant
    total-weight-eq
    RP.abstract-ranking RP.abstract-ranking

------------------------------------------------------------------------
-- Spot checks: product ordering at various (ℕ × ℕ) states
--
-- (Conserve, Conserve) ≤ (Invest, Invest) when both regions prefer Invest
-- (Invest, Invest) ≤ (Conserve, Conserve) when both regions prefer Conserve
------------------------------------------------------------------------

open VerifiedRanking product-ranking

check-sparse-sparse : _≤ₐ_ (0 , 3) (RP.Conserve , RP.Conserve) (RP.Invest , RP.Invest)
check-sparse-sparse = tt , tt

check-dense-dense : _≤ₐ_ (10 , 100) (RP.Invest , RP.Invest) (RP.Conserve , RP.Conserve)
check-dense-dense = tt , tt

check-mixed : _≤ₐ_ (0 , 10) (RP.Conserve , RP.Invest) (RP.Invest , RP.Conserve)
check-mixed = tt , tt
