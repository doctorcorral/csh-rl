{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- Pedagogical: Three equivalent formulations
--
-- 1. preserves-× : returns product (head ≤ᵣ head) × (tail ≤ₛ tail)
-- 2. Core.preserves : returns record _≤ₛ_
-- 3. optimality-η : unpacks (1) into (2)
--
-- All three are the same.
------------------------------------------------------------------------

module appendix.PreservationEquivalence where

open import Data.List using (List)
open import Codata.Guarded.Stream using (Stream; head; tail)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (proj₁; proj₂; _×_; _,_)

module _
  {State Action Reward : Set}
  {step : State → Action → State × Reward}
  {_≤ᵣ_ : Reward → Reward → Set}
  {max : Reward → Reward → Reward}
  {bottom : Reward}
  {all-actions : List Action}
  where

  open import CSHRL.Core
  open Core State Action Reward step _≤ᵣ_ max bottom all-actions

  ------------------------------------------------------------------------
  -- 1. Alternative preserves (product-based)
  --    Now uses propositions instead of Bool
  ------------------------------------------------------------------------

  preserves-× : (State → Action → Action → Set) → Set
  preserves-× _≤ₐ_ = ∀ a b s → _≤ₐ_ s a b →
                     let v₁ = action-value s a
                         v₂ = action-value s b
                     in head v₁ ≤ᵣ head v₂ × (tail v₁ ≤ₛ tail v₂)

  ------------------------------------------------------------------------
  -- 2. optimality-η: unpacks product into record
  ------------------------------------------------------------------------

  optimality-η : {_≤ₐ_ : State → Action → Action → Set} →
                 preserves-× _≤ₐ_ →
                 ∀ s other opt → _≤ₐ_ s other opt →
                 action-value s other ≤ₛ action-value s opt
  head≤ (optimality-η pres s other opt r) = proj₁ (pres other opt s r)
  tail≤ (optimality-η pres s other opt r) = proj₂ (pres other opt s r)

  ------------------------------------------------------------------------
  -- THE EQUIVALENCES
  ------------------------------------------------------------------------

  -- optimality-η unpacked = preserves-× (round-trip)
  optimality-η≡preserves-× : {_≤ₐ_ : State → Action → Action → Set}
                             (pres : preserves-× _≤ₐ_) →
                             ∀ s a b r →
                             let result = optimality-η pres s a b r
                             in (head≤ result , tail≤ result) ≡ pres a b s r
  optimality-η≡preserves-× _ _ _ _ _ = refl

  -- Core.preserves unpacked = preserves-× form
  Core-preserves≡preserves-× : (h : CoindHomo) → ∀ a b s r →
                               let p = CoindHomo.preserves h a b s r
                               in (head≤ p , tail≤ p) ≡
                                  (head≤ p , tail≤ p)  -- trivially equal
  Core-preserves≡preserves-× _ _ _ _ _ = refl

  -- Therefore: optimality-η ≡ Core.preserves (both unpack to same thing)
  all-three-equal : (h : CoindHomo) → ∀ s a b r →
                    let -- Build preserves-× from Core.preserves
                        pres-× : preserves-× (CoindHomo._≤ₐ_ h)
                        pres-× a' b' s' r' = let p = CoindHomo.preserves h a' b' s' r'
                                             in head≤ p , tail≤ p
                        -- Apply optimality-η to get back a record
                        via-η = optimality-η pres-× s a b r
                        -- Original Core.preserves
                        original = CoindHomo.preserves h a b s r
                    in (head≤ via-η ≡ head≤ original)
                     × (tail≤ via-η ≡ tail≤ original)
  all-three-equal _ _ _ _ _ = refl , refl
