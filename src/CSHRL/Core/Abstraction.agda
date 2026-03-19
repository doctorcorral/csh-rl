{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Core.Abstraction
--
-- State Abstraction for Verified Rankings.
--
-- The central theorem: verify a ranking on a *finite abstract* system,
-- automatically obtain a ranking on the *full concrete* system---even
-- when the concrete state space is infinite or continuous.
--
-- A StateAbstraction bundles:
--   • project : Concrete → Abstract  (collapse states)
--   • embed   : Abstract → Concrete  (choose representatives)
--   • section : project ∘ embed = id (representatives are consistent)
--
-- The key assumption is *marginal-invariance*: states in the same
-- abstract class have identical marginal reward distributions.
-- Under this condition, abstract-lift transfers any VerifiedRanking
-- from the abstract system to the concrete one.
--
-- This subsumes feature-based abstraction (AllFeatAgree) as a
-- special case where project = feature-vector.
--
-- Composition: product-abstraction lets you abstract two independent
-- components separately, then compose the abstractions.
--
-- All --safe, no postulates.
------------------------------------------------------------------------

module CSHRL.Core.Abstraction where

open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; subst)

open import CSHRL.Probability.Finite using (Dist)
open import CSHRL.Probability.SD using (_SD[_]≤_)
open import CSHRL.Core.Compose using (VerifiedRanking)

------------------------------------------------------------------------
-- State Abstraction
--
-- project collapses concrete states to abstract states.
-- embed picks a representative concrete state for each abstract state.
-- section ensures consistency: project (embed a) ≡ a.
------------------------------------------------------------------------

record StateAbstraction (Concrete Abstract : Set) : Set where
  field
    project : Concrete → Abstract
    embed   : Abstract → Concrete
    section : ∀ a → project (embed a) ≡ a

open StateAbstraction

------------------------------------------------------------------------
-- The Lifting Theorem
--
-- Given:
--   • A state abstraction (Concrete → Abstract)
--   • Marginal-invariance: same abstract class ⟹ same marginal
--   • A VerifiedRanking on the abstract system
--
-- Produces a VerifiedRanking on the full concrete system.
--
-- The concrete ordering is: a ≤ₛ b  iff  a ≤_{project(s)} b
-- in the abstract system.  Preservation transfers via
-- marginal-invariance.
------------------------------------------------------------------------

abstract-lift :
  ∀ {Concrete Abstract Action : Set}
    {m : Concrete → Action → ℕ → Dist ℕ}
    {k : ℕ} →
  (abs : StateAbstraction Concrete Abstract) →
  (invariant : ∀ c₁ c₂ → project abs c₁ ≡ project abs c₂ →
    ∀ a n → m c₁ a n ≡ m c₂ a n) →
  VerifiedRanking Abstract Action (λ as a n → m (embed abs as) a n) k →
  VerifiedRanking Concrete Action m k
abstract-lift {_} {_} {_} {m} {k} abs invariant vr = record
  { _≤ₐ_ = λ s a b → VerifiedRanking._≤ₐ_ vr (project abs s) a b
  ; preserves = λ a b s p n →
      let eq : project abs s ≡ project abs (embed abs (project abs s))
          eq = sym (section abs (project abs s))
          eq-a = invariant s (embed abs (project abs s)) eq a n
          eq-b = invariant s (embed abs (project abs s)) eq b n
          abs-pf = VerifiedRanking.preserves vr a b (project abs s) p n
      in subst (m s a n SD[ k ]≤_) (sym eq-b)
           (subst (_SD[ k ]≤ m (embed abs (project abs s)) b n) (sym eq-a)
             abs-pf)
  }

------------------------------------------------------------------------
-- Identity Abstraction
--
-- When abstract = concrete, the lifting is trivial.
------------------------------------------------------------------------

id-abstraction : ∀ {S : Set} → StateAbstraction S S
id-abstraction = record
  { project = λ s → s
  ; embed   = λ s → s
  ; section = λ _ → refl
  }

------------------------------------------------------------------------
-- Product Abstraction
--
-- Two independent abstractions compose component-wise.
-- This enables modular abstraction of product environments:
-- abstract each component separately, then combine.
------------------------------------------------------------------------

product-abstraction :
  ∀ {C₁ A₁ C₂ A₂ : Set} →
  StateAbstraction C₁ A₁ → StateAbstraction C₂ A₂ →
  StateAbstraction (C₁ × C₂) (A₁ × A₂)
product-abstraction abs₁ abs₂ = record
  { project = λ { (c₁ , c₂) → project abs₁ c₁ , project abs₂ c₂ }
  ; embed   = λ { (a₁ , a₂) → embed abs₁ a₁ , embed abs₂ a₂ }
  ; section = λ { (a₁ , a₂) →
      cong₂ _,_ (section abs₁ a₁) (section abs₂ a₂) }
  }

------------------------------------------------------------------------
-- Composed Abstraction
--
-- Two-level abstraction: Concrete → Mid → Abstract.
-- If you can abstract in two stages, you can abstract in one.
------------------------------------------------------------------------

compose-abstraction :
  ∀ {C M A : Set} →
  StateAbstraction C M → StateAbstraction M A →
  StateAbstraction C A
compose-abstraction abs₁ abs₂ = record
  { project = λ c → project abs₂ (project abs₁ c)
  ; embed   = λ a → embed abs₁ (embed abs₂ a)
  ; section = λ a →
      subst (λ x → project abs₂ x ≡ a)
        (sym (section abs₁ (embed abs₂ a)))
        (section abs₂ a)
  }

------------------------------------------------------------------------
-- Abstraction-Aware Convolution Product
--
-- Combine abstract-lift with conv-product: abstract two components
-- independently, verify FOSD rankings on abstract systems, then
-- lift the convolution product to the full concrete system.
--
-- This is the composition pattern for continuous-state product MDPs
-- with additive rewards:
--   1. Abstract each component's state space (potentially infinite)
--   2. Verify FOSD ranking on each finite abstract component
--   3. conv-product composes the abstract rankings
--   4. abstract-lift on the product abstraction yields the concrete ranking
------------------------------------------------------------------------

open import CSHRL.Probability.FOSD using (_FOSD≤_)
open import CSHRL.Probability.Finite using (total-weight)
open import CSHRL.Probability.Convolution using (conv; FOSD→SD-conv)

abstract-conv-product :
  ∀ {C₁ A₁ C₂ A₂ Act₁ Act₂ : Set}
    {m₁ : C₁ → Act₁ → ℕ → Dist ℕ}
    {m₂ : C₂ → Act₂ → ℕ → Dist ℕ}
    {k : ℕ} →
  (abs₁ : StateAbstraction C₁ A₁) →
  (abs₂ : StateAbstraction C₂ A₂) →
  (inv₁ : ∀ c₁ c₁' → project abs₁ c₁ ≡ project abs₁ c₁' →
    ∀ a n → m₁ c₁ a n ≡ m₁ c₁' a n) →
  (inv₂ : ∀ c₂ c₂' → project abs₂ c₂ ≡ project abs₂ c₂' →
    ∀ a n → m₂ c₂ a n ≡ m₂ c₂' a n) →
  (tw : ∀ s a b n → total-weight (m₁ (embed abs₁ s) a n) ≡
                     total-weight (m₁ (embed abs₁ s) b n)) →
  VerifiedRanking A₁ Act₁ (λ s a n → m₁ (embed abs₁ s) a n) 0 →
  VerifiedRanking A₂ Act₂ (λ s a n → m₂ (embed abs₂ s) a n) 0 →
  VerifiedRanking (C₁ × C₂) (Act₁ × Act₂)
    (λ { (s₁ , s₂) (a₁ , a₂) n →
      conv (m₁ s₁ a₁ n) (m₂ s₂ a₂ n) }) k
abstract-conv-product {C₁} {A₁} {C₂} {A₂} {Act₁} {Act₂} {m₁} {m₂} {k}
  abs₁ abs₂ inv₁ inv₂ tw vr₁ vr₂ =
  abstract-lift (product-abstraction abs₁ abs₂) inv-prod abs-conv
  where
    open import CSHRL.Core.Compose using (conv-product)
    open import Data.Product using (proj₁; proj₂)

    abs-conv : VerifiedRanking (A₁ × A₂) (Act₁ × Act₂)
      (λ { (s₁ , s₂) (a₁ , a₂) n →
        conv (m₁ (embed abs₁ s₁) a₁ n) (m₂ (embed abs₂ s₂) a₂ n) }) k
    abs-conv = conv-product tw vr₁ vr₂

    inv-prod : ∀ c₁ c₂ →
      (project abs₁ (proj₁ c₁) , project abs₂ (proj₂ c₁)) ≡
      (project abs₁ (proj₁ c₂) , project abs₂ (proj₂ c₂)) →
      ∀ act n →
      conv (m₁ (proj₁ c₁) (proj₁ act) n)
           (m₂ (proj₂ c₁) (proj₂ act) n) ≡
      conv (m₁ (proj₁ c₂) (proj₁ act) n)
           (m₂ (proj₂ c₂) (proj₂ act) n)
    inv-prod (c₁₁ , c₁₂) (c₂₁ , c₂₂) eq (a₁ , a₂) n
      with cong proj₁ eq | cong proj₂ eq
    ... | eq₁ | eq₂ = cong₂ conv (inv₁ c₁₁ c₂₁ eq₁ a₁ n)
                                  (inv₂ c₁₂ c₂₂ eq₂ a₂ n)
