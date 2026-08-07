{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Probability.Compose
--
-- Compositional Algebra for Stochastic Dominance.
--
-- Proves that FOSD and k-th order SD are closed under natural
-- composition operations on finite distributions:
--
--   1. Concatenation (++): mixture of independent distributions
--   2. Scaling (scale k): reward amplification by factor k
--
-- The closure properties lift to the full SD hierarchy via
-- distributivity lemmas for prefix-sum and sd-weight.
--
-- Key structural insight: prefix-sum is a *linear* operator.
-- It distributes over addition (prefix-sum-+) and scalar
-- multiplication (prefix-sum-*).  Since sd-weight is iterated
-- prefix-sum, it inherits linearity:
--   sd-weight k (d₁ ++ d₂) = sd-weight k d₁ + sd-weight k d₂
--   sd-weight k (scale c d) = c * sd-weight k d
--
-- These algebraic properties are the foundation for compositional
-- environment verification: verified rankings on components
-- automatically compose into verified rankings on composites.
--
-- All --safe, no postulates.
------------------------------------------------------------------------

module CSHRL.Probability.Compose where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-refl; +-mono-≤; +-assoc; +-comm;
         *-distribˡ-+; *-monoʳ-≤)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)

open import CSHRL.Probability.Finite using (Dist; scale)
open import CSHRL.Probability.FOSD
  using (cdf-weight; _FOSD≤_; cdf-weight-++; cdf-weight-scale)
open import CSHRL.Probability.SD
  using (sd-weight; _SD[_]≤_; prefix-sum)

------------------------------------------------------------------------
-- Prefix-Sum Extensionality
--
-- If f ≡ g pointwise, then prefix-sum f ≡ prefix-sum g.
------------------------------------------------------------------------

prefix-sum-ext : ∀ {f g : ℕ → ℕ} →
  (∀ r → f r ≡ g r) →
  ∀ r → prefix-sum f r ≡ prefix-sum g r
prefix-sum-ext eq zero    = eq 0
prefix-sum-ext eq (suc r) = cong₂ _+_ (eq (suc r)) (prefix-sum-ext eq r)

------------------------------------------------------------------------
-- Prefix-Sum Linearity: Addition
--
-- prefix-sum (λ r → f r + g r) r ≡ prefix-sum f r + prefix-sum g r
------------------------------------------------------------------------

private
  +-rearrange : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
  +-rearrange a b c d =
    trans (+-assoc a b (c + d))
    (trans (cong (a +_) (sym (+-assoc b c d)))
    (trans (cong (a +_) (cong (_+ d) (+-comm b c)))
    (trans (cong (a +_) (+-assoc c b d))
           (sym (+-assoc a c (b + d))))))

prefix-sum-+ : ∀ (f g : ℕ → ℕ) r →
  prefix-sum (λ r → f r + g r) r ≡ prefix-sum f r + prefix-sum g r
prefix-sum-+ f g zero    = refl
prefix-sum-+ f g (suc r) =
  trans (cong ((f (suc r) + g (suc r)) +_) (prefix-sum-+ f g r))
        (+-rearrange (f (suc r)) (g (suc r)) (prefix-sum f r) (prefix-sum g r))

------------------------------------------------------------------------
-- Prefix-Sum Linearity: Scalar Multiplication
--
-- prefix-sum (λ r → c * f r) r ≡ c * prefix-sum f r
------------------------------------------------------------------------

prefix-sum-* : ∀ c (f : ℕ → ℕ) r →
  prefix-sum (λ r → c * f r) r ≡ c * prefix-sum f r
prefix-sum-* c f zero    = refl
prefix-sum-* c f (suc r) =
  trans (cong (c * f (suc r) +_) (prefix-sum-* c f r))
        (sym (*-distribˡ-+ c (f (suc r)) (prefix-sum f r)))

------------------------------------------------------------------------
-- sd-weight Distributes over Concatenation (++)
--
-- sd-weight k (d₁ ++ d₂) r ≡ sd-weight k d₁ r + sd-weight k d₂ r
--
-- Proof: induction on k.
-- Base: cdf-weight-++ (from Probability.FOSD).
-- Step: prefix-sum-ext (IH) then prefix-sum-+ (linearity).
------------------------------------------------------------------------

sd-weight-++ : ∀ k (d₁ d₂ : Dist ℕ) r →
  sd-weight k (d₁ ++ d₂) r ≡ sd-weight k d₁ r + sd-weight k d₂ r
sd-weight-++ zero    d₁ d₂ r = cdf-weight-++ d₁ d₂ r
sd-weight-++ (suc k) d₁ d₂ r =
  trans (prefix-sum-ext (sd-weight-++ k d₁ d₂) r)
        (prefix-sum-+ (sd-weight k d₁) (sd-weight k d₂) r)

------------------------------------------------------------------------
-- sd-weight Distributes over Scaling
--
-- sd-weight k (scale c d) r ≡ c * sd-weight k d r
--
-- Proof: induction on k.
-- Base: cdf-weight-scale (from Probability.FOSD).
-- Step: prefix-sum-ext (IH) then prefix-sum-* (linearity).
------------------------------------------------------------------------

sd-weight-scale : ∀ k (d : Dist ℕ) r c →
  sd-weight k (scale c d) r ≡ c * sd-weight k d r
sd-weight-scale zero    d r c = cdf-weight-scale d r c
sd-weight-scale (suc k) d r c =
  trans (prefix-sum-ext (λ t → sd-weight-scale k d t c) r)
        (prefix-sum-* c (sd-weight k d) r)

------------------------------------------------------------------------
-- FOSD Closed under Concatenation
--
-- If μ₁ FOSD≤ ν₁ and μ₂ FOSD≤ ν₂,
-- then (μ₁ ++ μ₂) FOSD≤ (ν₁ ++ ν₂).
--
-- Mixture of dominated distributions is dominated.
------------------------------------------------------------------------

FOSD-++ : ∀ {μ₁ ν₁ μ₂ ν₂ : Dist ℕ} →
  μ₁ FOSD≤ ν₁ → μ₂ FOSD≤ ν₂ →
  (μ₁ ++ μ₂) FOSD≤ (ν₁ ++ ν₂)
FOSD-++ {μ₁} {ν₁} {μ₂} {ν₂} f1 f2 r
  rewrite cdf-weight-++ ν₁ ν₂ r | cdf-weight-++ μ₁ μ₂ r
  = +-mono-≤ (f1 r) (f2 r)

------------------------------------------------------------------------
-- FOSD Closed under Scaling
--
-- If μ FOSD≤ ν, then scale k μ FOSD≤ scale k ν.
--
-- Amplifying rewards preserves dominance.
------------------------------------------------------------------------

FOSD-scale : ∀ k {μ ν : Dist ℕ} →
  μ FOSD≤ ν → scale k μ FOSD≤ scale k ν
FOSD-scale k {μ} {ν} fosd r
  rewrite cdf-weight-scale ν r k | cdf-weight-scale μ r k
  = *-monoʳ-≤ k (fosd r)

------------------------------------------------------------------------
-- SD[k] Closed under Concatenation
--
-- If μ₁ SD[k]≤ ν₁ and μ₂ SD[k]≤ ν₂,
-- then (μ₁ ++ μ₂) SD[k]≤ (ν₁ ++ ν₂).
--
-- The hierarchy is preserved under mixture at every order.
------------------------------------------------------------------------

SD-++ : ∀ k {μ₁ ν₁ μ₂ ν₂ : Dist ℕ} →
  μ₁ SD[ k ]≤ ν₁ → μ₂ SD[ k ]≤ ν₂ →
  (μ₁ ++ μ₂) SD[ k ]≤ (ν₁ ++ ν₂)
SD-++ k {μ₁} {ν₁} {μ₂} {ν₂} f1 f2 r
  rewrite sd-weight-++ k ν₁ ν₂ r | sd-weight-++ k μ₁ μ₂ r
  = +-mono-≤ (f1 r) (f2 r)

------------------------------------------------------------------------
-- SD[k] Closed under Scaling
--
-- If μ SD[k]≤ ν, then scale c μ SD[k]≤ scale c ν.
--
-- The hierarchy is preserved under reward amplification.
------------------------------------------------------------------------

SD-scale : ∀ k c {μ ν : Dist ℕ} →
  μ SD[ k ]≤ ν → scale c μ SD[ k ]≤ scale c ν
SD-scale k c {μ} {ν} sd r
  rewrite sd-weight-scale k ν r c | sd-weight-scale k μ r c
  = *-monoʳ-≤ c (sd r)
