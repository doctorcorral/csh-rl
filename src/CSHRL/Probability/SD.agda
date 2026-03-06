{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Probability.SD
--
-- The Stochastic Dominance Hierarchy for finite distributions.
--
-- Generalizes FOSD to k-th order stochastic dominance via iterated
-- prefix sums of the CDF.
--
-- SD-order 0 = FOSD (all monotone utility functions)
-- SD-order 1 = SOSD (all concave monotone = risk-averse)
-- SD-order 2 = TOSD (all utilities with non-increasing absolute
--                     risk aversion = "prudent" agents)
-- SD-order k = (k+1)-th order SD
--
-- Key results:
--   1. SD[k] ⟹ SD[k+1] (hierarchy subsumption via prefix-sum mono)
--   2. SD[k] ⟹ EV dominance (for 0/1 dists with equal total weights)
--   3. Preorder properties at every level
--
-- All --safe, no postulates.
------------------------------------------------------------------------

module CSHRL.Probability.SD where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _≤?_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; +-mono-≤)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong)

open import CSHRL.Probability.Finite using (Dist; total-weight; weighted-sum)
open import CSHRL.Probability.FOSD
  using (cdf-weight; _FOSD≤_; FOSD-refl; FOSD-trans;
         AllBelow; fosd→ev;
         armA; armB; bandit-fosd)

------------------------------------------------------------------------
-- Prefix Sum
------------------------------------------------------------------------

prefix-sum : (ℕ → ℕ) → ℕ → ℕ
prefix-sum f zero    = f 0
prefix-sum f (suc r) = f (suc r) + prefix-sum f r

------------------------------------------------------------------------
-- k-th Order Integrated CDF
--
-- sd-weight 0 d r = cdf-weight d r          (CDF: FOSD level)
-- sd-weight 1 d r = prefix-sum (cdf d) r    (integrated CDF: SOSD)
-- sd-weight k d r = k-fold prefix sum of CDF
------------------------------------------------------------------------

sd-weight : ℕ → Dist ℕ → ℕ → ℕ
sd-weight zero    d = cdf-weight d
sd-weight (suc k) d = prefix-sum (sd-weight k d)

------------------------------------------------------------------------
-- Stochastic Dominance Ordering (k-th order)
--
-- μ SD[ k ]≤ ν means: ν dominates μ in (k+1)-th order SD.
-- Equivalently: every agent whose utility function class corresponds
-- to order (k+1) prefers ν over μ.
------------------------------------------------------------------------

_SD[_]≤_ : Dist ℕ → ℕ → Dist ℕ → Set
μ SD[ k ]≤ ν = ∀ r → sd-weight k ν r ≤ sd-weight k μ r

_SOSD≤_ : Dist ℕ → Dist ℕ → Set
μ SOSD≤ ν = μ SD[ 1 ]≤ ν

_TOSD≤_ : Dist ℕ → Dist ℕ → Set
μ TOSD≤ ν = μ SD[ 2 ]≤ ν

------------------------------------------------------------------------
-- SD[0] ≡ FOSD (definitional equality)
------------------------------------------------------------------------

SD-0→FOSD : ∀ {μ ν} → μ SD[ 0 ]≤ ν → μ FOSD≤ ν
SD-0→FOSD sd = sd

FOSD→SD-0 : ∀ {μ ν} → μ FOSD≤ ν → μ SD[ 0 ]≤ ν
FOSD→SD-0 fosd = fosd

------------------------------------------------------------------------
-- Preorder Properties
------------------------------------------------------------------------

SD-refl : ∀ k (d : Dist ℕ) → d SD[ k ]≤ d
SD-refl k d r = ≤-refl

SD-trans : ∀ {k} {a b c : Dist ℕ} →
  a SD[ k ]≤ b → b SD[ k ]≤ c → a SD[ k ]≤ c
SD-trans ab bc r = ≤-trans (bc r) (ab r)

------------------------------------------------------------------------
-- Prefix Sum Monotonicity
--
-- If f r ≤ g r for all r, then prefix-sum f r ≤ prefix-sum g r.
------------------------------------------------------------------------

prefix-sum-mono : ∀ {f g : ℕ → ℕ} →
  (∀ r → f r ≤ g r) →
  ∀ r → prefix-sum f r ≤ prefix-sum g r
prefix-sum-mono fg zero    = fg 0
prefix-sum-mono fg (suc r) =
  +-mono-≤ (fg (suc r)) (prefix-sum-mono fg r)

------------------------------------------------------------------------
-- The Hierarchy: SD[k] ⟹ SD[k+1]
--
-- FOSD ⟹ SOSD ⟹ TOSD ⟹ ...
-- Each level is strictly weaker (more distributions satisfy it),
-- corresponding to a broader class of utility functions.
--
-- The proof is one line: prefix-sum preserves monotonicity.
------------------------------------------------------------------------

SD-subsumes : ∀ k {μ ν : Dist ℕ} →
  μ SD[ k ]≤ ν → μ SD[ suc k ]≤ ν
SD-subsumes k sd = prefix-sum-mono sd

SD-subsumes-n : ∀ k j {μ ν : Dist ℕ} →
  μ SD[ k ]≤ ν → μ SD[ j + k ]≤ ν
SD-subsumes-n k zero    sd = sd
SD-subsumes-n k (suc j) sd = SD-subsumes (j + k) (SD-subsumes-n k j sd)

------------------------------------------------------------------------
-- sd-weight at r = 0 equals cdf-weight at 0 (for all orders)
--
-- prefix-sum f 0 = f 0, so iterating prefix-sum preserves the
-- value at 0.  This is the key lemma for the EV bridge.
------------------------------------------------------------------------

sd-at-0 : ∀ k (d : Dist ℕ) → sd-weight k d 0 ≡ cdf-weight d 0
sd-at-0 zero    d = refl
sd-at-0 (suc k) d = sd-at-0 k d

------------------------------------------------------------------------
-- SD[k] at r=0 gives CDF dominance at r=0
------------------------------------------------------------------------

sd→cdf-0 : ∀ k (μ ν : Dist ℕ) →
  μ SD[ k ]≤ ν →
  cdf-weight ν 0 ≤ cdf-weight μ 0
sd→cdf-0 k μ ν sd =
  subst₂ _≤_ (sd-at-0 k ν) (sd-at-0 k μ) (sd 0)
  where
    subst₂ : ∀ {A B : Set} (P : A → B → Set) {x x' y y'} →
      x ≡ x' → y ≡ y' → P x y → P x' y'
    subst₂ P refl refl p = p

------------------------------------------------------------------------
-- For AllBelow 1 distributions: CDF at suc r = total weight
--
-- When all values are ≤ 1, every entry satisfies v ≤ suc r,
-- so cdf-weight d (suc r) = total-weight d.
------------------------------------------------------------------------

cdf-all-below-1 : ∀ (d : Dist ℕ) → AllBelow d 1 →
  ∀ r → cdf-weight d (suc r) ≡ total-weight d
cdf-all-below-1 [] _ _ = refl
cdf-all-below-1 ((v , w) ∷ rest) (v≤1 , ab) r with v ≤? suc r
... | yes _ = cong (w +_) (cdf-all-below-1 rest ab r)
... | no v>sr = ⊥-elim (v>sr (≤-trans v≤1 (s≤s z≤n)))

------------------------------------------------------------------------
-- SD[k] ⟹ Expected-Value Dominance
--
-- For 0/1 distributions with equal total weights:
-- 1. SD[k] at r=0 gives CDF dominance at r=0
-- 2. For r ≥ 1, both CDFs equal total weight (AllBelow 1)
-- 3. Together, this gives full FOSD
-- 4. FOSD → EV by the existing bridge
--
-- This means EVERY level of the SD hierarchy implies EV dominance.
------------------------------------------------------------------------

sd→ev : ∀ k (μ ν : Dist ℕ) →
  AllBelow μ 1 → AllBelow ν 1 →
  total-weight μ ≡ total-weight ν →
  μ SD[ k ]≤ ν →
  weighted-sum μ ≤ weighted-sum ν
sd→ev k μ ν ab-μ ab-ν tw sd =
  fosd→ev μ ν ab-μ ab-ν tw sd-to-fosd
  where
    sd-to-fosd : μ FOSD≤ ν
    sd-to-fosd zero = sd→cdf-0 k μ ν sd
    sd-to-fosd (suc r)
      rewrite cdf-all-below-1 ν ab-ν r
      | cdf-all-below-1 μ ab-μ r | tw = ≤-refl

------------------------------------------------------------------------
-- Computational Tests
------------------------------------------------------------------------

-- FOSD on BiasedBandit lifts to SOSD and TOSD automatically
test-bandit-sosd : armB SOSD≤ armA
test-bandit-sosd = SD-subsumes 0 {armB} {armA} bandit-fosd

test-bandit-tosd : armB TOSD≤ armA
test-bandit-tosd = SD-subsumes 1 {armB} {armA} test-bandit-sosd

test-bandit-sd5 : armB SD[ 5 ]≤ armA
test-bandit-sd5 = SD-subsumes-n 0 5 {armB} {armA} bandit-fosd

-- SOSD is strictly weaker than FOSD:
-- ex-μ = {0 w/ weight 2, 2 w/ weight 1}, E[X] = 2/3
-- ex-ν = {1 w/ weight 3},                 E[X] = 1
-- FOSD fails at r=1 (cdf ν 1 = 3 > 2 = cdf μ 1)
-- but SOSD holds (integrated CDF of ν ≤ integrated CDF of μ everywhere)

ex-μ : Dist ℕ
ex-μ = (0 , 2) ∷ (2 , 1) ∷ []

ex-ν : Dist ℕ
ex-ν = (1 , 3) ∷ []

test-not-fosd-ν1 : cdf-weight ex-ν 1 ≡ 3
test-not-fosd-ν1 = refl

test-not-fosd-μ1 : cdf-weight ex-μ 1 ≡ 2
test-not-fosd-μ1 = refl

-- SOSD holds: icdf(ν, r) ≤ icdf(μ, r) at each threshold
test-icdf-μ : sd-weight 1 ex-μ 0 ≡ 2
test-icdf-μ = refl

test-icdf-ν : sd-weight 1 ex-ν 0 ≡ 0
test-icdf-ν = refl

test-icdf-μ1 : sd-weight 1 ex-μ 1 ≡ 4
test-icdf-μ1 = refl

test-icdf-ν1 : sd-weight 1 ex-ν 1 ≡ 3
test-icdf-ν1 = refl

test-icdf-μ2 : sd-weight 1 ex-μ 2 ≡ 7
test-icdf-μ2 = refl

test-icdf-ν2 : sd-weight 1 ex-ν 2 ≡ 6
test-icdf-ν2 = refl
