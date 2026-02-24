{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Probability.Finite
--
-- Finite discrete distributions as weighted lists.
-- Foundation for stochastic CSHRL via the Giry monad.
--
-- Design choices:
-- - Weights are natural numbers (unnormalized) for decidability
-- - Distribution is a list of (outcome, weight) pairs
-- - Zero weights are allowed but represent impossible outcomes
-- - Empty distribution represents the impossible event
------------------------------------------------------------------------

module CSHRL.Probability.Finite where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-identityʳ; +-assoc; *-distribˡ-+)
open import Data.List using (List; []; _∷_; map; foldr; concatMap; length)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Function using (_∘_; id)

------------------------------------------------------------------------
-- Core Types
------------------------------------------------------------------------

-- A finite distribution over A is a list of weighted outcomes
-- The weight represents relative probability (unnormalized)
Dist : Set → Set
Dist A = List (A × ℕ)

-- Weighted outcome type alias for clarity
Weighted : Set → Set
Weighted A = A × ℕ

------------------------------------------------------------------------
-- Basic Operations
------------------------------------------------------------------------

-- Extract just the outcomes (support)
support : ∀ {A} → Dist A → List A
support = map proj₁

-- Extract just the weights
weights : ∀ {A} → Dist A → List ℕ
weights = map proj₂

-- Total weight (normalizing constant)
total-weight : ∀ {A} → Dist A → ℕ
total-weight = foldr (λ aw acc → proj₂ aw + acc) 0

-- Scale all weights by a factor
scale : ∀ {A} → ℕ → Dist A → Dist A
scale k = map (λ { (a , w) → a , k * w })

------------------------------------------------------------------------
-- Monad Operations
------------------------------------------------------------------------

-- Pure: deterministic distribution (single outcome with weight 1)
pure : ∀ {A} → A → Dist A
pure a = (a , 1) ∷ []

-- Alias for compatibility
return : ∀ {A} → A → Dist A
return = pure

-- Bind: compose distributions (Kleisli extension)
-- For each outcome a with weight w, run f a and scale by w
_>>=_ : ∀ {A B} → Dist A → (A → Dist B) → Dist B
d >>= f = concatMap (λ { (a , w) → scale w (f a) }) d

-- Join: flatten nested distributions
join : ∀ {A} → Dist (Dist A) → Dist A
join dd = dd >>= id

-- Map (functor)
fmap : ∀ {A B} → (A → B) → Dist A → Dist B
fmap f = map (λ { (a , w) → f a , w })

-- Applicative operations
_<*>_ : ∀ {A B} → Dist (A → B) → Dist A → Dist B
df <*> da = df >>= (λ f → fmap f da)

_<$>_ : ∀ {A B} → (A → B) → Dist A → Dist B
_<$>_ = fmap

------------------------------------------------------------------------
-- Constructors for Common Distributions
------------------------------------------------------------------------

-- Uniform distribution over a list
uniform : ∀ {A} → List A → Dist A
uniform = map (_, 1)

-- Bernoulli-like: two outcomes with given weights
bernoulli : ∀ {A} → A → ℕ → A → ℕ → Dist A
bernoulli a₁ w₁ a₂ w₂ = (a₁ , w₁) ∷ (a₂ , w₂) ∷ []

-- Fair coin flip
coin : Dist ℕ  -- 0 = tails, 1 = heads
coin = bernoulli 0 1 1 1

-- Biased coin with weight p for heads (out of p + q total)
biased-coin : ℕ → ℕ → Dist ℕ
biased-coin p q = bernoulli 0 q 1 p

------------------------------------------------------------------------
-- Expected Value (for numeric outcomes)
------------------------------------------------------------------------

-- Weighted sum: Σ (value * weight)
-- This is the unnormalized expected value
weighted-sum : Dist ℕ → ℕ
weighted-sum = foldr (λ { (v , w) acc → v * w + acc }) 0

-- For a general reward type, we parameterize by arithmetic operations
module ExpectedValue
  (Reward : Set)
  (_+ᵣ_   : Reward → Reward → Reward)
  (_*ᵣ_   : ℕ → Reward → Reward)      -- Scalar multiplication
  (zeroᵣ  : Reward)
  where

  -- Weighted sum of rewards (unnormalized expected value)
  𝔼-unnorm : Dist Reward → Reward
  𝔼-unnorm = foldr (λ { (r , w) acc → (w *ᵣ r) +ᵣ acc }) zeroᵣ

  -- To get true expected value, divide by total-weight
  -- (kept abstract since division requires rationals or careful handling)

------------------------------------------------------------------------
-- Probability Queries
------------------------------------------------------------------------

-- Count outcomes satisfying a predicate (by weight)
count-weight : ∀ {A} → (A → ℕ) → Dist A → ℕ
count-weight indicator d = foldr (λ { (a , w) acc → indicator a * w + acc }) 0 d

-- Filter outcomes satisfying a predicate
filter-dist : ∀ {A} → (A → ℕ) → Dist A → Dist A
filter-dist indicator = map (λ { (a , w) → a , indicator a * w })

------------------------------------------------------------------------
-- Properties (Monad Laws - stated, proofs can be added)
------------------------------------------------------------------------

-- Left identity: pure a >>= f ≡ f a
-- Right identity: d >>= pure ≡ d  
-- Associativity: (d >>= f) >>= g ≡ d >>= (λ x → f x >>= g)

-- These follow from list concatMap laws + weight scaling properties

------------------------------------------------------------------------
-- Comparison Operations (for stochastic dominance)
------------------------------------------------------------------------

-- Pointwise comparison of distributions (first-order stochastic dominance)
-- requires ordering and decidability - deferred to StochasticCore

-- Helper: combine two distributions (product)
_⊗_ : ∀ {A B} → Dist A → Dist B → Dist (A × B)
da ⊗ db = da >>= (λ a → fmap (a ,_) db)

------------------------------------------------------------------------
-- Utilities
------------------------------------------------------------------------

-- Size of distribution (number of outcomes, not total weight)
size : ∀ {A} → Dist A → ℕ
size = length

-- Check if distribution is deterministic (single outcome)
is-deterministic : ∀ {A} → Dist A → Set
is-deterministic d = size d ≡ 1

-- Singleton extraction (for deterministic distributions)
-- Returns the single outcome if distribution has exactly one element
get-singleton : ∀ {A} → (d : Dist A) → A ⊎ ℕ  -- Returns outcome or size
get-singleton []              = inj₂ 0
get-singleton ((a , _) ∷ [])  = inj₁ a
get-singleton (_ ∷ _ ∷ _)     = inj₂ 2  -- Multiple outcomes
