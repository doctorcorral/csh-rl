{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- appendix.StochasticSubsumption: Argmax Subsumption for Stochastic MDPs
--
-- This module extends the classical subsumption theorem to stochastic
-- environments. The key insight: by linearity of expectation,
--
--   𝔼[Σᵢ rᵢ] = Σᵢ 𝔼[rᵢ]
--
-- So comparing partial sums of expected rewards is equivalent to
-- comparing expected partial sums—exactly what classical RL optimizes.
--
-- ARCHITECTURE:
-- - Main stochastic theory uses LEXICOGRAPHIC comparison (_≤ₛ-lex_)
--   for alignment with trace-based learning
-- - This module uses POINTWISE expected comparison for subsumption
-- - The two serve different purposes:
--   * Lex: ranking semantics, trace comparison
--   * Pointwise: argmax subsumption, classical RL connection
--
-- THEOREM: If rankings satisfy pointwise expected stream dominance,
-- then for any finite horizon N, the ranked-higher action has
-- higher expected cumulative reward.
------------------------------------------------------------------------

module appendix.StochasticSubsumption where

open import Data.List using (List; map; foldr; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Codata.Guarded.Stream using (Stream; head; tail; tabulate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Import finite distributions
open import CSHRL.Probability.Finite using (Dist; pure; _>>=_; fmap; scale)

------------------------------------------------------------------------
-- Stochastic Subsumption Module
------------------------------------------------------------------------

module StochasticSubsumption
  (State Action Reward : Set)
  
  -- Stochastic transition
  (step : State → Action → Dist (State × Reward))
  
  -- Reward ordering
  (_≤ᵣ_ : Reward → Reward → Set)
  (≤ᵣ-refl : ∀ {r} → r ≤ᵣ r)
  
  -- Reward arithmetic
  (_+ᵣ_ : Reward → Reward → Reward)
  (_*ᵣ_ : ℕ → Reward → Reward)
  (zeroᵣ : Reward)
  (+ᵣ-mono-≤ : ∀ {a b c d} → a ≤ᵣ b → c ≤ᵣ d → (a +ᵣ c) ≤ᵣ (b +ᵣ d))
  
  -- For value computation
  (max : Reward → Reward → Reward)
  (bottom : Reward)
  (all-actions : List Action)
  where

  ------------------------------------------------------------------------
  -- Expected Value Computation (from Stochastic.agda)
  ------------------------------------------------------------------------

  StreamR : Set
  StreamR = Stream Reward

  -- Weighted sum (unnormalized expected value)
  𝔼ᵣ : Dist Reward → Reward
  𝔼ᵣ = foldr (λ { (r , w) acc → (w *ᵣ r) +ᵣ acc }) zeroᵣ

  -- Expected immediate reward
  expected-immediate : Dist (State × Reward) → Reward
  expected-immediate d = 𝔼ᵣ (fmap proj₂ d)

  -- Max over list
  max-list : List Reward → Reward
  max-list = foldr max bottom

  -- Finite-horizon expected value
  solve-expected : State → ℕ → Reward
  solve-expected s zero = 
    max-list (map (λ a → expected-immediate (step s a)) all-actions)
  solve-expected s (suc n) = 
    max-list (map (λ a → 
      𝔼ᵣ (fmap (λ { (s' , _) → solve-expected s' n }) (step s a))) 
      all-actions)

  -- Expected action-value stream
  expected-action-value : State → Action → StreamR
  head (expected-action-value s a) = expected-immediate (step s a)
  tail (expected-action-value s a) = 
    tabulate (λ n → 𝔼ᵣ (fmap (λ { (s' , _) → solve-expected s' n }) (step s a)))

  ------------------------------------------------------------------------
  -- Pointwise Expected Stream Dominance
  ------------------------------------------------------------------------

  -- This is the POINTWISE version (not lexicographic)
  -- Required for subsumption; stronger than lex
  record _≤ₛ-expected_ (x y : StreamR) : Set where
    coinductive
    field
      head≤ : head x ≤ᵣ head y
      tail≤ : tail x ≤ₛ-expected tail y

  open _≤ₛ-expected_ public

  -- Reflexivity
  ≤ₛ-expected-refl : ∀ (s : StreamR) → s ≤ₛ-expected s
  head≤ (≤ₛ-expected-refl s) = ≤ᵣ-refl
  tail≤ (≤ₛ-expected-refl s) = ≤ₛ-expected-refl (tail s)

  ------------------------------------------------------------------------
  -- Pointwise Dominance (Bridge to Finite Horizons)
  ------------------------------------------------------------------------

  -- Extract n-th element
  iter-head : ℕ → StreamR → Reward
  iter-head zero    s = head s
  iter-head (suc n) s = iter-head n (tail s)

  -- Pointwise: at every index
  PointwiseDominance : StreamR → StreamR → Set
  PointwiseDominance x y = ∀ n → iter-head n x ≤ᵣ iter-head n y

  -- KEY LEMMA: coinductive expected ≤ₛ implies pointwise
  ≤ₛ-expected-to-pointwise : ∀ {x y} → x ≤ₛ-expected y → PointwiseDominance x y
  ≤ₛ-expected-to-pointwise p zero    = head≤ p
  ≤ₛ-expected-to-pointwise p (suc n) = ≤ₛ-expected-to-pointwise (tail≤ p) n

  ------------------------------------------------------------------------
  -- Partial Sums of Expected Rewards
  ------------------------------------------------------------------------

  -- Partial sum: Σᵢ₌₀ᴺ⁻¹ 𝔼[rᵢ]
  -- By linearity of expectation, this equals 𝔼[Σᵢ₌₀ᴺ⁻¹ rᵢ]
  partial-sum : ℕ → StreamR → Reward
  partial-sum zero    _ = zeroᵣ
  partial-sum (suc n) s = head s +ᵣ partial-sum n (tail s)

  ------------------------------------------------------------------------
  -- Stochastic Coinductive Homomorphism (Pointwise Version)
  ------------------------------------------------------------------------

  -- For subsumption, we need rankings that preserve POINTWISE expected dominance
  record StochasticCoindHomoPW : Set₁ where
    field
      _≤ₐ_ : State → Action → Action → Set
      preserves : ∀ a b s → _≤ₐ_ s a b →
                  expected-action-value s a ≤ₛ-expected expected-action-value s b

  ------------------------------------------------------------------------
  -- Subsumption Theorem
  ------------------------------------------------------------------------

  private
    pointwise-tail : ∀ {x y} → PointwiseDominance x y → 
                     PointwiseDominance (tail x) (tail y)
    pointwise-tail pw n = pw (suc n)

  -- Partial sum respects pointwise dominance
  partial-sum-mono : ∀ N x y → PointwiseDominance x y → 
                     partial-sum N x ≤ᵣ partial-sum N y
  partial-sum-mono zero _ _ _ = ≤ᵣ-refl
  partial-sum-mono (suc n) x y pw = 
    +ᵣ-mono-≤ (pw zero) (partial-sum-mono n (tail x) (tail y) (pointwise-tail pw))

  -- SUBSUMPTION THEOREM TYPE
  SubsumesExpectedPartialSum : StochasticCoindHomoPW → Set
  SubsumesExpectedPartialSum homo = ∀ s a b N →
    StochasticCoindHomoPW._≤ₐ_ homo s a b →
    partial-sum N (expected-action-value s a) ≤ᵣ 
    partial-sum N (expected-action-value s b)

  -- MAIN THEOREM: Stochastic subsumption
  stochastic-subsumes-partial-sum : (homo : StochasticCoindHomoPW) → 
                                     SubsumesExpectedPartialSum homo
  stochastic-subsumes-partial-sum homo s a b N ranking-says = 
    partial-sum-mono N (expected-action-value s a) (expected-action-value s b) pointwise
    where
      stream-dom : expected-action-value s a ≤ₛ-expected expected-action-value s b
      stream-dom = StochasticCoindHomoPW.preserves homo a b s ranking-says
      pointwise : PointwiseDominance (expected-action-value s a) (expected-action-value s b)
      pointwise = ≤ₛ-expected-to-pointwise stream-dom

  ------------------------------------------------------------------------
  -- Corollary: Stochastic Argmax is Subsumed
  ------------------------------------------------------------------------

  StochasticArgmaxSubsumed : StochasticCoindHomoPW → Set
  StochasticArgmaxSubsumed homo = ∀ s b →
    (∀ a → StochasticCoindHomoPW._≤ₐ_ homo s a b) →
    ∀ a N → partial-sum N (expected-action-value s a) ≤ᵣ 
            partial-sum N (expected-action-value s b)

  stochastic-argmax-subsumed : (homo : StochasticCoindHomoPW) → 
                                StochasticArgmaxSubsumed homo
  stochastic-argmax-subsumed homo s b b-is-top a N = 
    stochastic-subsumes-partial-sum homo s a b N (b-is-top a)

  ------------------------------------------------------------------------
  -- Connection: Pointwise implies Lexicographic (from main theory)
  ------------------------------------------------------------------------

  -- For reference: lexicographic ordering (conditional tail)
  record _≤ₛ-lex_ (x y : StreamR) : Set where
    coinductive
    field
      head≤ : head x ≤ᵣ head y
      tail≤ : head x ≡ head y → tail x ≤ₛ-lex tail y

  -- Pointwise is stronger than lexicographic
  pointwise→lex : ∀ {x y} → x ≤ₛ-expected y → x ≤ₛ-lex y
  _≤ₛ-lex_.head≤ (pointwise→lex p) = head≤ p
  _≤ₛ-lex_.tail≤ (pointwise→lex p) = λ _ → pointwise→lex (tail≤ p)

  ------------------------------------------------------------------------
  -- Commentary: Why Two Orderings?
  ------------------------------------------------------------------------

  -- LEXICOGRAPHIC (_≤ₛ-lex_):
  -- - Natural for trace-based learning (finite prefix comparison)
  -- - Captures "first difference wins" semantics
  -- - Weaker: doesn't require infinite pointwise dominance
  -- - Used in main StochasticCoindHomo
  --
  -- POINTWISE (_≤ₛ-expected_):
  -- - Required for argmax subsumption
  -- - Implies lexicographic (but not vice versa)
  -- - Many practical MDPs satisfy pointwise when ranking is sound
  -- - Used here for classical RL connection
  --
  -- The relationship:
  --   Pointwise ⟹ Lexicographic ⟹ (first difference decides)
  --
  -- For CoinFlip: Flip pointwise-dominates Stay, so both apply.
