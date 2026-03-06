{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Core.FOSD
--
-- Coinductive First-Order Stochastic Dominance on reward streams.
--
-- Extends CSHRL's stochastic framework from expected-value
-- comparison (≤ₛ-lex) to full distributional comparison via FOSD.
--
-- FOSD on streams: action a FOSD-dominates action b iff at every
-- timestep, the marginal reward distribution under a stochastically
-- dominates that under b.
--
-- Strictly stronger than ≤ₛ-lex: provides robustness to ALL
-- monotone utility functions, not just expected value.
--
-- Defines:
--   1. Marginal reward distribution at timestep n
--   2. Pointwise FOSD on streams of distributions
--   3. Coinductive FOSD on streams of distributions
--   4. The Stochastic Isomorphism Conjecture (as a type)
--   5. FOSDCoindHomo: FOSD-based coinductive homomorphism
--   6. FOSD ⟹ lex bridge (structure)
--
-- All --safe, no postulates.
------------------------------------------------------------------------

module CSHRL.Core.FOSD where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.List using (List; []; _∷_; map; foldr; concatMap)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Codata.Guarded.Stream using (Stream; head; tail; tabulate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Function using (_∘_)

open import CSHRL.Probability.Finite
  using (Dist; pure; _>>=_; fmap; scale; total-weight; weighted-sum)
open import CSHRL.Probability.FOSD
  using (_FOSD≤_; FOSD-refl; FOSD-trans;
         cdf-weight; fosd→ev; AllBelow)

------------------------------------------------------------------------
-- FOSD Core Module
------------------------------------------------------------------------

module FOSDCore
  (State Action : Set)
  (step : State → Action → Dist (State × ℕ))
  (all-actions : List Action)
  (default-action : Action)
  where

  --------------------------------------------------------------------
  -- Marginal Reward Distributions
  --
  -- At timestep n, the reward under (state, action) is a random
  -- variable. We compute its marginal distribution by unrolling
  -- the MDP n steps and projecting onto rewards.
  --------------------------------------------------------------------

  immediate-reward-dist : State → Action → Dist ℕ
  immediate-reward-dist s a = fmap proj₂ (step s a)

  -- Future state distribution after one step
  next-state-dist : State → Action → Dist State
  next-state-dist s a = fmap proj₁ (step s a)

  -- Marginal reward distribution at timestep n.
  -- Step 0: immediate reward from (s, a).
  -- Step n+1: take one step, then compute marginal at step n
  -- from the resulting state (using default action).
  marginal-reward : State → Action → ℕ → Dist ℕ
  marginal-reward s a zero = immediate-reward-dist s a
  marginal-reward s a (suc n) =
    step s a >>= λ { (s' , _) →
      marginal-reward s' default-action n }

  --------------------------------------------------------------------
  -- Pointwise FOSD
  --
  -- At every timestep n, the marginal reward distribution under
  -- action a FOSD-dominates that under action b.
  --------------------------------------------------------------------

  PointwiseFOSD : State → Action → Action → Set
  PointwiseFOSD s a b =
    ∀ n → marginal-reward s b n FOSD≤ marginal-reward s a n

  -- Reflexivity
  pw-fosd-refl : ∀ s a → PointwiseFOSD s a a
  pw-fosd-refl s a n = FOSD-refl (marginal-reward s a n)

  --------------------------------------------------------------------
  -- Coinductive FOSD on Streams of Distributions
  --
  -- The coinductive variant: FOSD at the head, and FOSD of
  -- the "tail distributions" (distributions at subsequent steps)
  -- coinductively.
  --
  -- For finite distributions, this unfolds to: at every depth,
  -- the marginal distribution FOSD-dominates.
  --------------------------------------------------------------------

  -- Coinductive FOSD indexed by a sequence of marginal distributions.
  -- At each level: head distribution FOSD-dominates, and tails do too.
  record StreamFOSD (μs νs : Stream (Dist ℕ)) : Set where
    coinductive
    field
      head-fosd : head νs FOSD≤ head μs
      tail-fosd : StreamFOSD (tail μs) (tail νs)

  open StreamFOSD public

  -- Reflexivity
  stream-fosd-refl : ∀ (ds : Stream (Dist ℕ)) → StreamFOSD ds ds
  head-fosd (stream-fosd-refl ds) = FOSD-refl (head ds)
  tail-fosd (stream-fosd-refl ds) = stream-fosd-refl (tail ds)

  -- Marginal reward stream: tabulate marginal distributions
  marginal-stream : State → Action → Stream (Dist ℕ)
  head (marginal-stream s a) = immediate-reward-dist s a
  tail (marginal-stream s a) =
    tabulate (λ n → marginal-reward s a (suc n))

  -- Coinductive FOSD on actions via their marginal streams
  _≤ₛ-fosd_ : State → Action → Action → Set
  _≤ₛ-fosd_ s a b = StreamFOSD (marginal-stream s a) (marginal-stream s b)

  --------------------------------------------------------------------
  -- The Stochastic Isomorphism Conjecture
  --
  -- Conjecture: Coinductive FOSD ⟺ Pointwise FOSD
  --
  -- Forward (coinductive → pointwise): unfold the coinductive
  -- record n times, extracting head-fosd at each step.
  --
  -- Reverse (pointwise → coinductive): pointwise at all n implies
  -- head at 0 and coinductively for tails (shifted pointwise).
  --------------------------------------------------------------------

  -- iter-head: nth element of a stream of distributions
  iter-head : ℕ → Stream (Dist ℕ) → Dist ℕ
  iter-head zero    ds = head ds
  iter-head (suc n) ds = iter-head n (tail ds)

  iter-head-tabulate : ∀ (f : ℕ → Dist ℕ) n →
    iter-head n (tabulate f) ≡ f n
  iter-head-tabulate f zero    = refl
  iter-head-tabulate f (suc n) = iter-head-tabulate (f ∘ suc) n

  -- iter-head n (marginal-stream s a) ≡ marginal-reward s a n
  iter-head-marginal : ∀ s a n →
    iter-head n (marginal-stream s a) ≡ marginal-reward s a n
  iter-head-marginal s a zero    = refl
  iter-head-marginal s a (suc n) =
    iter-head-tabulate (λ k → marginal-reward s a (suc k)) n

  -- Forward: coinductive → pointwise
  stream-fosd-to-pointwise : ∀ {μs νs} →
    StreamFOSD μs νs →
    ∀ n → iter-head n νs FOSD≤ iter-head n μs
  stream-fosd-to-pointwise sf zero    = head-fosd sf
  stream-fosd-to-pointwise sf (suc n) =
    stream-fosd-to-pointwise (tail-fosd sf) n

  conjecture-forward : ∀ s a b →
    _≤ₛ-fosd_ s a b → PointwiseFOSD s a b
  conjecture-forward s a b sf n =
    subst₂ _FOSD≤_
      (iter-head-marginal s b n)
      (iter-head-marginal s a n)
    (stream-fosd-to-pointwise sf n)
    where
      subst₂ : ∀ {A B : Set} (P : A → B → Set) {x x' y y'} →
        x ≡ x' → y ≡ y' → P x y → P x' y'
      subst₂ P refl refl p = p

  -- Reverse: pointwise → coinductive
  pointwise-tail : ∀ {μs νs} →
    (∀ n → iter-head n νs FOSD≤ iter-head n μs) →
    ∀ n → iter-head n (tail νs) FOSD≤ iter-head n (tail μs)
  pointwise-tail pw n = pw (suc n)

  pointwise-to-stream-fosd : ∀ {μs νs} →
    (∀ n → iter-head n νs FOSD≤ iter-head n μs) →
    StreamFOSD μs νs
  head-fosd (pointwise-to-stream-fosd pw) = pw zero
  tail-fosd (pointwise-to-stream-fosd pw) =
    pointwise-to-stream-fosd (pointwise-tail pw)

  conjecture-reverse : ∀ s a b →
    PointwiseFOSD s a b → _≤ₛ-fosd_ s a b
  conjecture-reverse s a b pw =
    pointwise-to-stream-fosd λ n →
      subst₂ _FOSD≤_
        (sym (iter-head-marginal s b n))
        (sym (iter-head-marginal s a n))
      (pw n)
    where
      subst₂ : ∀ {A B : Set} (P : A → B → Set) {x x' y y'} →
        x ≡ x' → y ≡ y' → P x y → P x' y'
      subst₂ P refl refl p = p

  Conjecture-Forward : Set
  Conjecture-Forward = ∀ s a b →
    _≤ₛ-fosd_ s a b → PointwiseFOSD s a b

  Conjecture-Reverse : Set
  Conjecture-Reverse = ∀ s a b →
    PointwiseFOSD s a b → _≤ₛ-fosd_ s a b

  Conjecture-Isomorphism : Set
  Conjecture-Isomorphism = Conjecture-Forward × Conjecture-Reverse

  conjecture-isomorphism : Conjecture-Isomorphism
  conjecture-isomorphism = conjecture-forward , conjecture-reverse

  --------------------------------------------------------------------
  -- FOSD-Based Coinductive Homomorphism
  --
  -- A ranking that preserves FOSD (not just expected values)
  -- at every timestep. Strictly stronger than StochasticCoindHomo.
  --
  -- An agent with FOSDCoindHomo is optimal for ALL monotone
  -- utility functions simultaneously -- not just expected-value
  -- maximizers.
  --------------------------------------------------------------------

  -- When _≤ₐ_ s a b (a ≤ b, b preferred), the preferred action b must
  -- dominate a: PointwiseFOSD s b a (b's marginals FOSD-dominate a's).
  record FOSDCoindHomo : Set₁ where
    field
      _≤ₐ_ : State → Action → Action → Set
      preserves-fosd : ∀ a b s →
        _≤ₐ_ s a b → PointwiseFOSD s b a

  open FOSDCoindHomo public

  --------------------------------------------------------------------
  -- FOSD ⟹ Expected-Value Dominance (Bridge Structure)
  --
  -- For 0/1 reward MDPs with equal total weights, pointwise FOSD
  -- implies pointwise expected-value dominance at every timestep.
  --
  -- This connects FOSDCoindHomo to StochasticCoindHomo:
  -- any FOSD-preserving ranking also preserves expected values.
  --
  -- fosd→ev from Probability.FOSD provides the per-timestep
  -- bridge; this module lifts it to streams.
  --------------------------------------------------------------------

  module FOSDImpliesLex
    (all-below : ∀ s a n → AllBelow (marginal-reward s a n) 1)
    (tw-eq : ∀ s a b n → total-weight (marginal-reward s a n) ≡
                          total-weight (marginal-reward s b n))
    where

    pointwise-ev : ∀ s a b →
      PointwiseFOSD s a b →
      ∀ n → weighted-sum (marginal-reward s b n) ≤
            weighted-sum (marginal-reward s a n)
    pointwise-ev s a b pw-fosd n =
      fosd→ev (marginal-reward s b n) (marginal-reward s a n)
        (all-below s b n) (all-below s a n)
        (tw-eq s b a n) (pw-fosd n)

  --------------------------------------------------------------------
  -- FOSD ⟹ Lexicographic EV-Stream Dominance
  --
  -- Lifts pointwise EV dominance to coinductive lexicographic
  -- dominance on the stream of expected marginal rewards.
  --
  -- This is the formal FOSD → lex bridge: any FOSDCoindHomo
  -- (ranking that preserves FOSD) also preserves lexicographic
  -- expected-value stream ordering.
  --
  -- marginal-ev-stream s a = ⟨ E[marginal(s,a,0)],
  --                            E[marginal(s,a,1)], ... ⟩
  --
  -- PointwiseFOSD s a b ⟹ marginal-ev-stream s b ≤ₛ-ev
  --                         marginal-ev-stream s a
  --------------------------------------------------------------------

  module FOSDToLexStream
    (all-below : ∀ s a n → AllBelow (marginal-reward s a n) 1)
    (tw-eq : ∀ s a b n → total-weight (marginal-reward s a n) ≡
                          total-weight (marginal-reward s b n))
    where

    open FOSDImpliesLex all-below tw-eq

    marginal-ev : State → Action → ℕ → ℕ
    marginal-ev s a n = weighted-sum (marginal-reward s a n)

    marginal-ev-stream : State → Action → Stream ℕ
    marginal-ev-stream s a = tabulate (marginal-ev s a)

    record _≤ₛ-ev_ (x y : Stream ℕ) : Set where
      coinductive
      field
        hd≤ : head x ≤ head y
        tl≤ : head x ≡ head y → tail x ≤ₛ-ev tail y

    open _≤ₛ-ev_ public

    ≤ₛ-ev-refl : ∀ (s : Stream ℕ) → s ≤ₛ-ev s
    hd≤ (≤ₛ-ev-refl s) = ≤-refl
    tl≤ (≤ₛ-ev-refl s) _ = ≤ₛ-ev-refl (tail s)

    private
      iter-ℕ : ℕ → Stream ℕ → ℕ
      iter-ℕ zero    s = head s
      iter-ℕ (suc n) s = iter-ℕ n (tail s)

      iter-tab : ∀ (f : ℕ → ℕ) n → iter-ℕ n (tabulate f) ≡ f n
      iter-tab f zero    = refl
      iter-tab f (suc n) = iter-tab (f ∘ suc) n

    pw→lex : ∀ {x y : Stream ℕ} →
      (∀ n → iter-ℕ n x ≤ iter-ℕ n y) →
      x ≤ₛ-ev y
    hd≤ (pw→lex pw) = pw zero
    tl≤ (pw→lex pw) _ = pw→lex (λ n → pw (suc n))

    fosd→lex-stream : ∀ s a b →
      PointwiseFOSD s a b →
      marginal-ev-stream s b ≤ₛ-ev marginal-ev-stream s a
    fosd→lex-stream s a b pw = pw→lex (λ n →
      subst₂ _≤_
        (sym (iter-tab (marginal-ev s b) n))
        (sym (iter-tab (marginal-ev s a) n))
        (pointwise-ev s a b pw n))
      where
        subst₂ : ∀ {A B : Set} (P : A → B → Set) {x x' y y'} →
          x ≡ x' → y ≡ y' → P x y → P x' y'
        subst₂ P refl refl p = p

    fosd-homo→ev-lex : (homo : FOSDCoindHomo) →
      ∀ a b s → FOSDCoindHomo._≤ₐ_ homo s a b →
        marginal-ev-stream s a ≤ₛ-ev marginal-ev-stream s b
    fosd-homo→ev-lex homo a b s p =
      fosd→lex-stream s b a
        (FOSDCoindHomo.preserves-fosd homo a b s p)

  --------------------------------------------------------------------
  -- Synthesis Observation Layer for FOSD
  --
  -- Instead of comparing expected traces (as in ≤ₛ-lex synthesis),
  -- compare marginal distributions via FOSD at each threshold.
  --
  -- The PredicateDSL and CEGIS machinery are UNCHANGED.
  -- Only the observation generation differs:
  --   Expected-value: observe (state, E[trace(a)] ≤ E[trace(b)])
  --   FOSD:           observe (state, ∀r. CDF(a,r) ≤ CDF(b,r))
  --
  -- This provides the same synthesis guarantees (propagation,
  -- dissolution, tight bound) but for a stronger ordering.
  --------------------------------------------------------------------

  fosd-compare : State → Action → Action → ℕ → ℕ → Set
  fosd-compare s a b n r =
    cdf-weight (marginal-reward s b n) r ≤
    cdf-weight (marginal-reward s a n) r

  -- Full FOSD comparison at a given depth (all thresholds)
  fosd-at-depth : State → Action → Action → ℕ → Set
  fosd-at-depth s a b n =
    marginal-reward s b n FOSD≤ marginal-reward s a n
