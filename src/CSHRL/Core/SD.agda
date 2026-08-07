{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Core.SD
--
-- The Stochastic Dominance Hierarchy on reward streams.
--
-- Lifts the SD hierarchy from Probability.SD (single distributions)
-- to coinductive reward streams, defining:
--
--   1. PointwiseSD k: SD[k] at every depth of the reward stream
--   2. SDCoindHomo k: a ranking that preserves SD[k] at every state
--   3. Hierarchy subsumption on streams and homos
--   4. The SD-to-Lex Bridge: any SDCoindHomo k implies lexicographic
--      EV-stream dominance (for 0/1 rewards with equal total weights)
--
-- The bridge theorem is the crown jewel: rankings verified at ANY
-- level of the SD hierarchy automatically yield expected-value
-- optimality.  Higher levels (FOSD > SOSD > TOSD > ...) provide
-- progressively weaker requirements, capturing broader classes of
-- utility functions:
--
--   SDCoindHomo 0 (FOSD) → all monotone utilities
--   SDCoindHomo 1 (SOSD) → all concave monotone (risk-averse)
--   SDCoindHomo 2 (TOSD) → all prudent agents
--   SDCoindHomo k         → (k+1)-th order utility class
--
-- All --safe, no postulates.
------------------------------------------------------------------------

module CSHRL.Core.SD where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Codata.Guarded.Stream using (Stream; head; tail; tabulate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Function using (_∘_)

open import CSHRL.Probability.Finite
  using (Dist; total-weight; weighted-sum)
open import CSHRL.Probability.FOSD
  using (AllBelow)
open import CSHRL.Probability.SD
  using (_SD[_]≤_; SD-refl; SD-subsumes; sd→ev)

------------------------------------------------------------------------
-- SD Core Module
------------------------------------------------------------------------

module SDCore
  (State Action : Set)
  (step : State → Action → Dist (State × ℕ))
  (all-actions : List Action)
  (default-action : Action)
  where

  open import CSHRL.Core.FOSD
  open FOSDCore State Action step all-actions default-action
    using (marginal-reward; PointwiseFOSD; FOSDCoindHomo;
           marginal-stream; iter-head; iter-head-marginal)

  --------------------------------------------------------------------
  -- Pointwise SD on Reward Streams
  --
  -- At every timestep n, the marginal reward distribution under
  -- action a SD[k]-dominates that under action b.
  --------------------------------------------------------------------

  PointwiseSD : ℕ → State → Action → Action → Set
  PointwiseSD k s a b =
    ∀ n → marginal-reward s b n SD[ k ]≤ marginal-reward s a n

  pw-sd-refl : ∀ k s a → PointwiseSD k s a a
  pw-sd-refl k s a n = SD-refl k (marginal-reward s a n)

  --------------------------------------------------------------------
  -- Compatibility: PointwiseFOSD = PointwiseSD 0
  --------------------------------------------------------------------

  pw-fosd→pw-sd-0 : ∀ s a b → PointwiseFOSD s a b → PointwiseSD 0 s a b
  pw-fosd→pw-sd-0 s a b pw = pw

  pw-sd-0→pw-fosd : ∀ s a b → PointwiseSD 0 s a b → PointwiseFOSD s a b
  pw-sd-0→pw-fosd s a b pw = pw

  --------------------------------------------------------------------
  -- Hierarchy on Streams: PointwiseSD k ⟹ PointwiseSD (k+1)
  --
  -- If a ranking dominates at SD level k at every timestep,
  -- it also dominates at the weaker level k+1.
  --------------------------------------------------------------------

  pw-sd-subsumes : ∀ k s a b →
    PointwiseSD k s a b → PointwiseSD (suc k) s a b
  pw-sd-subsumes k s a b pw n = SD-subsumes k (pw n)

  --------------------------------------------------------------------
  -- Coinductive SD on Streams of Distributions
  --
  -- The coinductive variant of PointwiseSD: SD[k] at the head,
  -- and SD[k] of the tail distributions coinductively.
  -- Generalizes StreamFOSD from Core.FOSD to arbitrary k.
  --------------------------------------------------------------------

  record StreamSD (k : ℕ) (μs νs : Stream (Dist ℕ)) : Set where
    coinductive
    field
      head-sd : head νs SD[ k ]≤ head μs
      tail-sd : StreamSD k (tail μs) (tail νs)

  open StreamSD public

  stream-sd-refl : ∀ k (ds : Stream (Dist ℕ)) → StreamSD k ds ds
  head-sd (stream-sd-refl k ds) = SD-refl k (head ds)
  tail-sd (stream-sd-refl k ds) = stream-sd-refl k (tail ds)

  _≤ₛ-sd_ : ℕ → State → Action → Action → Set
  _≤ₛ-sd_ k s a b = StreamSD k (marginal-stream s a) (marginal-stream s b)

  --------------------------------------------------------------------
  -- The SD Isomorphism: Coinductive SD[k] ⟺ Pointwise SD[k]
  --
  -- Generalizes the FOSD Stochastic Isomorphism to all levels
  -- of the hierarchy. The proof is purely structural: it only
  -- uses head/tail decomposition, not any property of SD[k].
  --------------------------------------------------------------------

  stream-sd-to-pointwise : ∀ {k μs νs} →
    StreamSD k μs νs →
    ∀ n → iter-head n νs SD[ k ]≤ iter-head n μs
  stream-sd-to-pointwise sf zero    = head-sd sf
  stream-sd-to-pointwise sf (suc n) =
    stream-sd-to-pointwise (tail-sd sf) n

  pointwise-to-stream-sd : ∀ {k μs νs} →
    (∀ n → iter-head n νs SD[ k ]≤ iter-head n μs) →
    StreamSD k μs νs
  head-sd (pointwise-to-stream-sd pw) = pw zero
  tail-sd (pointwise-to-stream-sd pw) =
    pointwise-to-stream-sd (λ n → pw (suc n))

  private
    subst₂-rel : ∀ {A B : Set} (P : A → B → Set) {x x' y y'} →
      x ≡ x' → y ≡ y' → P x y → P x' y'
    subst₂-rel P refl refl p = p

  sd-iso-forward : ∀ k s a b →
    _≤ₛ-sd_ k s a b → PointwiseSD k s a b
  sd-iso-forward k s a b sf n =
    subst₂-rel (λ μ ν → μ SD[ k ]≤ ν)
      (iter-head-marginal s b n)
      (iter-head-marginal s a n)
      (stream-sd-to-pointwise sf n)

  sd-iso-reverse : ∀ k s a b →
    PointwiseSD k s a b → _≤ₛ-sd_ k s a b
  sd-iso-reverse k s a b pw =
    pointwise-to-stream-sd λ n →
      subst₂-rel (λ μ ν → μ SD[ k ]≤ ν)
        (sym (iter-head-marginal s b n))
        (sym (iter-head-marginal s a n))
        (pw n)

  SD-Isomorphism : ℕ → Set
  SD-Isomorphism k = (∀ s a b → _≤ₛ-sd_ k s a b → PointwiseSD k s a b)
                   × (∀ s a b → PointwiseSD k s a b → _≤ₛ-sd_ k s a b)

  sd-isomorphism : ∀ k → SD-Isomorphism k
  sd-isomorphism k = sd-iso-forward k , sd-iso-reverse k

  --------------------------------------------------------------------
  -- SD-Based Coinductive Homomorphism
  --
  -- A ranking that preserves SD[k] at every state.
  -- SDCoindHomo 0 = FOSDCoindHomo (FOSD preservation).
  -- SDCoindHomo 1 = SOSD preservation (risk-averse optimality).
  -- SDCoindHomo k = (k+1)-th order SD preservation.
  --
  -- Each level captures a broader class of utility functions.
  --------------------------------------------------------------------

  record SDCoindHomo (k : ℕ) : Set₁ where
    field
      _≤ₐ_ : State → Action → Action → Set
      preserves-sd : ∀ a b s →
        _≤ₐ_ s a b → PointwiseSD k s b a

  open SDCoindHomo public

  --------------------------------------------------------------------
  -- Compatibility: FOSDCoindHomo → SDCoindHomo 0
  --------------------------------------------------------------------

  fosd-homo→sd-0 : FOSDCoindHomo → SDCoindHomo 0
  fosd-homo→sd-0 homo = record
    { _≤ₐ_ = FOSDCoindHomo._≤ₐ_ homo
    ; preserves-sd = FOSDCoindHomo.preserves-fosd homo
    }

  --------------------------------------------------------------------
  -- Hierarchy on Homos: SDCoindHomo k → SDCoindHomo (k+1)
  --
  -- If a ranking preserves SD[k], it also preserves SD[k+1].
  -- This is the subsumption chain lifted to coinductive homos.
  --------------------------------------------------------------------

  sd-homo-subsumes : ∀ k → SDCoindHomo k → SDCoindHomo (suc k)
  sd-homo-subsumes k homo = record
    { _≤ₐ_ = SDCoindHomo._≤ₐ_ homo
    ; preserves-sd = λ a b s p →
        pw-sd-subsumes k s b a (SDCoindHomo.preserves-sd homo a b s p)
    }

  --------------------------------------------------------------------
  -- Multi-step subsumption on homos
  --------------------------------------------------------------------

  sd-homo-subsumes-n : ∀ k j → SDCoindHomo k → SDCoindHomo (j + k)
  sd-homo-subsumes-n k zero    homo = homo
  sd-homo-subsumes-n k (suc j) homo =
    sd-homo-subsumes (j + k) (sd-homo-subsumes-n k j homo)

  --------------------------------------------------------------------
  -- SD[k] ⟹ Per-Timestep Expected-Value Dominance
  --
  -- For 0/1 reward MDPs with equal total weights, SD[k] at every
  -- depth implies per-timestep EV dominance.
  --
  -- This uses the key lemma sd→ev from Probability.SD:
  -- SD[k] at r=0 gives CDF dominance → complement dominance → EV.
  --------------------------------------------------------------------

  module SDImpliesEV
    (k : ℕ)
    (all-below : ∀ s a n → AllBelow (marginal-reward s a n) 1)
    (tw-eq : ∀ s a b n → total-weight (marginal-reward s a n) ≡
                          total-weight (marginal-reward s b n))
    where

    sd-pointwise-ev : ∀ s a b →
      PointwiseSD k s a b →
      ∀ n → weighted-sum (marginal-reward s b n) ≤
            weighted-sum (marginal-reward s a n)
    sd-pointwise-ev s a b pw n =
      sd→ev k (marginal-reward s b n) (marginal-reward s a n)
        (all-below s b n) (all-below s a n) (tw-eq s b a n) (pw n)

  --------------------------------------------------------------------
  -- SD-to-Lex Bridge
  --
  -- Lifts per-timestep EV dominance to coinductive lexicographic
  -- dominance on the stream of expected marginal rewards.
  --
  -- This is the master bridge theorem: ANY SDCoindHomo k
  -- (at any level of the hierarchy) implies lexicographic
  -- EV-stream dominance.
  --
  -- The proof structure mirrors FOSDToLexStream from Core.FOSD,
  -- but uses sd→ev instead of fosd→ev for the per-timestep step.
  --------------------------------------------------------------------

  module SDToLexStream
    (k : ℕ)
    (all-below : ∀ s a n → AllBelow (marginal-reward s a n) 1)
    (tw-eq : ∀ s a b n → total-weight (marginal-reward s a n) ≡
                          total-weight (marginal-reward s b n))
    where

    open SDImpliesEV k all-below tw-eq

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

    sd→lex-stream : ∀ s a b →
      PointwiseSD k s a b →
      marginal-ev-stream s b ≤ₛ-ev marginal-ev-stream s a
    sd→lex-stream s a b pw = pw→lex (λ n →
      subst₂ _≤_
        (sym (iter-tab (marginal-ev s b) n))
        (sym (iter-tab (marginal-ev s a) n))
        (sd-pointwise-ev s a b pw n))
      where
        subst₂ : ∀ {A B : Set} (P : A → B → Set) {x x' y y'} →
          x ≡ x' → y ≡ y' → P x y → P x' y'
        subst₂ P refl refl p = p

    sd-homo→ev-lex : (homo : SDCoindHomo k) →
      ∀ a b s → SDCoindHomo._≤ₐ_ homo s a b →
        marginal-ev-stream s a ≤ₛ-ev marginal-ev-stream s b
    sd-homo→ev-lex homo a b s p =
      sd→lex-stream s b a
        (SDCoindHomo.preserves-sd homo a b s p)
