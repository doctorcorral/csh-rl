{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- appendix.Arithmetic: Extension for Classical RL Subsumption
--
-- This module extends Core with reward arithmetic to prove that
-- CSHRL's coinductive optimality subsumes classical RL's argmax
-- criterion. Specifically: if a ranking satisfies the coinductive
-- symmetric homomorphism property, then for any finite horizon N,
-- the action ranked higher has a higher partial sum of rewards.
--
-- This is NOT required for CSHRL's core theory—it's an extension
-- that connects CSHRL to classical RL for comparison purposes.
------------------------------------------------------------------------

module appendix.Arithmetic where

open import Data.List using (List; map; foldr; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _⊔_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Codata.Guarded.Stream using (Stream; head; tail; tabulate)

------------------------------------------------------------------------
-- Extended Core Module
--
-- Adds reward arithmetic parameters: addition, reflexivity, and
-- monotonicity of addition with respect to the reward ordering.
------------------------------------------------------------------------

module CoreWithArithmetic
  (State Action Reward : Set)
  (step                : State → Action → State × Reward)
  (_≤ᵣ_                : Reward → Reward → Set)
  (max                 : Reward → Reward → Reward)
  (bottom              : Reward)
  (all-actions         : List Action)
  -- Additional parameters for arithmetic
  (_+ᵣ_                : Reward → Reward → Reward)
  (≤ᵣ-refl             : ∀ {r} → r ≤ᵣ r)
  (+ᵣ-mono-≤           : ∀ {a b c d} → a ≤ᵣ b → c ≤ᵣ d → (a +ᵣ c) ≤ᵣ (b +ᵣ d))
  where

  ------------------------------------------------------------------------
  -- Core Definitions (duplicated for independence, matches CSHRL.Core)
  ------------------------------------------------------------------------

  StreamR : Set
  StreamR = Stream Reward

  max-list : List Reward → Reward
  max-list = foldr max bottom

  solve : State → ℕ → Reward
  solve s zero    = max-list (map (λ a → proj₂ (step s a)) all-actions)
  solve s (suc n) = max-list (map (λ a → solve (proj₁ (step s a)) n) all-actions)

  value : State → StreamR
  value s = tabulate (solve s)

  action-value : State → Action → StreamR
  head (action-value s a) = proj₂ (step s a)
  tail (action-value s a) = value (proj₁ (step s a))

  -- Coinductive stream ordering
  record _≤ₛ_ (x y : StreamR) : Set where
    coinductive
    field
      head≤ : head x ≤ᵣ head y
      tail≤ : tail x ≤ₛ tail y

  open _≤ₛ_ public

  -- The coinductive symmetric homomorphism
  record CoindHomo : Set₁ where
    field
      _≤ₐ_      : State → Action → Action → Set
      preserves : ∀ a b s → _≤ₐ_ s a b →
                  action-value s a ≤ₛ action-value s b

  ------------------------------------------------------------------------
  -- Pointwise Dominance: Bridge to Finite Horizons
  ------------------------------------------------------------------------

  -- Extract the n-th element of a reward stream
  iter-head : ℕ → StreamR → Reward
  iter-head zero    s = head s
  iter-head (suc n) s = iter-head n (tail s)

  -- Pointwise dominance: at every index, xₙ ≤ᵣ yₙ
  PointwiseDominance : StreamR → StreamR → Set
  PointwiseDominance x y = ∀ n → iter-head n x ≤ᵣ iter-head n y

  -- KEY LEMMA: coinductive ≤ₛ implies pointwise dominance
  ≤ₛ-to-pointwise : ∀ {x y} → x ≤ₛ y → PointwiseDominance x y
  ≤ₛ-to-pointwise p zero    = head≤ p
  ≤ₛ-to-pointwise p (suc n) = ≤ₛ-to-pointwise (tail≤ p) n

  ------------------------------------------------------------------------
  -- Partial Sums and Subsumption Theorem
  ------------------------------------------------------------------------

  -- Partial sum of first N elements of a stream
  partial-sum : ℕ → StreamR → Reward
  partial-sum zero    _ = bottom
  partial-sum (suc n) s = head s +ᵣ partial-sum n (tail s)

  -- SUBSUMPTION THEOREM TYPE:
  -- If action a is ranked ≤ action b, then for any horizon N,
  -- the partial sum of a's rewards ≤ partial sum of b's rewards
  SubsumesPartialSum : CoindHomo → Set
  SubsumesPartialSum homo = ∀ s a b N →
    CoindHomo._≤ₐ_ homo s a b →
    partial-sum N (action-value s a) ≤ᵣ partial-sum N (action-value s b)

  ------------------------------------------------------------------------
  -- Proof of Subsumption
  ------------------------------------------------------------------------

  -- Helper: shift pointwise dominance by one step
  private
    pointwise-tail : ∀ {x y} → PointwiseDominance x y → 
                     PointwiseDominance (tail x) (tail y)
    pointwise-tail pw n = pw (suc n)

  -- Helper: partial sum respects pointwise dominance
  partial-sum-mono : ∀ N x y → PointwiseDominance x y → 
                     partial-sum N x ≤ᵣ partial-sum N y
  partial-sum-mono zero _ _ _ = ≤ᵣ-refl
  partial-sum-mono (suc n) x y pw = 
    +ᵣ-mono-≤ (pw zero) (partial-sum-mono n (tail x) (tail y) (pointwise-tail pw))

  -- MAIN THEOREM: subsumption follows from preservation + pointwise lemma
  subsumes-partial-sum : (homo : CoindHomo) → SubsumesPartialSum homo
  subsumes-partial-sum homo s a b N ranking-says = 
    partial-sum-mono N (action-value s a) (action-value s b) pointwise
    where
      -- Step 1: preservation gives stream dominance
      stream-dom : action-value s a ≤ₛ action-value s b
      stream-dom = CoindHomo.preserves homo a b s ranking-says
      -- Step 2: convert to pointwise
      pointwise : PointwiseDominance (action-value s a) (action-value s b)
      pointwise = ≤ₛ-to-pointwise stream-dom

  ------------------------------------------------------------------------
  -- Corollary: Classical Argmax is Subsumed
  --
  -- If we have a CoindHomo and action b is ranked highest (∀ a. a ≤ₐ b),
  -- then for any horizon N, b has the highest partial sum.
  ------------------------------------------------------------------------

  ArgmaxSubsumed : CoindHomo → Set
  ArgmaxSubsumed homo = ∀ s b →
    (∀ a → CoindHomo._≤ₐ_ homo s a b) →  -- b is top-ranked
    ∀ a N → partial-sum N (action-value s a) ≤ᵣ partial-sum N (action-value s b)

  argmax-subsumed : (homo : CoindHomo) → ArgmaxSubsumed homo
  argmax-subsumed homo s b b-is-top a N = subsumes-partial-sum homo s a b N (b-is-top a)
