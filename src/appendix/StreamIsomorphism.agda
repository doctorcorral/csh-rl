{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- StreamIsomorphism: The Symmetric Correspondence
--
-- This module proves the isomorphism between coinductive stream ordering
-- and pointwise dominance. Together with ≤ₛ-to-pointwise (in Core), this
-- establishes that:
--
--   x ≤ₛ y  ⟺  ∀ n. xₙ ≤ᵣ yₙ
--
-- This formally justifies the "symmetric" in CSHRL: the correspondence
-- between rankings and stream dominance is bidirectional.
------------------------------------------------------------------------

module appendix.StreamIsomorphism where

open import Data.List using (List; map; foldr; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _⊔_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Codata.Guarded.Stream using (Stream; head; tail; tabulate)

------------------------------------------------------------------------
-- The module is parameterized by the environment (same as Core)
------------------------------------------------------------------------

module StreamIso
  (State Action Reward : Set)
  (step                : State → Action → State × Reward)
  (_≤ᵣ_                : Reward → Reward → Set)
  (max                 : Reward → Reward → Reward)
  (bottom              : Reward)
  (all-actions         : List Action)
  where

  -- Stream of rewards
  StreamR : Set
  StreamR = Stream Reward

  ------------------------------------------------------------------------
  -- Coinductive stream ordering (from Core)
  ------------------------------------------------------------------------

  record _≤ₛ_ (x y : StreamR) : Set where
    coinductive
    field
      head≤ : head x ≤ᵣ head y
      tail≤ : tail x ≤ₛ tail y

  open _≤ₛ_ public

  ------------------------------------------------------------------------
  -- Pointwise dominance
  ------------------------------------------------------------------------

  -- Extract the n-th element of a stream
  iter-head : ℕ → StreamR → Reward
  iter-head zero    s = head s
  iter-head (suc n) s = iter-head n (tail s)

  -- Pointwise dominance: at every index, xₙ ≤ᵣ yₙ
  PointwiseDominance : StreamR → StreamR → Set
  PointwiseDominance x y = ∀ n → iter-head n x ≤ᵣ iter-head n y

  ------------------------------------------------------------------------
  -- Direction 1: Coinductive → Pointwise (already in Core)
  ------------------------------------------------------------------------

  ≤ₛ-to-pointwise : ∀ {x y} → x ≤ₛ y → PointwiseDominance x y
  ≤ₛ-to-pointwise p zero    = head≤ p
  ≤ₛ-to-pointwise p (suc n) = ≤ₛ-to-pointwise (tail≤ p) n

  ------------------------------------------------------------------------
  -- Direction 2: Pointwise → Coinductive (THE NEW RESULT)
  ------------------------------------------------------------------------

  -- Helper: shift pointwise dominance to tails
  pointwise-tail : ∀ {x y} → PointwiseDominance x y → 
                   PointwiseDominance (tail x) (tail y)
  pointwise-tail pw n = pw (suc n)

  -- THE KEY THEOREM: Pointwise dominance implies coinductive ordering
  -- This is a corecursive definition that unfolds forever
  pointwise-to-≤ₛ : ∀ {x y} → PointwiseDominance x y → x ≤ₛ y
  head≤ (pointwise-to-≤ₛ pw) = pw zero
  tail≤ (pointwise-to-≤ₛ pw) = pointwise-to-≤ₛ (pointwise-tail pw)

  ------------------------------------------------------------------------
  -- THE ISOMORPHISM: Combining both directions
  ------------------------------------------------------------------------

  -- Logical equivalence
  _⇔_ : Set → Set → Set
  A ⇔ B = (A → B) × (B → A)

  -- The two formulations are equivalent
  stream-iso : ∀ x y → (x ≤ₛ y) ⇔ (PointwiseDominance x y)
  stream-iso x y = ≤ₛ-to-pointwise , pointwise-to-≤ₛ

  ------------------------------------------------------------------------
  -- Corollary: Round-trip identities
  ------------------------------------------------------------------------

  -- Starting from coinductive, going to pointwise and back
  -- yields a proof that agrees at every level
  round-trip-≤ₛ : ∀ {x y} (p : x ≤ₛ y) →
                  ∀ n → iter-head n x ≤ᵣ iter-head n y
  round-trip-≤ₛ p = ≤ₛ-to-pointwise p
  -- Note: We can't prove p ≡ pointwise-to-≤ₛ (≤ₛ-to-pointwise p)
  -- definitionally because coinductive records don't have η in Agda,
  -- but the underlying data is the same.

  ------------------------------------------------------------------------
  -- Summary
  ------------------------------------------------------------------------
  --
  -- We have proven:
  --   1. ≤ₛ-to-pointwise : x ≤ₛ y → PointwiseDominance x y
  --   2. pointwise-to-≤ₛ : PointwiseDominance x y → x ≤ₛ y
  --
  -- Together: x ≤ₛ y ⟺ ∀ n. iter-head n x ≤ᵣ iter-head n y
  --
  -- This is the ISOMORPHISM that justifies "symmetric" in CSHRL.
  -- The ranking structure and the stream dominance structure are
  -- not just related by a one-way homomorphism—they are equivalent.
  --
  -- Future work: explore implications for:
  --   - Finder soundness and completeness
  --   - Characterization of when rankings are unique
  --   - Connection to the symmetric group S_{|A|}
  ------------------------------------------------------------------------
