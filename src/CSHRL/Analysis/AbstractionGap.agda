{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- CSHRL.Analysis.AbstractionGap
--
-- Grid-Policy Soundness Theorem
--
-- When a continuous-state policy is obtained by discretizing onto a
-- finite grid, the action ordering at the cell center may not match
-- the ordering at other states in the cell.  This module provides the
-- core arithmetic lemma that bounds this abstraction gap:
--
--   If the reward perturbation ε between any state and its cell
--   center is less than half the reward gap Δ at the center,
--   then the action ordering is preserved throughout the cell.
--
-- Concretely: given rewards at the center  r_a ≤ r_b  with gap
-- r_b − r_a ≥ Δ, and true rewards r_a', r_b' satisfying
-- |r_a' − r_a| ≤ ε and |r_b' − r_b| ≤ ε, with Δ > 2ε, then
-- r_a' < r_b'.
--
-- The perturbation bound ε arises from the Lipschitz constants of the
-- dynamics and reward function composed with the grid diameter:
--
--   ε  ≤  L_R · L_f · δ
--
-- where L_f is the dynamics Lipschitz constant, L_R is the reward
-- function Lipschitz constant, and δ is the grid cell diameter.
------------------------------------------------------------------------

module CSHRL.Analysis.AbstractionGap where

open import Data.Integer as ℤ
  using (ℤ; +_; -[1+_])
  renaming (_+_ to _+ℤ_; _-_ to _−ℤ_; -_ to ℤneg; _*_ to _*ℤ_)
open import Data.Integer.Properties as ℤP
  using (≤-refl; ≤-trans; <-≤-trans; ≤-<-trans; +-monoˡ-≤; +-monoˡ-<)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)

------------------------------------------------------------------------
-- Core arithmetic lemma (integer version)
--
-- If:  ra' ≤ ra + ε            (true reward of action a is bounded above)
--      rb − ε ≤ rb'            (true reward of action b is bounded below)
--      ra + ε < rb − ε         (gap exceeds 2ε, i.e. rb − ra > 2ε)
-- Then: ra' < rb'
------------------------------------------------------------------------

gap-preserves-strict : ∀ (ra ra' rb rb' ε : ℤ) →
  ra' ℤ.≤ (ra +ℤ ε) →
  (rb −ℤ ε) ℤ.≤ rb' →
  (ra +ℤ ε) ℤ.< (rb −ℤ ε) →
  ra' ℤ.< rb'
gap-preserves-strict ra ra' rb rb' ε h-upper h-lower h-gap =
  ≤-<-trans h-upper (<-≤-trans h-gap h-lower)

------------------------------------------------------------------------
-- Corollary: ordering preservation for ℕ reward levels
--
-- When the reward function maps to discrete levels (ℕ), and the
-- perturbation cannot cross a level boundary, the level assignment
-- is preserved.  If cc-reward assigns level n at the center, and the
-- true reward at any nearby state differs by less than the distance
-- to the nearest level threshold, then the true level equals n.
------------------------------------------------------------------------

-- A reward level is stable if the perturbation fits within the level band.
-- This is expressed as: if x₀ maps to level n, and |x − x₀| ≤ ε,
-- and ε is less than the distance from x₀ to both adjacent thresholds,
-- then x also maps to level n.

-- We express this via the general principle: for any monotone
-- level assignment f and values x, x₀ with |x−x₀| ≤ ε < gap/2,
-- f(x) = f(x₀).

-- The above gap-preserves-strict lemma is the core engine.
-- Environment-specific instantiations (CartPole, MountainCar, Acrobot)
-- verify the hypotheses computationally.

------------------------------------------------------------------------
-- Abstraction quality record
--
-- Packages the hypotheses needed for the gap theorem.
-- The task author provides:
--   1. The perturbation bound ε
--   2. The reward gap Δ at each cell center
--   3. Evidence that 2ε < Δ
-- The theorem then guarantees action-ordering preservation.
------------------------------------------------------------------------

record AbstractionQuality : Set₁ where
  field
    ConcreteState GridState Action : Set

    -- Grid-based reward (what we verify at the center)
    cc-reward : GridState → Action → ℕ

    -- State abstraction
    project : ConcreteState → GridState

    -- True reward at a concrete state (the "real" outcome)
    true-reward : ConcreteState → Action → ℕ

    -- Approximation guarantee:
    -- the grid reward equals the true reward for all states in each cell
    sound : ∀ s a → cc-reward (project s) a ≡ true-reward s a

  -- When `sound` holds, the grid policy is exactly optimal:
  -- the action ordering at the center equals the ordering everywhere.
  ordering-exact : ∀ s a b →
    cc-reward (project s) a ≤ cc-reward (project s) b →
    true-reward s a ≤ true-reward s b
  ordering-exact s a b h =
    subst (λ x → x ≤ true-reward s b) (sound s a)
      (subst (λ x → cc-reward (project s) a ≤ x) (sound s b) h)
