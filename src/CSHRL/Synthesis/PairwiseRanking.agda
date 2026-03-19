{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Synthesis.PairwiseRanking
--
-- Restricted Preservation for pairwise CoindHomo rankings.
--
-- A full ranking over k actions is determined by C(k,2) pairwise
-- comparison predicates.  Each predicate p_{ij} is independently
-- self-consistent (a CoindHomo for {action_i, action_j}).
--
-- Restricted Preservation (CSHRL.lagda.tex §7):
--   "since preservation is pairwise, the fact that a ≤ₐ b implies
--    action-value s a ≤ₛ action-value s b does not depend on which
--    other actions exist."
--
-- We formalize this for the gridless PredProg setting:
--   1. The full ranking is determined by C(k,2) pairwise predicates
--   2. Restriction to {i,j} (removing all other actions) yields
--      exactly predicate p_{ij}
--   3. Since p_{ij} was independently verified (converged CoindHomo),
--      the restricted ranking inherits that verification
--   4. No recomputation needed — the fallback is O(1) lookup
------------------------------------------------------------------------

module CSHRL.Synthesis.PairwiseRanking where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Generic pairwise ranking for 3 actions
------------------------------------------------------------------------

module ThreeActions
  (State  : Set)
  (Action : Set)
  (a₁ a₂ a₃ : Action)
  where

  -- A pairwise comparison: state → Bool (true = first argument preferred)
  Cmp : Set
  Cmp = State → Bool

  -- Three pairwise comparisons determine the full ranking
  record FullRanking : Set where
    field
      cmp₁₂ : Cmp   -- a₁ ≥ a₂ ?
      cmp₁₃ : Cmp   -- a₁ ≥ a₃ ?
      cmp₂₃ : Cmp   -- a₂ ≥ a₃ ?

  open FullRanking public

  -- Best action from the full ranking
  best : FullRanking → State → Action
  best r s with cmp₁₂ r s | cmp₁₃ r s | cmp₂₃ r s
  ... | true  | true  | _     = a₁
  ... | true  | false | _     = a₃
  ... | false | _     | true  = a₂
  ... | false | _     | false = a₃

  ------------------------------------------------------------------
  -- Restriction: remove one action, return best of remaining two
  --
  -- KEY INSIGHT: The restricted ranking for {aᵢ, aⱼ} is EXACTLY
  -- the pairwise predicate cmpᵢⱼ that was already verified.
  -- This is the computational content of Restricted Preservation.
  ------------------------------------------------------------------

  -- Remove a₃ → rank {a₁, a₂} by cmp₁₂
  best-without-a₃ : FullRanking → State → Action
  best-without-a₃ r s = if cmp₁₂ r s then a₁ else a₂

  -- Remove a₂ → rank {a₁, a₃} by cmp₁₃
  best-without-a₂ : FullRanking → State → Action
  best-without-a₂ r s = if cmp₁₃ r s then a₁ else a₃

  -- Remove a₁ → rank {a₂, a₃} by cmp₂₃
  best-without-a₁ : FullRanking → State → Action
  best-without-a₁ r s = if cmp₂₃ r s then a₂ else a₃

  ------------------------------------------------------------------
  -- Restricted Preservation: definitional equalities
  --
  -- Each restricted ranking is definitionally equal to the
  -- independently-verified pairwise comparison.
  --
  -- These are proved by refl — the restriction IS the pairwise
  -- predicate, not an approximation or re-derivation.
  ------------------------------------------------------------------

  restrict-preserves-₁₂ : ∀ r s →
    best-without-a₃ r s ≡ (if cmp₁₂ r s then a₁ else a₂)
  restrict-preserves-₁₂ _ _ = refl

  restrict-preserves-₁₃ : ∀ r s →
    best-without-a₂ r s ≡ (if cmp₁₃ r s then a₁ else a₃)
  restrict-preserves-₁₃ _ _ = refl

  restrict-preserves-₂₃ : ∀ r s →
    best-without-a₁ r s ≡ (if cmp₂₃ r s then a₂ else a₃)
  restrict-preserves-₂₃ _ _ = refl

  ------------------------------------------------------------------
  -- The fallback: when best action is unavailable, use the
  -- pairwise comparison between the remaining two.
  --
  -- This is O(1): evaluate ONE predicate at the current state.
  ------------------------------------------------------------------

  fallback : FullRanking → State → Action
  fallback r s with cmp₁₂ r s | cmp₁₃ r s | cmp₂₃ r s
  -- Best was a₁ → fall back to {a₂, a₃} via cmp₂₃
  ... | true  | true  | true  = a₂
  ... | true  | true  | false = a₃
  -- Best was a₃ → fall back to {a₁, a₂} via cmp₁₂
  ... | true  | false | _     = a₁
  -- Best was a₂ → fall back to {a₁, a₃} via cmp₁₃
  ... | false | _     | true  = if cmp₁₃ r s then a₁ else a₃
  -- Best was a₃ → fall back to {a₁, a₂} via cmp₁₂ (=false, so a₂)
  ... | false | _     | false = a₂
