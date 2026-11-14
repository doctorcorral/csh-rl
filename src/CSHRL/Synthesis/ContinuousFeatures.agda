{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Synthesis.ContinuousFeatures
--
-- Generic feature template for continuous-state environments.
--
-- Parameterized by:
--   • State type and number of dimensions
--   • Dimension accessor (get-dim : State → ℕ → ℤ)
--
-- Generates two families of predicates:
--
--   axis d t      →  x_d < t            (threshold on dimension d)
--   diag i j c    →  c · x_i + x_j < 0  (linear combination)
--
-- The feature pool is built from:
--   • axis-features: one per dimension per threshold value
--   • diag-features: one per ordered pair (i,j) per coefficient c
--
-- This is the continuous-state analogue of AutoFeatureNat:
--   thresholds ↔ bin boundaries      (like neurons per layer)
--   coefficients ↔ linear combos     (like connection weights)
--   PredProg depth ↔ network depth   (like number of layers)
--
-- Instantiation for CartPole:
--   2 dims, thresholds = [0], max-coeff = 10
--   → 2 axis + 20 diagonal = 22 candidate features
--
-- Integration: ContFeatures.DSL is a PredicateDSL instance
-- ready for CEGIS synthesis.
------------------------------------------------------------------------

module CSHRL.Synthesis.ContinuousFeatures where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat  as ℕ using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Integer.Base as ℤ
  using (ℤ; +_; -[1+_])
  renaming (_+_ to _+ℤ_; _*_ to _*ℤ_)
open import Data.Integer.Properties as ℤP
  using () renaming (_<?_ to _<?ℤ_)
open import Data.List using (List; []; _∷_; map; concatMap; _++_)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)

open import CSHRL.Synthesis.Core

module ContFeatures
  (State    : Set)
  (num-dims : ℕ)
  (get-dim  : State → ℕ → ℤ)
  where

  --------------------------------------------------------------------
  -- Feature type
  --------------------------------------------------------------------

  data CFeature : Set where
    axis : ℕ → ℤ → CFeature
    diag : ℕ → ℕ → ℤ → CFeature

  eval-cf : CFeature → State → Bool
  eval-cf (axis d t)   s with get-dim s d <?ℤ t
  ... | yes _ = true
  ... | no  _ = false
  eval-cf (diag i j c) s with (c *ℤ get-dim s i +ℤ get-dim s j) <?ℤ (+ 0)
  ... | yes _ = true
  ... | no  _ = false

  --------------------------------------------------------------------
  -- PredicateDSL instantiation
  --------------------------------------------------------------------

  module DSL = PredicateDSL State CFeature eval-cf

  --------------------------------------------------------------------
  -- Feature pool generation
  --------------------------------------------------------------------

  private
    range : ℕ → List ℕ
    range zero    = []
    range (suc n) = range n ++ (n ∷ [])

    coeff-range : ℕ → List ℤ
    coeff-range zero    = []
    coeff-range (suc n) = coeff-range n ++ (+ suc n ∷ -[1+ n ] ∷ [])

    ordered-pairs : List (ℕ × ℕ)
    ordered-pairs =
      concatMap (λ i →
        concatMap (λ j →
          if i ≡ᵇ j then [] else (i , j) ∷ [])
        (range num-dims))
      (range num-dims)

  axis-features : List ℤ → List CFeature
  axis-features ts = concatMap (λ d → map (axis d) ts) (range num-dims)

  diag-features : ℕ → List CFeature
  diag-features max-c =
    concatMap (λ { (i , j) → map (diag i j) (coeff-range max-c) })
             ordered-pairs

  gen-features : List ℤ → ℕ → List CFeature
  gen-features thresholds max-coeff =
    axis-features thresholds ++ diag-features max-coeff

  --------------------------------------------------------------------
  -- Adaptive feature generation from trajectory states
  --
  -- Given observed states, extracts per-dimension values, sorts and
  -- deduplicates them, and creates axis features at those thresholds.
  -- This makes threshold selection fully automatic: thresholds are
  -- derived from the states the agent actually visits.
  --------------------------------------------------------------------

  private
    insert-uniq : ℤ → List ℤ → List ℤ
    insert-uniq x [] = x ∷ []
    insert-uniq x (y ∷ ys) with x <?ℤ y
    ... | yes _ = x ∷ y ∷ ys
    ... | no  _ with y <?ℤ x
    ...   | yes _ = y ∷ insert-uniq x ys
    ...   | no  _ = y ∷ ys

    sort-dedup : List ℤ → List ℤ
    sort-dedup [] = []
    sort-dedup (x ∷ xs) = insert-uniq x (sort-dedup xs)

  traj-axis-features : List State → List CFeature
  traj-axis-features states =
    concatMap (λ d → map (axis d)
                         (sort-dedup (+ 0 ∷ map (λ s → get-dim s d) states)))
             (range num-dims)

  adaptive-features : ℕ → List State → List CFeature
  adaptive-features max-coeff states =
    traj-axis-features states ++ diag-features max-coeff

  --------------------------------------------------------------------
  -- Decision chain: generic k-action policy from PredProg predicates
  --
  -- A decision chain [(p₁, a₁), (p₂, a₂), ...] with default action
  -- aₖ evaluates predicates top-to-bottom.  The first predicate
  -- that fires selects its action; if none fire, the default is used.
  --
  --   k = 2: chain = [(p, Left)], default = Right
  --          ≡ if eval p s then Left else Right
  --
  --   k = 3: chain = [(p₁, A₁), (p₂, A₂)], default = A₃
  --          ≡ if eval p₁ s then A₁
  --            else if eval p₂ s then A₂
  --            else A₃
  --------------------------------------------------------------------

  module ActionChain (Action : Set) where

    Chain : Set
    Chain = List (DSL.PredProg × Action)

    eval-chain : Chain → Action → State → Action
    eval-chain []              def s = def
    eval-chain ((p , a) ∷ rest) def s with DSL.eval p s
    ... | true  = a
    ... | false = eval-chain rest def s
