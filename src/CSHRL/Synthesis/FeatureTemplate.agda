{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Synthesis.FeatureTemplate
--
-- Feature Template Language (FTL) for List ℕ states.
--
-- Generates features from GENERIC arithmetic comparison templates,
-- not domain-specific concepts.  Four template families:
--
--   vals-eq i j    — do elements at positions i, j share the same value?
--   spread-eq i j  — does |value[i] − value[j]| equal |i − j|?
--   pair-any i j   — vals-eq ∨ spread-eq (composite pairwise test)
--   len-is n       — does the list have exactly n elements?
--
-- These are domain-agnostic structural comparisons on indexed data.
-- Domain concepts (e.g. N-Queens "attacks") EMERGE as combinations
-- discovered by filtering and redundancy elimination.
--
-- Three-stage discovery pipeline:
--   1. Enumerate all features for N indices
--   2. Filter against alive samples (keep conflict indicators)
--   3. Eliminate redundant atomics subsumed by composites
--
-- Integration: the generated ListNatFeature type plugs directly into
-- PredicateDSL as the Feature parameter.
------------------------------------------------------------------------

module CSHRL.Synthesis.FeatureTemplate where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.Nat  using (ℕ; zero; suc; _+_; _∸_; _≡ᵇ_)
open import Data.List using (List; []; _∷_; length; map; concatMap; _++_)
open import Data.Product using (_×_; _,_)

------------------------------------------------------------------------
-- Utilities
------------------------------------------------------------------------

safe-index : List ℕ → ℕ → ℕ
safe-index []       _ = 0
safe-index (x ∷ _)  zero    = x
safe-index (_ ∷ xs) (suc n) = safe-index xs n

has-index : List ℕ → ℕ → Bool
has-index []       _       = false
has-index (_ ∷ _)  zero    = true
has-index (_ ∷ xs) (suc n) = has-index xs n

abs-diff : ℕ → ℕ → ℕ
abs-diff x y = (x ∸ y) + (y ∸ x)

------------------------------------------------------------------------
-- Feature type
------------------------------------------------------------------------

data ListNatFeature : Set where
  vals-eq    : ℕ → ℕ → ListNatFeature
  spread-eq  : ℕ → ℕ → ListNatFeature
  pair-any   : ℕ → ℕ → ListNatFeature
  len-is     : ℕ → ListNatFeature

eval-list-feature : ListNatFeature → List ℕ → Bool
eval-list-feature (vals-eq i j) xs =
  has-index xs i ∧ has-index xs j ∧ (safe-index xs i ≡ᵇ safe-index xs j)
eval-list-feature (spread-eq i j) xs =
  has-index xs i ∧ has-index xs j ∧
  (abs-diff (safe-index xs i) (safe-index xs j) ≡ᵇ abs-diff i j)
eval-list-feature (pair-any i j) xs =
  has-index xs i ∧ has-index xs j ∧
  ((safe-index xs i ≡ᵇ safe-index xs j) ∨
   (abs-diff (safe-index xs i) (safe-index xs j) ≡ᵇ abs-diff i j))
eval-list-feature (len-is n) xs = length xs ≡ᵇ n

------------------------------------------------------------------------
-- Enumeration
------------------------------------------------------------------------

range-from : ℕ → ℕ → List ℕ
range-from _ zero    = []
range-from a (suc k) = a ∷ range-from (suc a) k

all-pairs : ℕ → List (ℕ × ℕ)
all-pairs n =
  concatMap (λ i → map (i ,_) (range-from (suc i) (n ∸ suc i)))
            (range-from 0 n)

enumerate-pairwise : ℕ → List ListNatFeature
enumerate-pairwise n =
  concatMap pair-feats (all-pairs n)
  where
    pair-feats : ℕ × ℕ → List ListNatFeature
    pair-feats (i , j) = vals-eq i j ∷ spread-eq i j ∷ pair-any i j ∷ []

enumerate-length : ℕ → List ListNatFeature
enumerate-length n = map len-is (range-from 0 (suc n))

enumerate-all : ℕ → List ListNatFeature
enumerate-all n = enumerate-pairwise n ++ enumerate-length n

------------------------------------------------------------------------
-- Filtering: conflict indicator discovery
------------------------------------------------------------------------

all-false-on : ListNatFeature → List (List ℕ) → Bool
all-false-on _ []          = true
all-false-on f (xs ∷ xss) = not (eval-list-feature f xs) ∧ all-false-on f xss

bfilter : ∀ {A : Set} → (A → Bool) → List A → List A
bfilter _ []       = []
bfilter p (x ∷ xs) = if p x then x ∷ bfilter p xs else bfilter p xs

filter-by-alive : List (List ℕ) → List ListNatFeature → List ListNatFeature
filter-by-alive alive = bfilter (λ f → all-false-on f alive)

------------------------------------------------------------------------
-- Redundancy elimination
--
-- An atomic feature (vals-eq i j or spread-eq i j) is SUBSUMED by
-- the composite (pair-any i j) for the same pair: whenever the
-- atomic fires, the composite also fires.  Eliminating subsumed
-- atomics discovers intermediate concepts (e.g. "conflict = same-col
-- OR same-diag") as composite features.
------------------------------------------------------------------------

is-subsumed-by : ListNatFeature → ListNatFeature → Bool
is-subsumed-by (vals-eq i j)   (pair-any i' j') = (i ≡ᵇ i') ∧ (j ≡ᵇ j')
is-subsumed-by (spread-eq i j) (pair-any i' j') = (i ≡ᵇ i') ∧ (j ≡ᵇ j')
is-subsumed-by _               _                = false

any-subsumes-in : List ListNatFeature → ListNatFeature → Bool
any-subsumes-in []       _ = false
any-subsumes-in (g ∷ gs) f = is-subsumed-by f g ∨ any-subsumes-in gs f

eliminate-redundant : List ListNatFeature → List ListNatFeature
eliminate-redundant fs = bfilter (λ f → not (any-subsumes-in fs f)) fs

------------------------------------------------------------------------
-- Is-solved discovery
--
-- Dual of conflict indicators: keep features that are TRUE on all
-- solved samples and FALSE on all non-solved samples.
------------------------------------------------------------------------

all-true-on : ListNatFeature → List (List ℕ) → Bool
all-true-on _ []          = true
all-true-on f (xs ∷ xss) = eval-list-feature f xs ∧ all-true-on f xss

filter-solved : List (List ℕ) → List (List ℕ) → List ListNatFeature → List ListNatFeature
filter-solved solved non-solved =
  bfilter (λ f → all-true-on f solved ∧ all-false-on f non-solved)

------------------------------------------------------------------------
-- Feature vectors and equivalence classes
--
-- A feature vector maps a carrier to its Boolean fingerprint under
-- a feature set.  Two carriers with the same vector are in the same
-- equivalence class.  |C/~| = number of distinct vectors.
------------------------------------------------------------------------

feature-vector : List ListNatFeature → List ℕ → List Bool
feature-vector []       _ = []
feature-vector (f ∷ fs) xs = eval-list-feature f xs ∷ feature-vector fs xs

private
  beq : Bool → Bool → Bool
  beq true  true  = true
  beq false false = true
  beq _     _     = false

  list-beq : List Bool → List Bool → Bool
  list-beq []         []         = true
  list-beq (b₁ ∷ bs₁) (b₂ ∷ bs₂) = beq b₁ b₂ ∧ list-beq bs₁ bs₂
  list-beq _          _          = false

  is-new : List Bool → List (List Bool) → Bool
  is-new _ []       = true
  is-new v (w ∷ ws) = if list-beq v w then false else is-new v ws

  collect-distinct : List (List Bool) → List (List Bool)
  collect-distinct []       = []
  collect-distinct (v ∷ vs) =
    let ds = collect-distinct vs
    in if is-new v ds then v ∷ ds else ds

equiv-classes : List ListNatFeature → List (List ℕ) → ℕ
equiv-classes feats boards =
  length (collect-distinct (map (feature-vector feats) boards))
