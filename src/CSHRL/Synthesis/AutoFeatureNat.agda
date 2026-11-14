{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Synthesis.AutoFeatureNat
--
-- Automatic Feature Template Language for ℕ-state FDMDPs.
--
-- Given ONLY the state count, action type, and step function,
-- generates a complete feature set with ZERO human engineering:
--
--   (a) State identity:   state-is k        — one-hot per state
--   (b) Factorization:    mod-is w k         — s mod w ≡ k
--                         div-is w k         — s / w ≡ k
--       for each non-trivial divisor w of num-states.
--       For grid environments, these AUTOMATICALLY discover
--       row/column coordinates (e.g., div-is 4 k = row-is k
--       for a 4-column grid).
--   (c) Dynamics:         has-pos-reward a   — positive reward?
--                         is-self-loop a     — action returns to same state?
--                         leads-terminal a   — action leads to terminal state?
--   (d) Thresholds:       state-ge k         — s ≥ k
--                         mod-ge w k         — s mod w ≥ k
--                         div-ge w k         — s / w ≥ k
--       Threshold features express REGIONS rather than exact matches,
--       enabling policies like "go right if left of column 3" with a
--       single atom instead of OR-ing multiple mod-is features.
--
-- Two enumeration modes:
--   enumerate-auto      — identity + factorization + dynamics (base)
--   enumerate-enriched  — base + threshold features (richer)
--
-- Non-trivial filtering removes constant features.
-- The surviving features feed directly into CEGIS for synthesis.
--
-- All --safe, no postulates.
------------------------------------------------------------------------

module CSHRL.Synthesis.AutoFeatureNat where

open import Data.Bool using (Bool; true; false; not; if_then_else_; _∧_; _∨_)
open import Data.Nat  using (ℕ; zero; suc; _+_; _*_; _∸_; _≡ᵇ_; _<ᵇ_; _≤ᵇ_)
open import Data.List using (List; []; _∷_; map; _++_; concatMap; length)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import CSHRL.Utils.NatArithmetic public using (divℕ; modℕ; range)

private
  divs-go : ℕ → ℕ → ℕ → List ℕ
  divs-go zero       _ _ = []
  divs-go (suc fuel) k n =
    if k <ᵇ n
    then (if modℕ n k ≡ᵇ 0
          then k ∷ divs-go fuel (suc k) n
          else divs-go fuel (suc k) n)
    else []

find-divisors : ℕ → List ℕ
find-divisors n = divs-go n 2 n

------------------------------------------------------------------------
-- Auto-FTL module for ℕ-state FDMDPs
------------------------------------------------------------------------

module AutoFTL
  (Action      : Set)
  (step        : ℕ → Action → ℕ × ℕ)
  (all-actions : List Action)
  (num-states  : ℕ)
  (is-terminal : ℕ → Bool)
  where

  private
    geᵇ : ℕ → ℕ → Bool
    geᵇ m n = n ≤ᵇ m

    range-from : ℕ → ℕ → List ℕ
    range-from _ zero    = []
    range-from k (suc n) = k ∷ range-from (suc k) n

  data AutoFeature : Set where
    state-is       : ℕ → AutoFeature
    mod-is         : ℕ → ℕ → AutoFeature
    div-is         : ℕ → ℕ → AutoFeature
    has-pos-reward : Action → AutoFeature
    is-self-loop   : Action → AutoFeature
    leads-terminal : Action → AutoFeature
    state-ge       : ℕ → AutoFeature
    mod-ge         : ℕ → ℕ → AutoFeature
    div-ge         : ℕ → ℕ → AutoFeature

  eval-auto : AutoFeature → ℕ → Bool
  eval-auto (state-is k)       s = s ≡ᵇ k
  eval-auto (mod-is w k)       s = modℕ s w ≡ᵇ k
  eval-auto (div-is w k)       s = divℕ s w ≡ᵇ k
  eval-auto (has-pos-reward a)  s = not (proj₂ (step s a) ≡ᵇ 0)
  eval-auto (is-self-loop a)   s = proj₁ (step s a) ≡ᵇ s
  eval-auto (leads-terminal a) s = is-terminal (proj₁ (step s a))
  eval-auto (state-ge k)       s = geᵇ s k
  eval-auto (mod-ge w k)       s = geᵇ (modℕ s w) k
  eval-auto (div-ge w k)       s = geᵇ (divℕ s w) k

  divisors : List ℕ
  divisors = find-divisors num-states

  factor-features : ℕ → List AutoFeature
  factor-features w =
    map (mod-is w) (range w) ++
    map (div-is w) (range (divℕ num-states w))

  enumerate-auto : List AutoFeature
  enumerate-auto =
    map state-is (range num-states) ++
    concatMap factor-features divisors ++
    map has-pos-reward all-actions ++
    map is-self-loop all-actions ++
    map leads-terminal all-actions

  private
    all-true-list : List Bool → Bool
    all-true-list []           = true
    all-true-list (false ∷ _)  = false
    all-true-list (true ∷ xs)  = all-true-list xs

    all-false-list : List Bool → Bool
    all-false-list []          = true
    all-false-list (true ∷ _)  = false
    all-false-list (false ∷ xs) = all-false-list xs

    bfilter : ∀ {A : Set} → (A → Bool) → List A → List A
    bfilter _ []       = []
    bfilter p (x ∷ xs) = if p x then x ∷ bfilter p xs else bfilter p xs

  is-nontrivial : AutoFeature → Bool
  is-nontrivial f =
    let vals = map (eval-auto f) (range num-states)
    in not (all-true-list vals) ∧ not (all-false-list vals)

  discovered : List AutoFeature
  discovered = bfilter is-nontrivial enumerate-auto

  ------------------------------------------------------------------------
  -- Threshold feature enumeration
  --
  -- state-ge k    for k ∈ {1, ..., num-states − 1}
  -- mod-ge w k    for k ∈ {1, ..., w − 1}       (per divisor w)
  -- div-ge w k    for k ∈ {1, ..., max-quotient} (per divisor w)
  --
  -- k = 0 is always true (trivial), so excluded from enumeration.
  ------------------------------------------------------------------------

  threshold-factor : ℕ → List AutoFeature
  threshold-factor w =
    map (mod-ge w) (range-from 1 (w ∸ 1)) ++
    map (div-ge w) (range-from 1 (divℕ (num-states ∸ 1) w))

  threshold-features : List AutoFeature
  threshold-features =
    map state-ge (range-from 1 (num-states ∸ 1)) ++
    concatMap threshold-factor divisors

  enumerate-enriched : List AutoFeature
  enumerate-enriched = enumerate-auto ++ threshold-features

  -- Compact: factorization + thresholds + dynamics, NO state-is.
  -- For large state spaces (> ~64 states) where one-hot features
  -- bloat the version space without adding discriminative power.
  enumerate-compact : List AutoFeature
  enumerate-compact =
    concatMap factor-features divisors ++
    threshold-features ++
    map has-pos-reward all-actions ++
    map is-self-loop all-actions ++
    map leads-terminal all-actions

  discovered-enriched : List AutoFeature
  discovered-enriched = bfilter is-nontrivial enumerate-enriched

  discovered-compact : List AutoFeature
  discovered-compact = bfilter is-nontrivial enumerate-compact
