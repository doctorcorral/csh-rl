{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Synthesis.DynFeatureTemplate
--
-- Feature Template Language for FINITE-STATE MDPs.
--
-- States in FDMDPs are atomic (finite enumerable types), not structured
-- like List ℕ.  Features are derived from the DYNAMICS: the step
-- function gives states meaning.
--
-- Two template families:
--
--   has-pos-reward a  — does action a from this state yield reward > 0?
--   is-self-loop a    — does action a return to this state?
--
-- These are domain-agnostic: they apply to ANY finite-state MDP.
-- Domain concepts emerge from filtering: for the Maze, is-self-loop Fwd
-- evaluates identically to the hand-crafted is-goal.
------------------------------------------------------------------------

module CSHRL.Synthesis.DynFeatureTemplate where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.List using (List; []; _∷_; length; map; _++_)

module DynFTL
  {State : Set} {Action : Set}
  (next       : State → Action → State)
  (pos-reward? : State → Action → Bool)
  (_≟ₛ_       : State → State → Bool)
  (all-actions : List Action)
  (all-states  : List State)
  where

  data DynFeature : Set where
    has-pos-reward : Action → DynFeature
    is-self-loop   : Action → DynFeature

  eval-dyn : DynFeature → State → Bool
  eval-dyn (has-pos-reward a) s = pos-reward? s a
  eval-dyn (is-self-loop a)   s = s ≟ₛ next s a

  enumerate-dyn : List DynFeature
  enumerate-dyn = map has-pos-reward all-actions ++ map is-self-loop all-actions

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

  is-nontrivial : DynFeature → Bool
  is-nontrivial f =
    let vals = map (eval-dyn f) all-states
    in not (all-true-list vals) ∧ not (all-false-list vals)

  filter-nontrivial : List DynFeature → List DynFeature
  filter-nontrivial = bfilter is-nontrivial

  feature-vector : List DynFeature → State → List Bool
  feature-vector []       _ = []
  feature-vector (f ∷ fs) s = eval-dyn f s ∷ feature-vector fs s
