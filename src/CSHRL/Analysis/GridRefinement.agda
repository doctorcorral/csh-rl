{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Analysis.GridRefinement
--
-- Violation-Guided Abstraction Refinement (CEGAR for Grids)
--
-- Connects CSHRL's violation-guided learning to abstraction refinement:
-- a ranking violation at a concrete state s identifies a grid cell
-- where the abstraction is too coarse.  Splitting that cell and
-- re-verifying produces a finer grid where the violation is resolved.
--
-- The key observation: compose-abstraction already captures the
-- relationship between fine and coarse grids.  If
--
--   C  →[α₁]  Fine  →[coarsen]  Coarse
--
-- then compose-abstraction α₁ (refinement-abstraction rw) gives
-- a StateAbstraction C Coarse.  A VerifiedRanking on Fine lifts to C
-- via abstract-lift, giving a correct policy at ALL concrete states —
-- including those where the coarse ranking had violations.
--
-- Architecture:
--   1. Start with any grid (even a 2-state minimal grid)
--   2. Verify ranking on the grid (cc-reward + refl)
--   3. Deploy — observe violations at concrete states
--   4. A violation at s in cell g means: the ranking at g is wrong for s
--      → split g into sub-cells
--   5. Re-verify on the finer grid (new cc-reward + refl)
--   6. abstract-lift on the fine grid yields a correct concrete ranking
--   7. Repeat until no violations remain
--
-- Fragility, energy, or any other reward metric is an OPTIMISATION:
-- it provides a good initial reward that reduces the number of
-- refinement rounds.  The refinement loop itself needs only
-- a violation oracle (deployment observations).
------------------------------------------------------------------------

module CSHRL.Analysis.GridRefinement where

open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; subst)

open import CSHRL.Probability.Finite using (Dist)
open import CSHRL.Probability.SD using (_SD[_]≤_)
open import CSHRL.Core.Compose using (VerifiedRanking)
open import CSHRL.Core.Abstraction
  using (StateAbstraction; abstract-lift; compose-abstraction)

------------------------------------------------------------------------
-- Refinement Witness
--
-- A refinement witness relates a fine grid to a coarse grid.
-- Every fine cell maps to exactly one coarse cell (coarsen),
-- and every coarse cell has at least one fine cell (embed-coarse).
------------------------------------------------------------------------

record RefinementWitness (Fine Coarse : Set) : Set where
  field
    coarsen       : Fine → Coarse
    embed-coarse  : Coarse → Fine
    coarsen-section : ∀ g → coarsen (embed-coarse g) ≡ g

------------------------------------------------------------------------
-- A refinement witness IS a state abstraction (Fine → Coarse)
------------------------------------------------------------------------

refinement-abstraction :
  ∀ {Fine Coarse : Set} →
  RefinementWitness Fine Coarse →
  StateAbstraction Fine Coarse
refinement-abstraction rw = record
  { project = RefinementWitness.coarsen rw
  ; embed   = RefinementWitness.embed-coarse rw
  ; section = RefinementWitness.coarsen-section rw
  }

------------------------------------------------------------------------
-- Refinement Lift
--
-- The core theorem: if the fine grid has a correct ranking (verified
-- by abstract-lift from C → Fine), then the ranking is correct for
-- ALL concrete states — including those where the coarse ranking
-- had violations.
--
-- This is just abstract-lift applied to the fine abstraction.
-- The refinement witness is used to CONSTRUCT the fine abstraction
-- from the coarse one + cell splits; the lifting theorem is unchanged.
------------------------------------------------------------------------

refine-lift :
  ∀ {Concrete Fine Action : Set}
    {m : Concrete → Action → ℕ → Dist ℕ}
    {k : ℕ} →
  (fine-abs : StateAbstraction Concrete Fine) →
  (invariant : ∀ c₁ c₂ →
    StateAbstraction.project fine-abs c₁ ≡
    StateAbstraction.project fine-abs c₂ →
    ∀ a n → m c₁ a n ≡ m c₂ a n) →
  VerifiedRanking Fine Action
    (λ g a n → m (StateAbstraction.embed fine-abs g) a n) k →
  VerifiedRanking Concrete Action m k
refine-lift = abstract-lift

------------------------------------------------------------------------
-- Coherent Refinement
--
-- A refinement is coherent when the fine projection, followed by
-- coarsening, equals the coarse projection.  This ensures that
-- splitting cells doesn't move states between coarse cells.
------------------------------------------------------------------------

record CoherentRefinement
    (Concrete Fine Coarse : Set) : Set where
  field
    fine-abs   : StateAbstraction Concrete Fine
    coarse-abs : StateAbstraction Concrete Coarse
    witness    : RefinementWitness Fine Coarse
    coherent   : ∀ c →
      RefinementWitness.coarsen witness
        (StateAbstraction.project fine-abs c) ≡
      StateAbstraction.project coarse-abs c

------------------------------------------------------------------------
-- Composition: coherent refinement yields a composed abstraction
--
-- compose-abstraction (fine-abs) (refinement-abstraction witness)
-- gives a StateAbstraction C Coarse that is compatible with coarse-abs.
------------------------------------------------------------------------

coherent-compose :
  ∀ {C F G : Set} →
  CoherentRefinement C F G →
  StateAbstraction C G
coherent-compose cr =
  compose-abstraction
    (CoherentRefinement.fine-abs cr)
    (refinement-abstraction (CoherentRefinement.witness cr))

------------------------------------------------------------------------
-- CEGAR Interpretation
--
-- The following is the DESIGN PATTERN, not a single theorem:
--
-- Step 1: Start with coarse-abs : StateAbstraction C Coarse
--         and a VerifiedRanking on Coarse.
--
-- Step 2: Deploy: for each concrete state s encountered,
--         use decide(s) = decide-grid(project coarse-abs s).
--
-- Step 3: Observe a violation at concrete state s:
--         the ranking says action a ≤ b at project(s),
--         but the observed outcome shows a > b.
--
-- Step 4: This means the cell project(s) is too coarse.
--         Split it: define Fine with more constructors,
--         define fine-abs : StateAbstraction C Fine,
--         define witness : RefinementWitness Fine Coarse.
--
-- Step 5: Re-compute cc-reward on the fine grid.
--         Verify ranking on Fine (refl checks).
--         Use refine-lift to get VerifiedRanking on C.
--
-- Step 6: The violation at s is now resolved because
--         the fine cell containing s has a correct ranking.
--
-- Step 7: Return to Step 2 with the fine grid.
--
-- Termination: each split strictly increases |Fine|.
--   For environments where a finite grid suffices (all three of
--   our benchmarks), the process terminates.
--
-- Fragility / energy are OPTIMISATIONS: they provide reward signals
-- that make the initial ranking correct on the first attempt,
-- reducing the number of refinement rounds to zero.
------------------------------------------------------------------------
