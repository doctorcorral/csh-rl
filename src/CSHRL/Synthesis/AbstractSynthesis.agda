{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Synthesis.AbstractSynthesis
--
-- Model-Free Verified Synthesis for Continuous Environments
--
-- This module bridges StateAbstraction (Core.Abstraction) and
-- the CEGIS synthesis loop (Synthesis.Core), enabling the full
-- CSHRL pipeline to operate on continuous state spaces without
-- requiring a dynamics model.
--
-- Architecture:
--   1. A StateAbstraction projects continuous states to a finite grid.
--   2. The learning loop interacts with the environment and produces
--      Samples (state, action_a, action_b).
--   3. Each Sample is projected to the grid: the concrete state c
--      becomes the abstract state (project c).
--   4. A comparison oracle (from environment interaction, not from
--      an ODE model) determines which action is better at c.
--   5. The projected observation (project c, compare c a b) feeds
--      into CEGIS on the abstract state space.
--   6. CEGIS synthesizes a verified ranking on the finite grid.
--   7. abstract-lift lifts the ranking to all concrete states.
--
-- Key theorem (obs-projection):
--   Any two concrete states in the same grid cell produce
--   IDENTICAL CEGIS observations (under marginal-invariance).
--   Therefore CEGIS convergence requires at most |Abstract|
--   observations — one per grid cell — regardless of |Concrete|.
--
-- This means: the CSHRL synthesis loop, which was designed for
-- finite discrete environments, extends unchanged to continuous
-- environments via state abstraction.  The "observations" come
-- from environment interaction (model-free), and the verified
-- ranking covers the entire continuous space (via abstract-lift).
--
-- Fragility, energy, or any ODE-derived reward is an OPTIMISATION:
-- it provides a comparison oracle that doesn't require interaction.
-- But the synthesis framework is sound without it.
------------------------------------------------------------------------

module CSHRL.Synthesis.AbstractSynthesis where

open import Data.Bool using (Bool)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; trans)

open import CSHRL.Core.Abstraction
  using (StateAbstraction)

------------------------------------------------------------------------
-- Projected Observation
--
-- A continuous sample (concrete state + comparison result) projects
-- to an abstract CEGIS observation via the state abstraction.
------------------------------------------------------------------------

module ProjectedObservation
  {Concrete Abstract : Set}
  (abs : StateAbstraction Concrete Abstract)
  (compare : Concrete → Bool)
  where

  open StateAbstraction abs

  -- The projected observation: abstract state + comparison result
  proj-obs : Concrete → Abstract × Bool
  proj-obs c = (project c , compare c)

  -- The representative observation: same, but at the cell representative
  rep-obs : Concrete → Abstract × Bool
  rep-obs c = (project (embed (project c)) , compare (embed (project c)))

  ------------------------------------------------------------------------
  -- Observation Projection Lemma
  --
  -- Under marginal-invariance, observing at ANY concrete state c
  -- gives the same CEGIS observation as observing at the cell's
  -- representative embed(project c).
  --
  -- Marginal-invariance says: if project c₁ ≡ project c₂, then
  -- compare c₁ ≡ compare c₂.  Since project(embed(project c)) ≡
  -- project c (by section), the comparison results agree.
  --
  -- Consequence: CEGIS sees at most |Abstract| distinct observations.
  -- The |C/~| sample complexity bound transfers from the abstract
  -- system, regardless of |Concrete|.
  ------------------------------------------------------------------------

  obs-projection :
    (invariant : ∀ c₁ c₂ → project c₁ ≡ project c₂ →
      compare c₁ ≡ compare c₂) →
    ∀ c → proj-obs c ≡ rep-obs c
  obs-projection invariant c =
    let eq-proj : project c ≡ project (embed (project c))
        eq-proj = sym (section (project c))
        eq-comp : compare c ≡ compare (embed (project c))
        eq-comp = invariant c (embed (project c)) eq-proj
    in cong₂ _,_ eq-proj eq-comp

------------------------------------------------------------------------
-- Cell-Invariant Observation
--
-- A stronger form: any two concrete states in the same cell
-- produce identical observations.  This is the form that directly
-- connects to CEGIS's exploration-dissolution theorem.
------------------------------------------------------------------------

module CellInvariance
  {Concrete Abstract : Set}
  (abs : StateAbstraction Concrete Abstract)
  (compare : Concrete → Bool)
  (invariant : ∀ c₁ c₂ → StateAbstraction.project abs c₁ ≡
                           StateAbstraction.project abs c₂ →
    compare c₁ ≡ compare c₂)
  where

  open StateAbstraction abs

  proj-obs : Concrete → Abstract × Bool
  proj-obs c = (project c , compare c)

  -- Any two concrete states in the same cell yield the same observation
  cell-obs-invariant : ∀ c₁ c₂ →
    project c₁ ≡ project c₂ →
    proj-obs c₁ ≡ proj-obs c₂
  cell-obs-invariant c₁ c₂ eq =
    cong₂ _,_ eq (invariant c₁ c₂ eq)

------------------------------------------------------------------------
-- Abstract Synthesis Record
--
-- Bundles the requirements for model-free continuous synthesis:
-- a state abstraction, a comparison oracle, and the invariance
-- condition that makes CEGIS well-defined on the abstract space.
--
-- The comparison oracle can be:
--   • Model-based: computed from an ODE in Agda (current approach)
--   • Model-free:  observed from environment interaction (general case)
-- The module is agnostic to the oracle's implementation.
------------------------------------------------------------------------

record AbstractSynthesisSetup
    (Concrete Abstract Action : Set) : Set₁ where
  field
    abs : StateAbstraction Concrete Abstract

    -- Comparison oracle: "is action b at least as good as action a
    -- at concrete state c?"  The result is a Bool.
    -- Source: environment interaction (model-free) or ODE (model-based).
    compare : Concrete → Action → Action → Bool

    -- Marginal-invariance: same grid cell → same comparison.
    -- This is the constructive analogue of Li et al.'s
    -- model-irrelevance condition.
    compare-invariant : ∀ c₁ c₂ →
      StateAbstraction.project abs c₁ ≡
      StateAbstraction.project abs c₂ →
      ∀ a b → compare c₁ a b ≡ compare c₂ a b

  open StateAbstraction abs public

  -- For a fixed action pair, the comparison induces a
  -- ProjectedObservation
  pair-compare : Action → Action → Concrete → Bool
  pair-compare a b c = compare c a b

  -- Projected observation for a specific action pair
  pair-obs : Action → Action → Concrete → Abstract × Bool
  pair-obs a b c = (project c , pair-compare a b c)

  -- Cell invariance for each action pair
  pair-cell-invariant : ∀ a b c₁ c₂ →
    project c₁ ≡ project c₂ →
    pair-obs a b c₁ ≡ pair-obs a b c₂
  pair-cell-invariant a b c₁ c₂ eq =
    cong₂ _,_ eq (compare-invariant c₁ c₂ eq a b)

  -- The representative observation equals the projected observation
  pair-obs-via-rep : ∀ a b c →
    pair-obs a b c ≡
    (project (embed (project c)) , compare (embed (project c)) a b)
  pair-obs-via-rep a b c =
    let eq-proj = sym (section (project c))
        eq-comp = compare-invariant c (embed (project c)) eq-proj a b
    in cong₂ _,_ eq-proj eq-comp

------------------------------------------------------------------------
-- Sample Projection
--
-- A Sample from the continuous environment consists of a concrete
-- state and an action pair.  Projecting it gives:
--   1. The abstract state (for CEGIS's Carrier)
--   2. The comparison result (for CEGIS's Bool)
--
-- This is the `to-obs` function for LearningBridge.
------------------------------------------------------------------------

module SampleProjection
  {Concrete Abstract Action : Set}
  (setup : AbstractSynthesisSetup Concrete Abstract Action)
  where

  open AbstractSynthesisSetup setup

  record ContinuousSample : Set where
    constructor c-sample
    field
      cs-state : Concrete
      cs-a     : Action
      cs-b     : Action

  -- Project a continuous sample to a CEGIS observation
  -- This is the `to-obs` for LearningBridge instantiation
  project-sample : ContinuousSample → Abstract × Bool
  project-sample (c-sample c a b) = pair-obs a b c

  -- Two samples from the same cell yield the same observation
  project-sample-invariant : ∀ c₁ c₂ a b →
    project c₁ ≡ project c₂ →
    project-sample (c-sample c₁ a b) ≡
    project-sample (c-sample c₂ a b)
  project-sample-invariant c₁ c₂ a b eq =
    pair-cell-invariant a b c₁ c₂ eq

------------------------------------------------------------------------
-- End-to-End Architecture (documented, not fully instantiated)
--
-- The complete model-free pipeline composes:
--
--   (a) SampleProjection provides `to-obs` for LearningBridge
--       → continuous samples become abstract CEGIS observations
--
--   (b) CEGIS (from PredicateDSL) runs on Abstract as Carrier
--       → synthesises a predicate program per action pair
--       → convergence in ≤ |Abstract| observations (by
--         cell-obs-invariant + exploration-dissolution)
--
--   (c) The synthesised predicates define a ranking on Abstract
--       → VerifiedRanking Abstract Action marginal k
--
--   (d) abstract-lift (from Core.Abstraction) lifts to Concrete
--       → VerifiedRanking Concrete Action marginal k
--
-- Steps (b)-(d) are existing modules.  This module provides (a)
-- and proves that the projection preserves the invariants
-- required by (b).
--
-- The comparison oracle is the only environment-dependent input.
-- It can come from:
--   • Rollouts: deploy action a, observe reward, compare
--   • ODE computation: Euler-integrate, compare next-state energy
--   • Fragility: compute minimax distance to terminal boundary
-- All three satisfy compare-invariant under the appropriate
-- marginal-invariance condition on the grid abstraction.
--
-- Partial policies:
-- Before CEGIS converges, the current version space already
-- encodes information from all observations so far.  Any
-- surviving predicate program is consistent with all observed
-- comparisons.  Deploying a partial ranking (from any survivor)
-- gives a policy that respects every observed preference —
-- a stronger guarantee than random, and one that improves
-- monotonically with each observation (by vs-shrinks).
------------------------------------------------------------------------
