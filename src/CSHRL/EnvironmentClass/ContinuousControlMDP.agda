{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.EnvironmentClass.ContinuousControlMDP
--
-- Reusable Environment Class for continuous-state control problems.
--
-- The task author provides:
--   • Domain types (ConcreteState, Action, GridState)
--   • Dynamics (next-state on the grid)
--   • State abstraction (project, embed, section)
--   • Reward configuration (frag-to-reward, reward-level, monotonicity)
--   • Policy (decide-grid)
--
-- The EC automatically provides:
--   • Fragility computation (via ComputeFragility)
--   • Abstract step function
--   • FOSD synthesis layer (fosd-compare)
--   • Marginal reward distributions
--   • Auto-derived action ordering from fragility comparison
--   • Verified abstract ranking (from reward monotonicity)
--   • Lifted continuous ranking (via abstract-lift)
--   • Deployable controller (decide = decide-grid ∘ project)
--
-- The ordering proof reduces from O(|S|·|A|²) cases to O(L²) cases,
-- where L is the number of distinct reward levels (typically 3–5).
--
-- All --safe, no postulates.
------------------------------------------------------------------------

module CSHRL.EnvironmentClass.ContinuousControlMDP where

open import Data.Bool using (Bool)
open import Data.Nat using (ℕ; _≤_)
open import Data.List using (List)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; subst)
open import Relation.Nullary using (Dec)

open import CSHRL.Probability.Finite using (Dist; pure)
open import CSHRL.Probability.SD using (_SD[_]≤_)
open import CSHRL.Probability.FOSD using (_FOSD≤_)
open import CSHRL.Core.Compose using (VerifiedRanking)
open import CSHRL.Core.Abstraction using (StateAbstraction; abstract-lift)
open import CSHRL.Analysis.Fragility

import CSHRL.Synthesis.FOSDStochasticFiniteMDP as FOSD-Synth

------------------------------------------------------------------------
-- Parameters record
--
-- Everything the task author must supply.
------------------------------------------------------------------------

record CCParameters : Set₁ where
  field
    ConcreteState Action GridState : Set
    _≟g_           : (s₁ s₂ : GridState) → Dec (s₁ ≡ s₂)
    all-actions    : List Action
    default-action : Action
    all-grid-states : List GridState
    terminal?      : GridState → Bool
    next-state     : GridState → Action → GridState

    project : ConcreteState → GridState
    embed   : GridState → ConcreteState
    section : ∀ g → project (embed g) ≡ g

    frag-to-reward     : ℕ → ℕ
    reward-level       : ℕ → Dist ℕ
    reward-level-mono  : ∀ m n → m ≤ n →
                         reward-level m FOSD≤ reward-level n

    decide-grid : GridState → Action

------------------------------------------------------------------------
-- Everything the EC provides
------------------------------------------------------------------------

module ContinuousControl (P : CCParameters) where

  open CCParameters P

  --------------------------------------------------------------------
  -- Fragility: auto-computed from the transition graph
  --------------------------------------------------------------------

  open ComputeFragility GridState _≟g_ Action next-state terminal?
         all-grid-states all-actions public

  --------------------------------------------------------------------
  -- Derived reward: fragility transformed by frag-to-reward
  --------------------------------------------------------------------

  cc-reward : GridState → Action → ℕ
  cc-reward s a = frag-to-reward (frag-reward s a)

  --------------------------------------------------------------------
  -- Abstract step: (next-state, transformed-reward) distribution
  --------------------------------------------------------------------

  abstract-step : GridState → Action → Dist (GridState × ℕ)
  abstract-step s a =
    let ns = next-state s a
    in pure (ns , frag-to-reward (fragility ns))

  --------------------------------------------------------------------
  -- FOSD synthesis layer: fosd-compare from dynamics
  --------------------------------------------------------------------

  open FOSD-Synth.SFDMDPSynthesisFOSD
    GridState Action abstract-step all-actions default-action public

  --------------------------------------------------------------------
  -- Marginal reward distributions
  --------------------------------------------------------------------

  marginal-by-grid : GridState → Action → ℕ → Dist ℕ
  marginal-by-grid s a _ = reward-level (cc-reward s a)

  cc-abstraction : StateAbstraction ConcreteState GridState
  cc-abstraction = record
    { project = project
    ; embed   = embed
    ; section = section
    }

  marginal : ConcreteState → Action → ℕ → Dist ℕ
  marginal s = marginal-by-grid (project s)

  marginal-invariant : ∀ s₁ s₂ → project s₁ ≡ project s₂ →
    ∀ a t → marginal s₁ a t ≡ marginal s₂ a t
  marginal-invariant s₁ s₂ eq a t =
    cong (λ p → marginal-by-grid p a t) eq

  --------------------------------------------------------------------
  -- Auto-derived ordering: a ≤ b iff b's reward dominates a's
  --------------------------------------------------------------------

  auto-order : GridState → Action → Action → Set
  auto-order s a b = cc-reward s a ≤ cc-reward s b

  --------------------------------------------------------------------
  -- Verified abstract ranking
  --
  -- The key theorem: reward-level monotonicity + section = refl
  -- gives the full verified ranking WITHOUT enumerating all
  -- (state, action, action) triples.
  --------------------------------------------------------------------

  private
    abs-marginal : GridState → Action → ℕ → Dist ℕ
    abs-marginal gs = marginal (embed gs)

  abstract-ranking : VerifiedRanking GridState Action abs-marginal 0
  abstract-ranking = record
    { _≤ₐ_ = auto-order
    ; preserves = λ a b gs p n →
        subst (λ g → marginal-by-grid g a n SD[ 0 ]≤
                      marginal-by-grid g b n)
              (sym (section gs))
              (reward-level-mono (cc-reward gs a) (cc-reward gs b) p)
    }

  --------------------------------------------------------------------
  -- Lifted continuous ranking: ℚⁿ → verified
  --------------------------------------------------------------------

  continuous-ranking : VerifiedRanking ConcreteState Action marginal 0
  continuous-ranking =
    abstract-lift cc-abstraction marginal-invariant abstract-ranking

  --------------------------------------------------------------------
  -- Deployable controller
  --------------------------------------------------------------------

  decide : ConcreteState → Action
  decide s = decide-grid (project s)
