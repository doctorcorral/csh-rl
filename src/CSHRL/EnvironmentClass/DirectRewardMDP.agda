{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.EnvironmentClass.DirectRewardMDP
--
-- Generalised Environment Class for grid-abstracted MDPs where the
-- reward function is supplied directly by the task author rather than
-- derived from fragility computation.
--
-- This is a strict generalisation of ContinuousControlMDP:
--   • ContinuousControlMDP  =  DirectRewardMDP  where
--       cc-reward s a = frag-to-reward (fragility (next-state s a))
--
-- Useful when the natural reward signal is not "distance to terminal"
-- but instead domain-specific (e.g. instantaneous power, energy level,
-- Lyapunov derivative).
--
-- The task author provides:
--   • Domain types (ConcreteState, Action, GridState)
--   • A reward function  cc-reward : GridState → Action → ℕ
--   • Reward-distribution monotonicity  (reward-level-mono)
--   • State abstraction  (project, embed, section)
--   • Policy  (decide-grid)
--
-- The EC automatically provides:
--   • Auto-derived per-state action ordering
--   • Verified abstract ranking  (from reward monotonicity)
--   • Lifted continuous ranking  (via abstract-lift)
--   • Deployable controller  (decide = decide-grid ∘ project)
--
-- All --safe, no postulates.
------------------------------------------------------------------------

module CSHRL.EnvironmentClass.DirectRewardMDP where

open import Data.Nat using (ℕ; _≤_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; subst)

open import CSHRL.Probability.Finite using (Dist)
open import CSHRL.Probability.SD using (_SD[_]≤_)
open import CSHRL.Probability.FOSD using (_FOSD≤_)
open import CSHRL.Core.Compose using (VerifiedRanking)
open import CSHRL.Core.Abstraction using (StateAbstraction; abstract-lift)

------------------------------------------------------------------------
-- Parameters record
------------------------------------------------------------------------

record DRParameters : Set₁ where
  field
    ConcreteState Action GridState : Set

    cc-reward      : GridState → Action → ℕ
    reward-level   : ℕ → Dist ℕ
    reward-level-mono : ∀ m n → m ≤ n →
                        reward-level m FOSD≤ reward-level n

    project    : ConcreteState → GridState
    embed      : GridState → ConcreteState
    section    : ∀ g → project (embed g) ≡ g

    decide-grid : GridState → Action

------------------------------------------------------------------------
-- Everything the EC provides
------------------------------------------------------------------------

module DirectControl (P : DRParameters) where

  open DRParameters P

  --------------------------------------------------------------------
  -- Per-state action ordering: a ≤ b  iff  cc-reward s a ≤ cc-reward s b
  --------------------------------------------------------------------

  auto-order : GridState → Action → Action → Set
  auto-order s a b = cc-reward s a ≤ cc-reward s b

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
  -- Verified abstract ranking
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
  -- Lifted continuous ranking
  --------------------------------------------------------------------

  continuous-ranking : VerifiedRanking ConcreteState Action marginal 0
  continuous-ranking =
    abstract-lift cc-abstraction marginal-invariant abstract-ranking

  --------------------------------------------------------------------
  -- Deployable controller
  --------------------------------------------------------------------

  decide : ConcreteState → Action
  decide s = decide-grid (project s)
