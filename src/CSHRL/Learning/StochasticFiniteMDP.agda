{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Learning.StochasticFiniteMDP
--
-- Learning implementation for Stochastic Finite MDPs.
--
-- Key differences from deterministic:
--   - Transitions are probabilistic: step s a = Dist (s', r)
--   - Traces are EXPECTED traces (weighted average over branches)
--   - Comparison uses expected lexicographic ordering
--
-- Reuses the trace/ranking infrastructure from the EC module
-- (EnvironmentClass.StochasticFiniteMDP) and adds:
--   - Violation detection (on expected traces)
--   - Learning loop (depth-increase on violation)
--   - Curried Learner interface (stateful, checkpoint-friendly)
--   - Active Learner interface (ranking swap + depth-increase)
--
-- The learning loop is identical in structure to the deterministic
-- case—only the trace computation differs. This demonstrates the
-- modularity of the CSHRL learning framework.
------------------------------------------------------------------------

module CSHRL.Learning.StochasticFiniteMDP where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.List using (List; []; _∷_; map; foldr)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Nullary using (Dec; yes; no)

open import CSHRL.Learning.Base
open import CSHRL.Probability.Finite using (Dist)
open import CSHRL.EnvironmentClass.StochasticFiniteMDP

------------------------------------------------------------------------
-- StochasticFiniteMDP Learning Module
------------------------------------------------------------------------

module StochasticFDMDPLearning
  -- Same parameters as the Environment Class
  (State : Set)
  (Action : Set)
  (Reward : Set)
  (step : State → Action → Dist (State × Reward))
  (_≤ᵣ_ : Reward → Reward → Set)
  (_≤?_ : (r s : Reward) → Dec (r ≤ᵣ s))
  (≤ᵣ-refl : ∀ {r} → r ≤ᵣ r)
  (max : Reward → Reward → Reward)
  (bottom : Reward)
  (_+ᵣ_ : Reward → Reward → Reward)
  (_*ᵣ_ : ℕ → Reward → Reward)
  (zeroᵣ : Reward)
  (all-actions : List Action)
  (default-action : Action)
  (horizon : ℕ)
  -- Additional: decidable equality for actions (needed by Learning.Base)
  (_≟ₐ_ : (a b : Action) → Dec (a ≡ b))
  where

  ------------------------------------------------------------------------
  -- Import from EC (expected-trace-action, find-ranking, _≤ₜᵇ_, …)
  ------------------------------------------------------------------------

  open StochasticFiniteMDP
    State Action Reward step
    _≤ᵣ_ _≤?_ ≤ᵣ-refl max bottom
    _+ᵣ_ _*ᵣ_ zeroᵣ
    all-actions default-action horizon
    public

  ------------------------------------------------------------------------
  -- Import Base (Ranking, Violation, Learner, ActiveLearner, …)
  ------------------------------------------------------------------------

  open UniversalLearning State Action _≟ₐ_ public

  ------------------------------------------------------------------------
  -- Boolean Trace Reflexivity
  --
  -- The EC defines _≤?ᵇ_ and _≤ₜᵇ_ but their reflexivity proofs
  -- are not exported. We prove them here.
  ------------------------------------------------------------------------

  -- Soundness: Boolean true implies propositional proof
  ≤?ᵇ-sound : ∀ r s → r ≤?ᵇ s ≡ true → r ≤ᵣ s
  ≤?ᵇ-sound r s p with r ≤? s
  ... | yes proof = proof
  ... | no  _     with () ← p

  -- Reflexivity of Boolean trace comparison
  ≤ₜᵇ-refl : ∀ t → t ≤ₜᵇ t ≡ true
  ≤ₜᵇ-refl [] = refl
  ≤ₜᵇ-refl (r ∷ t) with r ≤? r | r ≤? r
  ... | yes _ | yes _ = ≤ₜᵇ-refl t
  ... | yes _ | no ¬p = ⊥-elim (¬p ≤ᵣ-refl)
  ... | no ¬p | _     = ⊥-elim (¬p ≤ᵣ-refl)

  -- Equal traces imply ≤ₜᵇ
  eq-implies-≤ₜᵇ : ∀ t₁ t₂ → t₁ ≡ t₂ → t₁ ≤ₜᵇ t₂ ≡ true
  eq-implies-≤ₜᵇ t .t refl = ≤ₜᵇ-refl t

  ------------------------------------------------------------------------
  -- Trace type alias (for convenience)
  ------------------------------------------------------------------------

  Trace : Set
  Trace = List Reward

  ------------------------------------------------------------------------
  -- Finder Rankings
  ------------------------------------------------------------------------

  -- Ranking from finder at depth k
  finder-ranking : ℕ → Ranking
  finder-ranking k s = list-to-ranking (find-ranking s k)

  -- Totality of finder rankings
  finder-ranking-total : ∀ k s → IsTotal (finder-ranking k) s
  finder-ranking-total k s = list-ranking-total (find-ranking s k) s

  ------------------------------------------------------------------------
  -- Violation Detection (Using Expected Traces)
  ------------------------------------------------------------------------

  test-pair : ℕ → Sample → Maybe Violation
  test-pair k (sample s a b)
    with finder-ranking k s a b
       | expected-trace-action s a k ≤ₜᵇ expected-trace-action s b k
  ... | true  | false = just (violation s b a k)
  ... | _     | _     = nothing

  ------------------------------------------------------------------------
  -- Learning Loop
  ------------------------------------------------------------------------

  learn-step : ℕ → Sample → ℕ
  learn-step = default-learn-step test-pair

  learn-loop : ℕ → List Sample → ℕ
  learn-loop = default-learn-loop test-pair

  learned-ranking : ℕ → List Sample → Ranking
  learned-ranking initial-depth samples =
    finder-ranking (learn-loop initial-depth samples)

  ------------------------------------------------------------------------
  -- Convergence
  ------------------------------------------------------------------------

  Converges : Set
  Converges = ConvergesAt finder-ranking

  ------------------------------------------------------------------------
  -- Curried Learner Interface for Stochastic FDMDP
  ------------------------------------------------------------------------

  stochastic-learner : Learner
  stochastic-learner = make-learner test-pair

  new-stochastic-learner : LearnerState
  new-stochastic-learner = init-learner

  train-step : LearnerState → Sample → LearnerState
  train-step = stochastic-learner

  train-batch : LearnerState → List Sample → LearnerState
  train-batch = learn-many stochastic-learner

  current-ranking : LearnerState → State → List Action
  current-ranking ls s = find-ranking s (get-depth ls)

  train-until-stable : LearnerState → ℕ → ℕ → List Sample → LearnerState
  train-until-stable ls window max-iter samples =
    learn-until stochastic-learner (λ ls' → has-stabilized ls' window)
      max-iter ls samples

  training-trace : LearnerState → List Sample → List LearnerState
  training-trace = learn-with-trace stochastic-learner

  depth-history : List LearnerState → List ℕ
  depth-history [] = []
  depth-history (ls ∷ rest) = get-depth ls ∷ depth-history rest

  violation-history : List LearnerState → List ℕ
  violation-history [] = []
  violation-history (ls ∷ rest) = get-violations ls ∷ violation-history rest

  ------------------------------------------------------------------------
  -- Active Learner for Stochastic FDMDP
  ------------------------------------------------------------------------

  stochastic-active-learner : ActiveLearner
  stochastic-active-learner = make-active-learner test-pair global-swap-updater

  new-stochastic-active-learner : ActiveLearnerState
  new-stochastic-active-learner = init-active-learner (λ s → find-ranking s 0)

  new-stochastic-active-learner-at : ℕ → ActiveLearnerState
  new-stochastic-active-learner-at k = init-active-learner (λ s → find-ranking s k)

  active-train-step : ActiveLearnerState → Sample → ActiveLearnerState
  active-train-step = stochastic-active-learner

  active-batch : ActiveLearnerState → List Sample → ActiveLearnerState
  active-batch = active-train-batch stochastic-active-learner

  current-active-ranking : ActiveLearnerState → State → List Action
  current-active-ranking ls s = get-explicit-ranking ls s

  active-depth : ActiveLearnerState → ℕ
  active-depth = get-active-depth

  active-violation-count : ActiveLearnerState → ℕ
  active-violation-count = get-active-violations

  ------------------------------------------------------------------------
  -- Policy Materialization
  --
  -- Build a PolicyTable by evaluating find-ranking at listed states.
  -- For stochastic environments, path-following is not directly
  -- applicable (step returns a distribution), so the caller provides
  -- the list of states to materialize (e.g., via BFS over the
  -- distribution support).
  ------------------------------------------------------------------------

  -- Materialize at explicitly listed states
  materialize-at : List State → ℕ → PolicyTable
  materialize-at states depth = build-table (λ s → find-ranking s depth) states

  ------------------------------------------------------------------------
  -- Comparison with Deterministic Learning
  --
  -- The only differences are:
  --   1. step returns Dist (State × Reward) instead of State × Reward
  --   2. trace-action becomes expected-trace-action
  --   3. All else (ranking, learning loop, convergence) remains the same
  --
  -- This demonstrates the modularity of the CSHRL learning framework:
  -- the algorithm is parameterized by the trace computation, not the
  -- underlying dynamics.
  ------------------------------------------------------------------------
