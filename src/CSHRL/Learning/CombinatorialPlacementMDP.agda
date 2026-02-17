{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Learning.CombinatorialPlacementMDP
--
-- Learning implementation for Combinatorial Placement MDPs.
--
-- Key properties:
--   - States are Ongoing/Dead/Solved (placement structure)
--   - Binary rewards: 0 or solved-reward
--   - Short-circuit traces for absorbing states (Dead/Solved)
--   - Horizon-bounded search
--
-- Reuses the trace/ranking infrastructure from the EC module
-- (EnvironmentClass.CombinatorialPlacementMDP) and adds:
--   - Violation detection
--   - Restricted (unavailability-aware) trace computation
--   - Learning loop (depth-increase on violation)
--   - Curried Learner interface (stateful, checkpoint-friendly)
--   - Active Learner interface (ranking swap + depth-increase)
--
-- This parallels Learning.FiniteDeterministicMDP but specialised
-- for the placement structure.
------------------------------------------------------------------------

module CSHRL.Learning.CombinatorialPlacementMDP where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (≤-refl)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Nullary using (Dec; yes; no)

open import CSHRL.Learning.Base
open import CSHRL.EnvironmentClass.CombinatorialPlacementMDP

------------------------------------------------------------------------
-- CombinatorialPlacementMDP Learning Module
------------------------------------------------------------------------

module CPMDPLearning
  -- Same parameters as the Environment Class
  (Config : Set)
  (Action : Set)
  (is-dead    : Config → Bool)
  (is-solved  : Config → Bool)
  (place      : Config → Action → Config)
  (solved-reward : ℕ)
  (all-actions    : List Action)
  (default-action : Action)
  (horizon : ℕ)
  -- Additional: decidable equality for actions (needed by Learning.Base)
  (_≟ₐ_ : (a b : Action) → Dec (a ≡ b))
  where

  ------------------------------------------------------------------------
  -- Import from EC (State, step, Trace, trace-action, find-ranking, …)
  ------------------------------------------------------------------------

  open CombinatorialPlacementMDP
    Config Action is-dead is-solved
    place solved-reward all-actions default-action
    horizon
    public

  ------------------------------------------------------------------------
  -- Import Base (Ranking, Violation, Learner, ActiveLearner, …)
  ------------------------------------------------------------------------

  open UniversalLearning State Action _≟ₐ_ public

  ------------------------------------------------------------------------
  -- Boolean Trace Reflexivity
  --
  -- The EC defines _≤?ᵇ_ and _≤ₜᵇ_ but their reflexivity proofs live
  -- inside WithTraceBridge (which requires extra parameters).
  -- We prove them here unconditionally.
  ------------------------------------------------------------------------

  ≤?ᵇ-refl : ∀ n → n ≤?ᵇ n ≡ true
  ≤?ᵇ-refl zero    = refl
  ≤?ᵇ-refl (suc n) = ≤?ᵇ-refl n

  ≤ₜᵇ-refl : ∀ t → t ≤ₜᵇ t ≡ true
  ≤ₜᵇ-refl []      = refl
  ≤ₜᵇ-refl (r ∷ t) rewrite ≤?ᵇ-refl r = ≤ₜᵇ-refl t

  eq-implies-≤ₜᵇ : ∀ t₁ t₂ → t₁ ≡ t₂ → t₁ ≤ₜᵇ t₂ ≡ true
  eq-implies-≤ₜᵇ t .t refl = ≤ₜᵇ-refl t

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
  -- Restricted Trace Computation (for unavailable actions)
  --
  -- Uses the same short-circuit for Dead/Solved as the unrestricted
  -- version, but only considers available actions for Ongoing states.
  ------------------------------------------------------------------------

  mutual
    best-trace-restricted : Available → State → ℕ → Trace
    best-trace-restricted avail _          zero    = []
    best-trace-restricted avail Dead       (suc k) = 0 ∷ dead-trace k
    best-trace-restricted avail (Solved c) (suc k) = solved-reward ∷ solved-trace k
    best-trace-restricted avail (Ongoing c) (suc k) =
      let available = filter-available avail all-actions
          traces = map (λ a → trace-action-restricted avail (Ongoing c) a k) available
      in max-trace traces

    trace-action-restricted : Available → State → Action → ℕ → Trace
    trace-action-restricted avail s a k =
      let (s' , r) = step s a
      in r ∷ best-trace-restricted avail s' k

  -- Find ranking restricted to available actions
  find-ranking-restricted : Available → State → ℕ → List Action
  find-ranking-restricted avail s k =
    let available = filter-available avail all-actions
        scored = map (λ a → (a , trace-action-restricted avail s a k)) available
        sorted = sort-scored scored
    in map proj₁ sorted

  -- Restricted ranking from finder
  finder-ranking-restricted : Available → ℕ → Ranking
  finder-ranking-restricted avail k s =
    list-to-ranking (find-ranking-restricted avail s k)

  -- Totality of restricted finder rankings
  finder-ranking-restricted-total : ∀ avail k s →
    IsTotal (finder-ranking-restricted avail k) s
  finder-ranking-restricted-total avail k s =
    list-ranking-total (find-ranking-restricted avail s k) s

  ------------------------------------------------------------------------
  -- Violation Detection
  ------------------------------------------------------------------------

  -- Test a pair for violation at given depth
  test-pair : ℕ → Sample → Maybe Violation
  test-pair k (sample s a b)
    with finder-ranking k s a b
       | trace-action s a k ≤ₜᵇ trace-action s b k
  ... | true  | false = just (violation s b a k)
  ... | _     | _     = nothing

  ------------------------------------------------------------------------
  -- Learning Loop (Instantiated)
  ------------------------------------------------------------------------

  learn-step : ℕ → Sample → ℕ
  learn-step = default-learn-step test-pair

  learn-loop : ℕ → List Sample → ℕ
  learn-loop = default-learn-loop test-pair

  learned-ranking : ℕ → List Sample → Ranking
  learned-ranking initial-depth samples =
    finder-ranking (learn-loop initial-depth samples)

  ------------------------------------------------------------------------
  -- Adaptation to Unavailability
  ------------------------------------------------------------------------

  adapt-to-unavailability : Available → ℕ → Ranking
  adapt-to-unavailability avail depth = finder-ranking-restricted avail depth

  ------------------------------------------------------------------------
  -- Convergence
  ------------------------------------------------------------------------

  Converges : Set
  Converges = ConvergesAt finder-ranking

  ------------------------------------------------------------------------
  -- Monotonic Improvement
  --
  -- Violations can only decrease with depth.
  ------------------------------------------------------------------------

  ViolationsDecrease : Set
  ViolationsDecrease = ∀ s a b k →
    trace-action s a k ≤ₜᵇ trace-action s b k ≡ false →
    trace-action s a (suc k) ≤ₜᵇ trace-action s b (suc k) ≡ false

  ------------------------------------------------------------------------
  -- Soundness Properties
  ------------------------------------------------------------------------

  -- Type of finder soundness
  FinderSound : ℕ → Set
  FinderSound k = ∀ s a b →
    finder-ranking k s a b ≡ true →
    trace-action s a k ≤ₜᵇ trace-action s b k ≡ true ⊎
    trace-action s a k ≡ trace-action s b k

  -- Type of restricted preservation
  RestrictedPreserves : Available → ℕ → Set
  RestrictedPreserves avail k = ∀ a b s →
    avail a ≡ true →
    avail b ≡ true →
    finder-ranking-restricted avail k s a b ≡ true →
    trace-action-restricted avail s a k ≤ₜᵇ
      trace-action-restricted avail s b k ≡ true

  -- Restricted finder soundness type
  RestrictedFinderSound : Available → ℕ → Set
  RestrictedFinderSound avail k = ∀ s a b →
    finder-ranking-restricted avail k s a b ≡ true →
    trace-action-restricted avail s a k ≤ₜᵇ
      trace-action-restricted avail s b k ≡ true ⊎
    trace-action-restricted avail s a k ≡
      trace-action-restricted avail s b k

  -- Adaptation soundness: given restricted finder soundness, restricted preserves
  adaptation-sound : ∀ avail k →
    RestrictedFinderSound avail k →
    RestrictedPreserves avail k
  adaptation-sound avail k sound a b s avail-a avail-b rank-ab
    with sound s a b rank-ab
  ... | inj₁ p = p
  ... | inj₂ q = eq-implies-≤ₜᵇ
    (trace-action-restricted avail s a k)
    (trace-action-restricted avail s b k) q

  ------------------------------------------------------------------------
  -- Curried Learner Interface for CombinatorialPlacementMDP
  --
  -- Provides a stateful, checkpoint-friendly learning interface.
  -- Uses the universal LearnerState from Base with placement-specific test.
  ------------------------------------------------------------------------

  -- Create a CPMDP learner with the placement-specific test function
  cpmdp-learner : Learner
  cpmdp-learner = make-learner test-pair

  -- Initialize a fresh learner state
  new-cpmdp-learner : LearnerState
  new-cpmdp-learner = init-learner

  -- Train on a single sample
  train-step : LearnerState → Sample → LearnerState
  train-step = cpmdp-learner

  -- Train on multiple samples
  train-batch : LearnerState → List Sample → LearnerState
  train-batch = learn-many cpmdp-learner

  -- Get current ranking at learner's depth
  current-ranking : LearnerState → State → List Action
  current-ranking ls s = find-ranking s (get-depth ls)

  -- Get current ranking with unavailability
  current-ranking-restricted : LearnerState → Available → State → List Action
  current-ranking-restricted ls avail s =
    find-ranking-restricted avail s (get-depth ls)

  -- Train until no violations for N samples (or max iterations)
  train-until-stable : LearnerState → ℕ → ℕ → List Sample → LearnerState
  train-until-stable ls window max-iter samples =
    learn-until cpmdp-learner (λ ls' → has-stabilized ls' window)
      max-iter ls samples

  -- Get full training trace (for analysis/plotting)
  training-trace : LearnerState → List Sample → List LearnerState
  training-trace = learn-with-trace cpmdp-learner

  -- Extract depth history from trace (for plotting)
  depth-history : List LearnerState → List ℕ
  depth-history [] = []
  depth-history (ls ∷ rest) = get-depth ls ∷ depth-history rest

  -- Extract violation count history from trace
  violation-history : List LearnerState → List ℕ
  violation-history [] = []
  violation-history (ls ∷ rest) = get-violations ls ∷ violation-history rest

  ------------------------------------------------------------------------
  -- Active Learner for CombinatorialPlacementMDP
  --
  -- Uses active refinement: on violation, BOTH increase depth AND swap
  -- the violated pair in the explicit ranking.
  ------------------------------------------------------------------------

  -- Create an active CPMDP learner with the global swap updater
  cpmdp-active-learner : ActiveLearner
  cpmdp-active-learner = make-active-learner test-pair global-swap-updater

  -- Initialize active learner with Finder's ranking at depth 0
  new-cpmdp-active-learner : ActiveLearnerState
  new-cpmdp-active-learner = init-active-learner (λ s → find-ranking s 0)

  -- Initialize with a specific initial depth
  new-cpmdp-active-learner-at : ℕ → ActiveLearnerState
  new-cpmdp-active-learner-at k = init-active-learner (λ s → find-ranking s k)

  -- Active training step
  active-train-step : ActiveLearnerState → Sample → ActiveLearnerState
  active-train-step = cpmdp-active-learner

  -- Active batch training
  active-batch : ActiveLearnerState → List Sample → ActiveLearnerState
  active-batch = active-train-batch cpmdp-active-learner

  -- Get the current refined ranking for a state
  current-active-ranking : ActiveLearnerState → State → List Action
  current-active-ranking ls s = get-explicit-ranking ls s

  -- Get active learner depth
  active-depth : ActiveLearnerState → ℕ
  active-depth = get-active-depth

  -- Get active learner violation count
  active-violation-count : ActiveLearnerState → ℕ
  active-violation-count = get-active-violations

  ------------------------------------------------------------------------
  -- Policy Materialization
  --
  -- Build a PolicyTable by following the optimal path from an initial
  -- state.  Each step calls find-ranking once and stores the result.
  -- The resulting table is the learned policy: a concrete mapping from
  -- visited states to their optimal action rankings.
  --
  -- After materialization, the table can be used for instant lookups
  -- via PolicyLookup (requires decidable state equality from caller).
  ------------------------------------------------------------------------

  private
    head-action : List Action → Action
    head-action []      = default-action
    head-action (a ∷ _) = a

  -- Materialize rankings along the optimal path
  -- Calls find-ranking once per step, stores (state, ranking) pairs
  materialize-on-path : State → ℕ → ℕ → PolicyTable
  materialize-on-path _ _ zero = []
  materialize-on-path s depth (suc n) =
    let ranking = find-ranking s depth
        a = head-action ranking
        s' = proj₁ (step s a)
    in (s , ranking) ∷ materialize-on-path s' depth n

  -- Materialize at explicitly listed states
  materialize-at : List State → ℕ → PolicyTable
  materialize-at states depth = build-table (λ s → find-ranking s depth) states
