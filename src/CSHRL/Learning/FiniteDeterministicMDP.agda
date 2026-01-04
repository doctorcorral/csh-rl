{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Learning.FiniteDeterministicMDP
--
-- Learning implementation for Finite Deterministic MDPs.
--
-- Key properties:
--   - Deterministic transitions: step s a = (s', r) uniquely
--   - Finite horizon: traces stabilize at depth ≥ horizon
--   - Trace-based comparison: lexicographic ordering
--
-- This is the primary learning implementation for grid worlds,
-- mazes, and similar environments.
--
-- Uses Dec-based ordering for sound extraction of proofs from decisions.
------------------------------------------------------------------------

module CSHRL.Learning.FiniteDeterministicMDP where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Nullary using (Dec; yes; no)

open import CSHRL.Learning.Base

------------------------------------------------------------------------
-- FiniteDeterministicMDP Learning Module
------------------------------------------------------------------------

module FDMDPLearning
  (State Action Reward : Set)
  (step        : State → Action → State × Reward)
  (_≤ᵣ_        : Reward → Reward → Set)
  (max         : Reward → Reward → Reward)
  (bottom      : Reward)
  (all-actions : List Action)
  -- Decidable comparison for rewards (returns proof, not Bool!)
  (_≤?_        : (r s : Reward) → Dec (r ≤ᵣ s))
  (≤ᵣ-refl     : ∀ {r} → r ≤ᵣ r)
  -- Decidable equality for actions
  (_≟ₐ_        : (a b : Action) → Dec (a ≡ b))
  where

  ------------------------------------------------------------------------
  -- Import Base and Core
  ------------------------------------------------------------------------

  open UniversalLearning State Action _≟ₐ_ public

  open import CSHRL.Core
  open Core State Action Reward step _≤ᵣ_ max bottom all-actions public

  ------------------------------------------------------------------------
  -- Derive Boolean from Dec for computation
  ------------------------------------------------------------------------

  _≤?ᵇ_ : Reward → Reward → Bool
  r ≤?ᵇ s with r ≤? s
  ... | yes _ = true
  ... | no  _ = false

  -- Soundness: Boolean true implies propositional proof
  ≤?ᵇ-sound : ∀ r s → r ≤?ᵇ s ≡ true → r ≤ᵣ s
  ≤?ᵇ-sound r s p with r ≤? s
  ... | yes proof = proof
  ... | no  _     with () ← p

  ------------------------------------------------------------------------
  -- Trace Type and Comparison
  ------------------------------------------------------------------------

  Trace : Set
  Trace = List Reward

  -- Lexicographic trace comparison (Boolean for computation)
  _≤ₜᵇ_ : Trace → Trace → Bool
  []       ≤ₜᵇ []       = true
  []       ≤ₜᵇ (_ ∷ _)  = true
  (_ ∷ _)  ≤ₜᵇ []       = false
  (r₁ ∷ t₁) ≤ₜᵇ (r₂ ∷ t₂) =
    if r₁ ≤?ᵇ r₂ then
      if r₂ ≤?ᵇ r₁ then (t₁ ≤ₜᵇ t₂)  -- Equal, compare tails
      else true                        -- r₁ < r₂
    else false                         -- r₁ > r₂

  -- Reflexivity of Boolean trace comparison
  ≤ₜᵇ-refl : ∀ t → t ≤ₜᵇ t ≡ true
  ≤ₜᵇ-refl [] = refl
  ≤ₜᵇ-refl (r ∷ t) with r ≤? r | r ≤? r
  ... | yes _ | yes _ = ≤ₜᵇ-refl t
  ... | yes _ | no ¬p = ⊥-elim (¬p ≤ᵣ-refl)
    where open import Data.Empty using (⊥-elim)
  ... | no ¬p | _     = ⊥-elim (¬p ≤ᵣ-refl)
    where open import Data.Empty using (⊥-elim)

  -- Equal traces imply ≤ₜᵇ
  eq-implies-≤ₜᵇ : ∀ t₁ t₂ → t₁ ≡ t₂ → t₁ ≤ₜᵇ t₂ ≡ true
  eq-implies-≤ₜᵇ t .t refl = ≤ₜᵇ-refl t

  ------------------------------------------------------------------------
  -- Trace Computation (Deterministic)
  ------------------------------------------------------------------------

  mutual
    best-trace : State → ℕ → Trace
    best-trace s zero    = []
    best-trace s (suc k) = max-trace (map (λ a → trace-action s a k) all-actions)

    trace-action : State → Action → ℕ → Trace
    trace-action s a k =
      let (s' , r) = step s a
      in r ∷ best-trace s' k

    max-trace : List Trace → Trace
    max-trace []       = []
    max-trace (t ∷ ts) = max-helper t ts

    max-helper : Trace → List Trace → Trace
    max-helper current []       = current
    max-helper current (t ∷ ts) =
      if current ≤ₜᵇ t
      then max-helper t ts
      else max-helper current ts

  ------------------------------------------------------------------------
  -- Restricted Trace Computation (for unavailable actions)
  ------------------------------------------------------------------------

  mutual
    best-trace-restricted : Available → State → ℕ → Trace
    best-trace-restricted avail s zero = []
    best-trace-restricted avail s (suc k) =
      let available = filter-available avail all-actions
          traces = map (λ a → trace-action-restricted avail s a k) available
      in max-trace traces

    trace-action-restricted : Available → State → Action → ℕ → Trace
    trace-action-restricted avail s a k =
      let (s' , r) = step s a
      in r ∷ best-trace-restricted avail s' k

  ------------------------------------------------------------------------
  -- Sorting and Ranking
  ------------------------------------------------------------------------

  -- Sort actions by trace quality (insertion sort)
  insert-scored : (Action × Trace) → List (Action × Trace) → List (Action × Trace)
  insert-scored x [] = x ∷ []
  insert-scored (a₁ , t₁) ((a₂ , t₂) ∷ xs) =
    if t₂ ≤ₜᵇ t₁
    then (a₁ , t₁) ∷ (a₂ , t₂) ∷ xs
    else (a₂ , t₂) ∷ insert-scored (a₁ , t₁) xs

  sort-scored : List (Action × Trace) → List (Action × Trace)
  sort-scored []       = []
  sort-scored (x ∷ xs) = insert-scored x (sort-scored xs)

  ------------------------------------------------------------------------
  -- Find Ranking
  ------------------------------------------------------------------------

  -- Find ranking over all actions at depth k
  find-ranking : State → ℕ → List Action
  find-ranking s k =
    let scored = map (λ a → (a , trace-action s a k)) all-actions
        sorted = sort-scored scored
    in map proj₁ sorted

  -- Find ranking restricted to available actions
  find-ranking-restricted : Available → State → ℕ → List Action
  find-ranking-restricted avail s k =
    let available = filter-available avail all-actions
        scored = map (λ a → (a , trace-action-restricted avail s a k)) available
        sorted = sort-scored scored
    in map proj₁ sorted

  -- Ranking from finder at depth k
  finder-ranking : ℕ → Ranking
  finder-ranking k s = list-to-ranking (find-ranking s k)

  -- Restricted ranking from finder
  finder-ranking-restricted : Available → ℕ → Ranking
  finder-ranking-restricted avail k s = 
    list-to-ranking (find-ranking-restricted avail s k)

  ------------------------------------------------------------------------
  -- Totality of Finder Rankings
  ------------------------------------------------------------------------

  finder-ranking-total : ∀ k s → IsTotal (finder-ranking k) s
  finder-ranking-total k s = list-ranking-total (find-ranking s k) s

  finder-ranking-restricted-total : ∀ avail k s → 
    IsTotal (finder-ranking-restricted avail k) s
  finder-ranking-restricted-total avail k s = 
    list-ranking-total (find-ranking-restricted avail s k) s

  ------------------------------------------------------------------------
  -- Violation Detection
  ------------------------------------------------------------------------

  -- Test a pair for violation at given depth
  test-pair : ℕ → Sample → Maybe Violation
  test-pair k (sample s a b) with finder-ranking k s a b | trace-action s a k ≤ₜᵇ trace-action s b k
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
  learned-ranking initial-depth samples = finder-ranking (learn-loop initial-depth samples)

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
    trace-action-restricted avail s a k ≤ₜᵇ trace-action-restricted avail s b k ≡ true

  -- Restricted finder soundness type
  RestrictedFinderSound : Available → ℕ → Set
  RestrictedFinderSound avail k = ∀ s a b →
    finder-ranking-restricted avail k s a b ≡ true →
    trace-action-restricted avail s a k ≤ₜᵇ trace-action-restricted avail s b k ≡ true ⊎
    trace-action-restricted avail s a k ≡ trace-action-restricted avail s b k

  -- Adaptation soundness: given restricted finder soundness, we get restricted preserves
  adaptation-sound : ∀ avail k →
    RestrictedFinderSound avail k →
    RestrictedPreserves avail k
  adaptation-sound avail k sound a b s avail-a avail-b rank-ab with sound s a b rank-ab
  ... | inj₁ p = p
  ... | inj₂ q = eq-implies-≤ₜᵇ (trace-action-restricted avail s a k) (trace-action-restricted avail s b k) q

  ------------------------------------------------------------------------
  -- Curried Learner Interface for FDMDP
  --
  -- Provides a stateful, checkpoint-friendly learning interface.
  -- Uses the universal LearnerState from Base with FDMDP-specific test.
  ------------------------------------------------------------------------

  -- Create an FDMDP learner with the FDMDP-specific test function
  fdmdp-learner : Learner
  fdmdp-learner = make-learner test-pair

  -- Initialize a fresh learner state
  new-fdmdp-learner : LearnerState
  new-fdmdp-learner = init-learner

  -- Train on a single sample
  train-step : LearnerState → Sample → LearnerState
  train-step = fdmdp-learner

  -- Train on multiple samples
  train-batch : LearnerState → List Sample → LearnerState
  train-batch = learn-many fdmdp-learner

  -- Get current ranking at learner's depth
  current-ranking : LearnerState → State → List Action
  current-ranking ls s = find-ranking s (get-depth ls)

  -- Get current ranking with unavailability
  current-ranking-restricted : LearnerState → Available → State → List Action
  current-ranking-restricted ls avail s = find-ranking-restricted avail s (get-depth ls)

  -- Train until no violations for N samples (or max iterations)
  train-until-stable : LearnerState → ℕ → ℕ → List Sample → LearnerState
  train-until-stable ls window max-iter samples = 
    learn-until fdmdp-learner (λ ls' → has-stabilized ls' window) max-iter ls samples

  -- Get full training trace (for analysis/plotting)
  training-trace : LearnerState → List Sample → List LearnerState
  training-trace = learn-with-trace fdmdp-learner

  -- Extract depth history from trace (for plotting)
  depth-history : List LearnerState → List ℕ
  depth-history [] = []
  depth-history (ls ∷ rest) = get-depth ls ∷ depth-history rest

  -- Extract violation count history from trace
  violation-history : List LearnerState → List ℕ
  violation-history [] = []
  violation-history (ls ∷ rest) = get-violations ls ∷ violation-history rest

  ------------------------------------------------------------------------
  -- Active Learner for FDMDP
  --
  -- Uses active refinement: on violation, BOTH increase depth AND swap
  -- the violated pair in the explicit ranking.
  ------------------------------------------------------------------------

  -- Create an active FDMDP learner with the global swap updater
  fdmdp-active-learner : ActiveLearner
  fdmdp-active-learner = make-active-learner test-pair global-swap-updater

  -- Initialize active learner with Finder's ranking at depth 0
  new-fdmdp-active-learner : ActiveLearnerState
  new-fdmdp-active-learner = init-active-learner (λ s → find-ranking s 0)

  -- Initialize with a specific initial depth
  new-fdmdp-active-learner-at : ℕ → ActiveLearnerState
  new-fdmdp-active-learner-at k = init-active-learner (λ s → find-ranking s k)

  -- Active training step
  active-train-step : ActiveLearnerState → Sample → ActiveLearnerState
  active-train-step = fdmdp-active-learner

  -- Active batch training
  active-batch : ActiveLearnerState → List Sample → ActiveLearnerState
  active-batch = active-train-batch fdmdp-active-learner

  -- Get the current refined ranking for a state
  current-active-ranking : ActiveLearnerState → State → List Action
  current-active-ranking ls s = get-explicit-ranking ls s

  -- Get active learner depth
  active-depth : ActiveLearnerState → ℕ
  active-depth = get-active-depth

  -- Get active learner violation count
  active-violation-count : ActiveLearnerState → ℕ
  active-violation-count = get-active-violations

