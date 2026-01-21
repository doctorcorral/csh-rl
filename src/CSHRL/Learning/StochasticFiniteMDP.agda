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
-- The learning loop is identical in structure—only the trace computation
-- differs. This demonstrates the modularity of the CSHRL learning framework.
------------------------------------------------------------------------

module CSHRL.Learning.StochasticFiniteMDP where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.List using (List; []; _∷_; map; foldr)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Nullary using (Dec; yes; no)

open import CSHRL.Learning.Base
open import CSHRL.Probability.Finite using (Dist; pure; _>>=_; fmap; scale)

------------------------------------------------------------------------
-- StochasticFiniteMDP Learning Module
------------------------------------------------------------------------

module StochasticFDMDPLearning
  (State Action Reward : Set)
  -- Stochastic step function
  (step : State → Action → Dist (State × Reward))
  -- Reward ordering and operations
  (_≤ᵣ_    : Reward → Reward → Set)
  (max     : Reward → Reward → Reward)
  (bottom  : Reward)
  -- Reward arithmetic (for expected values)
  (_+ᵣ_    : Reward → Reward → Reward)
  (_*ᵣ_    : ℕ → Reward → Reward)
  (zeroᵣ   : Reward)
  -- Finiteness
  (all-actions : List Action)
  -- Decidable comparison
  (_≤?_    : (r s : Reward) → Dec (r ≤ᵣ s))
  (≤ᵣ-refl : ∀ {r} → r ≤ᵣ r)
  -- Decidable equality for actions
  (_≟ₐ_    : (a b : Action) → Dec (a ≡ b))
  where

  ------------------------------------------------------------------------
  -- Import Base
  ------------------------------------------------------------------------

  open UniversalLearning State Action _≟ₐ_ public

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
  -- Expected Value Computation
  ------------------------------------------------------------------------

  -- Weighted sum of rewards (unnormalized expected value)
  𝔼ᵣ : Dist Reward → Reward
  𝔼ᵣ = foldr (λ { (r , w) acc → (w *ᵣ r) +ᵣ acc }) zeroᵣ

  -- Expected immediate reward from a distribution
  expected-reward : Dist (State × Reward) → Reward
  expected-reward d = 𝔼ᵣ (fmap proj₂ d)

  ------------------------------------------------------------------------
  -- Trace Type and Comparison (Same as Deterministic)
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
  -- Expected Trace Computation (Stochastic)
  ------------------------------------------------------------------------

  -- Helper: max over a list of rewards
  max-list : List Reward → Reward
  max-list = foldr max bottom

  mutual
    -- Best expected trace from a state at depth k
    best-expected-trace : State → ℕ → Reward
    best-expected-trace s zero = zeroᵣ
    best-expected-trace s (suc k) = 
      max-list (map (λ a → expected-reward (step s a) +ᵣ 
                           expected-continuation s a k) all-actions)
    
    -- Expected value of continuing from action a at state s
    expected-continuation : State → Action → ℕ → Reward
    expected-continuation s a k = 
      𝔼ᵣ (fmap (λ { (s' , _) → best-expected-trace s' k }) (step s a))

  -- Expected trace for a specific action (as list of expected rewards)
  expected-trace-action : State → Action → ℕ → List Reward
  expected-trace-action s a zero = []
  expected-trace-action s a (suc k) = 
    expected-reward (step s a) ∷ 
    map (λ n → expected-continuation s a n) (countdown k)
    where
      countdown : ℕ → List ℕ
      countdown zero = []
      countdown (suc n) = n ∷ countdown n

  -- Max trace over a list
  max-trace : List Trace → Trace
  max-trace []       = []
  max-trace (t ∷ ts) = max-helper t ts
    where
      max-helper : Trace → List Trace → Trace
      max-helper current []       = current
      max-helper current (t ∷ ts) =
        if current ≤ₜᵇ t
        then max-helper t ts
        else max-helper current ts

  ------------------------------------------------------------------------
  -- Sorting and Ranking (Same Structure)
  ------------------------------------------------------------------------

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
  -- Find Ranking (Using Expected Traces)
  ------------------------------------------------------------------------

  find-ranking : State → ℕ → List Action
  find-ranking s k =
    let scored = map (λ a → (a , expected-trace-action s a k)) all-actions
        sorted = sort-scored scored
    in map proj₁ sorted

  -- Ranking from finder at depth k
  finder-ranking : ℕ → Ranking
  finder-ranking k s = list-to-ranking (find-ranking s k)

  ------------------------------------------------------------------------
  -- Totality of Finder Rankings
  ------------------------------------------------------------------------

  finder-ranking-total : ∀ k s → IsTotal (finder-ranking k) s
  finder-ranking-total k s = list-ranking-total (find-ranking s k) s

  ------------------------------------------------------------------------
  -- Violation Detection (Using Expected Traces)
  ------------------------------------------------------------------------

  test-pair : ℕ → Sample → Maybe Violation
  test-pair k (sample s a b) with finder-ranking k s a b | 
                                  expected-trace-action s a k ≤ₜᵇ expected-trace-action s b k
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
  learned-ranking initial-depth samples = finder-ranking (learn-loop initial-depth samples)

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
    learn-until stochastic-learner (λ ls' → has-stabilized ls' window) max-iter ls samples

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
