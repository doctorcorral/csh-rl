{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- Stochastic Finite MDP Environment Class
--
-- Extension of FiniteDeterministicMDP to stochastic transitions.
-- Uses the Giry monad (finite distributions) for probabilistic step.
--
-- This module provides:
--   1. Expected value computation via distribution convolution
--   2. Expected trace comparison for the Finder algorithm
--   3. StochasticCoindHomo instance template
--
-- Key insight: In stochastic settings, rankings preserve EXPECTED
-- stream dominance. The Finder computes expected traces and ranks
-- actions by their expected lexicographic ordinal.
------------------------------------------------------------------------

module CSHRL.EnvironmentClass.StochasticFiniteMDP where

open import Data.List using (List; []; _∷_; map; foldr; concatMap; length)
open import Data.Nat using (ℕ; zero; suc; _⊔_; _+_; _*_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Codata.Guarded.Stream using (Stream; head; tail; tabulate)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Nullary using (Dec; yes; no; ¬_)

-- Import probability monad
open import CSHRL.Probability.Finite using (Dist; pure; _>>=_; fmap; scale; total-weight)

------------------------------------------------------------------------
-- The Stochastic Environment Class Module
------------------------------------------------------------------------

module StochasticFiniteMDP
  -- Basic MDP signature
  (State : Set)
  (Action : Set)
  (Reward : Set)
  
  -- STOCHASTIC step function: returns distribution over (State × Reward)
  (step : State → Action → Dist (State × Reward))
  
  -- Reward ordering and operations
  (_≤ᵣ_ : Reward → Reward → Set)
  (_≤?_ : (r s : Reward) → Dec (r ≤ᵣ s))
  (≤ᵣ-refl : ∀ {r} → r ≤ᵣ r)
  (max : Reward → Reward → Reward)
  (bottom : Reward)
  
  -- Reward arithmetic (required for expected values)
  (_+ᵣ_ : Reward → Reward → Reward)
  (_*ᵣ_ : ℕ → Reward → Reward)  -- Scalar multiplication by weight
  (zeroᵣ : Reward)
  
  -- Finiteness
  (all-actions : List Action)
  (default-action : Action)
  
  -- Horizon bound
  (horizon : ℕ)
  
  where

  ------------------------------------------------------------------------
  -- Derive Boolean ordering
  ------------------------------------------------------------------------

  _≤?ᵇ_ : Reward → Reward → Bool
  r ≤?ᵇ s with r ≤? s
  ... | yes _ = true
  ... | no  _ = false

  ------------------------------------------------------------------------
  -- Import Stochastic Core
  ------------------------------------------------------------------------

  open import CSHRL.Core.Stochastic
  open StochasticCore State Action Reward step _≤ᵣ_ ≤ᵣ-refl _+ᵣ_ _*ᵣ_ zeroᵣ max bottom all-actions
    public

  ------------------------------------------------------------------------
  -- Expected Value Computation
  ------------------------------------------------------------------------

  -- Expected immediate reward from a distribution
  expected-reward : Dist (State × Reward) → Reward
  expected-reward d = 𝔼ᵣ (fmap proj₂ d)

  ------------------------------------------------------------------------
  -- Expected Trace Computation
  ------------------------------------------------------------------------

  -- A weighted trace: trace with its probability weight
  WeightedTrace : Set
  WeightedTrace = Dist (List Reward)

  -- Compute expected trace: weighted average of all possible traces
  -- For stochastic MDPs, we track the distribution of traces

  -- Best expected trace from a state at depth k
  -- Note: max-list is imported from StochasticCore
  mutual
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

  ------------------------------------------------------------------------
  -- Ranking via Expected Traces
  ------------------------------------------------------------------------

  -- Lexicographic comparison of expected traces
  _≤ₜᵇ_ : List Reward → List Reward → Bool
  []       ≤ₜᵇ []       = true
  []       ≤ₜᵇ (_ ∷ _)  = true
  (_ ∷ _)  ≤ₜᵇ []       = false
  (r₁ ∷ t₁) ≤ₜᵇ (r₂ ∷ t₂) = 
    if r₁ ≤?ᵇ r₂ then
      if r₂ ≤?ᵇ r₁ then (t₁ ≤ₜᵇ t₂)
      else true
    else false

  -- Propositional trace ordering
  _≤ₜ_ : List Reward → List Reward → Set
  []       ≤ₜ []       = ⊤
  []       ≤ₜ (_ ∷ _)  = ⊤
  (_ ∷ _)  ≤ₜ []       = ⊥
  (r₁ ∷ t₁) ≤ₜ (r₂ ∷ t₂) = (r₁ ≤ᵣ r₂) × ((r₂ ≤ᵣ r₁) → t₁ ≤ₜ t₂)

  -- Insert action into sorted list (by expected trace)
  insert : (Action × List Reward) → List (Action × List Reward) → List (Action × List Reward)
  insert x [] = x ∷ []
  insert (a₁ , t₁) ((a₂ , t₂) ∷ xs) = 
    if t₂ ≤ₜᵇ t₁ 
    then (a₁ , t₁) ∷ (a₂ , t₂) ∷ xs
    else (a₂ , t₂) ∷ insert (a₁ , t₁) xs

  sort-scored : List (Action × List Reward) → List (Action × List Reward)
  sort-scored []       = []
  sort-scored (x ∷ xs) = insert x (sort-scored xs)

  -- The Finder: compute optimal ranking based on expected traces
  find-ranking : State → ℕ → List Action
  find-ranking s k = 
    let scored = map (λ a → (a , expected-trace-action s a k)) all-actions
        sorted = sort-scored scored
    in map proj₁ sorted

  find-policy : State → ℕ → Action
  find-policy s k with find-ranking s k
  ... | []      = default-action
  ... | (a ∷ _) = a

  -- The ranking relation (Boolean)
  _ranks_≤ᵇ_ : State → Action → Action → Bool
  s ranks a ≤ᵇ b = expected-trace-action s a horizon ≤ₜᵇ expected-trace-action s b horizon

  -- The ranking relation (Propositional)
  _ranks_≤_ : State → Action → Action → Set
  s ranks a ≤ b = expected-trace-action s a horizon ≤ₜ expected-trace-action s b horizon

  ------------------------------------------------------------------------
  -- Preservation Proof Templates
  --
  -- Two orderings are available:
  -- 1. ≤ₛ-lex (lexicographic): appropriate for most stochastic MDPs
  -- 2. ≤ₛ-expected (pointwise): only works when stream dominance holds
  ------------------------------------------------------------------------

  ------------------------------------------------------------------------
  -- LEXICOGRAPHIC PRESERVATION (Recommended for Stochastic MDPs)
  --
  -- Uses conditional tail comparison: only require tail≤ when heads equal.
  -- This correctly captures lexicographic trace semantics and is the
  -- natural coinductive lifting for expected value comparison.
  ------------------------------------------------------------------------

  module WithLexPreservation
    -- Head preservation: ranking implies expected head dominance
    (head-lex-≤ : ∀ s a b → 
                  s ranks a ≤ b →
                  head (expected-action-value s a) ≤ᵣ head (expected-action-value s b))
    -- Tail preservation: only required when heads are equal
    (tail-lex-≤ : ∀ s a b → 
                  s ranks a ≤ b →
                  head (expected-action-value s a) ≡ head (expected-action-value s b) →
                  tail (expected-action-value s a) ≤ₛ-lex tail (expected-action-value s b))
    where

    -- Full lexicographic preservation
    lex-preserves : ∀ a b s → 
                    s ranks a ≤ b → 
                    expected-action-value s a ≤ₛ-lex expected-action-value s b
    head≤ (lex-preserves a b s p) = head-lex-≤ s a b p
    tail≤ (lex-preserves a b s p) = tail-lex-≤ s a b p

    -- The verified StochasticCoindHomo instance
    instance
      StochasticMDPHomo : StochasticCoindHomo
      StochasticMDPHomo = record
        { _≤ₐ_ = _ranks_≤_
        ; preserves = lex-preserves
        }

  ------------------------------------------------------------------------
  -- Direct Lexicographic Preservation
  ------------------------------------------------------------------------

  module WithDirectLexPreservation
    (preserves-direct : ∀ a b s → 
                        s ranks a ≤ b → 
                        expected-action-value s a ≤ₛ-lex expected-action-value s b)
    where

    instance
      StochasticMDPHomo : StochasticCoindHomo
      StochasticMDPHomo = record
        { _≤ₐ_ = _ranks_≤_
        ; preserves = preserves-direct
        }

  ------------------------------------------------------------------------
  -- Pointwise Preservation (Legacy - Stronger Condition)
  --
  -- Requires pointwise stream dominance at every timestep.
  -- Only works for special cases where expected traces coincide
  -- with pointwise stream dominance.
  ------------------------------------------------------------------------

  module WithPointwisePreservation
    (head-pw-≤ : ∀ s a b → 
                 s ranks a ≤ b →
                 head (expected-action-value s a) ≤ᵣ head (expected-action-value s b))
    (tail-pw-≤ : ∀ s a b → 
                 s ranks a ≤ b →
                 tail (expected-action-value s a) ≤ₛ-expected tail (expected-action-value s b))
    where

    pw-preserves : ∀ a b s → 
                   s ranks a ≤ b → 
                   expected-action-value s a ≤ₛ-expected expected-action-value s b
    _≤ₛ-pointwise_.head≤ (pw-preserves a b s p) = head-pw-≤ s a b p
    _≤ₛ-pointwise_.tail≤ (pw-preserves a b s p) = tail-pw-≤ s a b p

  ------------------------------------------------------------------------
  -- 5. Memoized Stochastic Finder (Dynamic Programming)
  --
  -- The recursive Finder has exponential complexity: each
  -- best-expected-trace(s, k) reexpands |A| × |outcomes| subtrees.
  -- This module builds a value table layer by layer:
  --
  --   bet[0][s] = 0
  --   bet[k+1][s] = max_a (E[r | s,a] + Σ w_i × bet[k][s'_i])
  --
  -- Total cost: O(depth × numStates × |A| × |outcomes|)
  --
  -- Usage:
  --   module Memo = StochasticFiniteMDP.MemoizedStochastic 16 id id 10
  --   policy = Memo.fast-policy s
  ------------------------------------------------------------------------

  module MemoizedStochastic
    (numStates : ℕ)
    (stateIndex : State → ℕ)
    (indexState : ℕ → State)
    (memo-depth : ℕ)
    where

    private
      nth-rew : List Reward → ℕ → Reward
      nth-rew []       _       = zeroᵣ
      nth-rew (r ∷ _)  zero    = r
      nth-rew (_ ∷ rs) (suc n) = nth-rew rs n

      tab-rew : ℕ → (ℕ → Reward) → List Reward
      tab-rew zero    _ = []
      tab-rew (suc n) f = f 0 ∷ tab-rew n (λ k → f (suc k))

      -- Expected continuation using a memoized table
      ec-memo : State → Action → List Reward → Reward
      ec-memo s a prev =
        𝔼ᵣ (fmap (λ { (s' , _) → nth-rew prev (stateIndex s') }) (step s a))

      -- Build one DP level from the previous level
      build-level : List Reward → List Reward
      build-level prev = tab-rew numStates (λ i →
        let s = indexState i
        in max-list (map (λ a →
             expected-reward (step s a) +ᵣ ec-memo s a prev) all-actions))

      -- Bottom-up DP: O(depth) iterations of build-level
      dp : ℕ → List Reward
      dp zero    = tab-rew numStates (λ _ → zeroᵣ)
      dp (suc k) = build-level (dp k)

    value-table : List Reward
    value-table = dp memo-depth

    private
      action-score : State → Action → Reward
      action-score s a =
        expected-reward (step s a) +ᵣ ec-memo s a value-table

      nth-action : List Action → ℕ → Action
      nth-action []       _       = default-action
      nth-action (a ∷ _)  zero    = a
      nth-action (_ ∷ as) (suc n) = nth-action as n

      tab-act : ℕ → (ℕ → Action) → List Action
      tab-act zero    _ = []
      tab-act (suc n) f = f 0 ∷ tab-act n (λ k → f (suc k))

    -- Policy via singleton-trace sort (reuses existing sort-scored)
    policy : State → Action
    policy s =
      let scored = map (λ a → (a , action-score s a ∷ [])) all-actions
          sorted = sort-scored scored
      in case sorted of λ where
           []            → default-action
           ((a , _) ∷ _) → a
      where
        case_of_ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → A → (A → B) → B
        case x of f = f x

    policy-table : List Action
    policy-table = tab-act numStates (λ i → policy (indexState i))

    fast-policy : State → Action
    fast-policy s = nth-action policy-table (stateIndex s)

  ------------------------------------------------------------------------
  -- Risk-Aware Extensions (Future Work)
  --
  -- Beyond expected value, stochastic settings support:
  -- - CVaR (Conditional Value at Risk) for risk-averse agents
  -- - Variance-penalized objectives
  -- - Distributional RL via quantile comparison
  --
  -- These require tracking full distributions, not just expectations.
  ------------------------------------------------------------------------
