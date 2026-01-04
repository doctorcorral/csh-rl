{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- Finite Deterministic MDP Environment Class
--
-- This module provides:
--   1. The Finder algorithm for computing optimal rankings
--   2. The structure for preservation proofs
--   3. A template for instances to provide domain-specific proofs
--
-- Each instance provides:
--   - The MDP (State, Action, Reward, step)
--   - Proofs of structural properties (terminal, horizon)
--   - The key bridge lemma connecting traces to streams
------------------------------------------------------------------------

module CSHRL.EnvironmentClass.FiniteDeterministicMDP where

open import Data.List using (List; []; _∷_; map; foldr)
open import Data.Nat using (ℕ; zero; suc; _⊔_; _≤_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Codata.Guarded.Stream using (Stream; head; tail; tabulate)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Nullary using (Dec; yes; no; ¬_)

------------------------------------------------------------------------
-- The Environment Class Module
------------------------------------------------------------------------

module FiniteDeterministicMDP
  -- Basic MDP signature
  (State : Set)
  (Action : Set)
  (Reward : Set)
  (step : State → Action → State × Reward)
  
  -- Reward ordering and operations
  (_≤ᵣ_ : Reward → Reward → Set)
  (_≤?_ : (r s : Reward) → Dec (r ≤ᵣ s))  -- Decidable ordering
  (≤ᵣ-refl : ∀ {r} → r ≤ᵣ r)
  (max : Reward → Reward → Reward)
  (bottom : Reward)
  
  -- Finiteness
  (all-actions : List Action)
  (default-action : Action)
  
  -- Horizon bound
  (horizon : ℕ)
  
  where

  -- Derive Boolean version from Dec for computational use
  _≤?ᵇ_ : Reward → Reward → Bool
  r ≤?ᵇ s with r ≤? s
  ... | yes _ = true
  ... | no  _ = false

  ------------------------------------------------------------------------
  -- Import Core
  ------------------------------------------------------------------------
  
  open import CSHRL.Core
  open Core State Action Reward step _≤ᵣ_ max bottom all-actions 
    hiding (preserves) public

  ------------------------------------------------------------------------
  -- 1. Finder Algorithm (Ordinal Value Iteration)
  ------------------------------------------------------------------------

  Trace : Set
  Trace = List Reward

  -- Lexicographic comparison (Boolean version for computation)
  _≤ₜᵇ_ : Trace → Trace → Bool
  []       ≤ₜᵇ []       = true
  []       ≤ₜᵇ (_ ∷ _)  = true
  (_ ∷ _)  ≤ₜᵇ []       = false
  (r₁ ∷ t₁) ≤ₜᵇ (r₂ ∷ t₂) = 
    if r₁ ≤?ᵇ r₂ then
      if r₂ ≤?ᵇ r₁ then (t₁ ≤ₜᵇ t₂)
      else true
    else false

  -- Lexicographic comparison (Propositional version for proofs)
  _≤ₜ_ : Trace → Trace → Set
  []       ≤ₜ []       = ⊤
  []       ≤ₜ (_ ∷ _)  = ⊤
  (_ ∷ _)  ≤ₜ []       = ⊥
  (r₁ ∷ t₁) ≤ₜ (r₂ ∷ t₂) = (r₁ ≤ᵣ r₂) × ((r₂ ≤ᵣ r₁) → t₁ ≤ₜ t₂)

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

  insert : (Action × Trace) → List (Action × Trace) → List (Action × Trace)
  insert x [] = x ∷ []
  insert (a₁ , t₁) ((a₂ , t₂) ∷ xs) = 
    if t₂ ≤ₜᵇ t₁ 
    then (a₁ , t₁) ∷ (a₂ , t₂) ∷ xs
    else (a₂ , t₂) ∷ insert (a₁ , t₁) xs

  sort-scored : List (Action × Trace) → List (Action × Trace)
  sort-scored []       = []
  sort-scored (x ∷ xs) = insert x (sort-scored xs)

  -- The Finder: compute optimal ranking
  find-ranking : State → ℕ → List Action
  find-ranking s k = 
    let scored = map (λ a → (a , trace-action s a k)) all-actions
        sorted = sort-scored scored
    in map proj₁ sorted

  find-policy : State → ℕ → Action
  find-policy s k with find-ranking s k
  ... | []      = default-action
  ... | (a ∷ _) = a

  -- The ranking relation derived from finder (Boolean version for computation)
  _ranks_≤ᵇ_ : State → Action → Action → Bool
  s ranks a ≤ᵇ b = trace-action s a horizon ≤ₜᵇ trace-action s b horizon

  -- The ranking relation as a proposition (directly using propositional trace ordering)
  _ranks_≤_ : State → Action → Action → Set
  s ranks a ≤ b = trace-action s a horizon ≤ₜ trace-action s b horizon

  ------------------------------------------------------------------------
  -- 2. Helper Lemmas for Preservation
  ------------------------------------------------------------------------

  -- Reflexivity of stream ordering
  ≤ₛ-refl : ∀ (s : StreamR) → s ≤ₛ s
  head≤ (≤ₛ-refl s) = ≤ᵣ-refl
  tail≤ (≤ₛ-refl s) = ≤ₛ-refl (tail s)

  -- Extract head comparison from propositional trace comparison
  -- With the propositional definition, this is just projection!
  trace-≤ₜ-head : ∀ r₁ t₁ r₂ t₂ → 
                  (r₁ ∷ t₁) ≤ₜ (r₂ ∷ t₂) →
                  r₁ ≤ᵣ r₂
  trace-≤ₜ-head r₁ t₁ r₂ t₂ (head≤ , _) = head≤

  -- Head preservation is direct
  preserves-head : ∀ s a b →
    s ranks a ≤ b →
    head (action-value s a) ≤ᵣ head (action-value s b)
  preserves-head s a b p = 
    let ra = proj₂ (step s a)
        rb = proj₂ (step s b)
        ta = best-trace (proj₁ (step s a)) horizon
        tb = best-trace (proj₁ (step s b)) horizon
    in trace-≤ₜ-head ra ta rb tb p

  ------------------------------------------------------------------------
  -- 3. Preservation Proof Template
  --
  -- The full preservation requires connecting traces to infinite streams.
  -- This is done via the bridge-lemma parameter that instances provide.
  ------------------------------------------------------------------------

  module WithBridgeLemma 
    -- The key bridge lemma: trace ordering implies tail stream ordering
    -- This handles both cases:
    --   1. When heads are strictly ordered (ra < rb), need to show value sa' ≤ₛ value sb'
    --   2. When heads are equal, tail traces determine tail streams
    -- Instances provide the domain-specific proof
    (tail-value-≤ₛ : ∀ s a b → 
                     s ranks a ≤ b →
                     value (proj₁ (step s a)) ≤ₛ value (proj₁ (step s b)))
    where
    
    -- With the bridge lemma, preservation follows directly
    preserves : ∀ a b s → 
                s ranks a ≤ b → 
                action-value s a ≤ₛ action-value s b
    head≤ (preserves a b s p) = preserves-head s a b p
    tail≤ (preserves a b s p) = tail-value-≤ₛ s a b p

    -- The verified CoindHomo instance
    instance
      FiniteMDPHomo : CoindHomo
      FiniteMDPHomo = record
        { _≤ₐ_ = _ranks_≤_
        ; preserves = preserves
        }

  ------------------------------------------------------------------------
  -- 4. Alternative: Direct Preservation Instance
  --
  -- For simple cases, instances can provide the full preservation directly.
  ------------------------------------------------------------------------

  module WithDirectPreservation
    (preserves-direct : ∀ a b s → 
                        s ranks a ≤ b → 
                        action-value s a ≤ₛ action-value s b)
    where

    instance
      FiniteMDPHomo : CoindHomo
      FiniteMDPHomo = record
        { _≤ₐ_ = _ranks_≤_
        ; preserves = preserves-direct
        }


