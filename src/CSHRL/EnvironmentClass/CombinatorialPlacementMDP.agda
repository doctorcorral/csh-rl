{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- Combinatorial Placement MDP Environment Class
--
-- Captures the essence of constraint satisfaction placement problems:
--   - N-Queens, Sudoku, Graph Coloring, etc.
--
-- Structure:
--   - States are: Ongoing (partial solution), Dead (constraint violated), 
--                 Solved (complete valid solution)
--   - Actions are placements
--   - Sparse rewards: 0 during placement, positive at Solved
--   - Dead and Solved are absorbing
--
-- Key insight for preservation:
--   - Dead states have value stream [0, 0, 0, ...]
--   - Solved states have value stream [R, R, R, ...] where R > 0
--   - Any path to Solved dominates any path to Dead
--   - The Finder's trace comparison correctly orders actions
------------------------------------------------------------------------

module CSHRL.EnvironmentClass.CombinatorialPlacementMDP where

open import Data.List using (List; []; _∷_; map; foldr; length)
open import Data.Nat using (ℕ; zero; suc; _⊔_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Codata.Guarded.Stream using (Stream; head; tail; tabulate)
open import Function using (_∘_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Nullary using (Dec; yes; no; ¬_)

------------------------------------------------------------------------
-- The Environment Class Module
------------------------------------------------------------------------

module CombinatorialPlacementMDP
  -- Placement configuration
  (Config : Set)           -- Type of partial/complete configurations
  (Action : Set)           -- Placement actions
  
  -- State classification
  (is-dead : Config → Bool)      -- Constraint violated?
  (is-solved : Config → Bool)    -- Complete valid solution?
  
  -- Transition
  (place : Config → Action → Config)  -- Apply placement
  
  -- Rewards
  (solved-reward : ℕ)     -- Reward for being in Solved state (e.g., 100)
  
  -- Finiteness
  (all-actions : List Action)
  (default-action : Action)
  
  -- Horizon (max placements needed)
  (horizon : ℕ)
  
  where

  ------------------------------------------------------------------------
  -- State Definition
  ------------------------------------------------------------------------
  
  data State : Set where
    Ongoing : Config → State
    Dead    : State
    Solved  : Config → State  -- Keep config for verification

  Reward : Set
  Reward = ℕ

  -- Propositional ordering on rewards
  _≤ᵣ_ : Reward → Reward → Set
  n ≤ᵣ m = n ≤ m

  -- Decidable ordering (returns proof or refutation)
  _≤?_ : (m n : Reward) → Dec (m ≤ᵣ n)
  zero  ≤? _     = yes z≤n
  suc _ ≤? zero  = no λ()
  suc m ≤? suc n with m ≤? n
  ... | yes p = yes (s≤s p)
  ... | no ¬p = no λ{ (s≤s p) → ¬p p }

  -- Boolean version for computational use in Finder
  _≤?ᵇ_ : Reward → Reward → Bool
  zero  ≤?ᵇ _     = true
  suc _ ≤?ᵇ zero  = false
  suc m ≤?ᵇ suc n = m ≤?ᵇ n

  -- Soundness: Boolean true implies propositional proof
  ≤?ᵇ-sound : ∀ r s → r ≤?ᵇ s ≡ true → r ≤ᵣ s
  ≤?ᵇ-sound zero    _       _  = z≤n
  ≤?ᵇ-sound (suc r) (suc s) p  = s≤s (≤?ᵇ-sound r s p)

  ------------------------------------------------------------------------
  -- Step Function
  ------------------------------------------------------------------------
  
  step : State → Action → State × Reward
  step Dead _ = (Dead , 0)
  step (Solved c) _ = (Solved c , solved-reward)  -- Absorbing with reward
  step (Ongoing c) a = 
    let c' = place c a
    in if is-dead c' then (Dead , 0)
       else if is-solved c' then (Solved c' , solved-reward)
       else (Ongoing c' , 0)

  ------------------------------------------------------------------------
  -- Import Core
  ------------------------------------------------------------------------
  
  open import CSHRL.Core
  open Core State Action Reward step _≤ᵣ_ _⊔_ 0 all-actions 
    hiding (preserves) public

  ------------------------------------------------------------------------
  -- Finder Algorithm (same structure as FiniteDeterministicMDP)
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
  -- Preservation Helpers
  ------------------------------------------------------------------------

  ≤ₛ-refl : ∀ (s : StreamR) → s ≤ₛ s
  head≤ (≤ₛ-refl s) = ≤-refl
  tail≤ (≤ₛ-refl s) = ≤ₛ-refl (tail s)

  ------------------------------------------------------------------------
  -- Value Stream Analysis
  --
  -- Key property of placement problems:
  --   solve Dead n     = 0          (dead is absorbing with 0)
  --   solve (Solved c) n = solved-reward  (solved is absorbing with R)
  --   solve (Ongoing c) n = depends on reachable states
  --
  -- For preservation, we need:
  --   - value Dead = [0, 0, 0, ...]
  --   - value (Solved c) = [R, R, R, ...]
  --   - Any action leading to Solved ≥ action leading to Dead
  ------------------------------------------------------------------------

  -- iter-head for accessing stream elements
  iter-head : ℕ → StreamR → Reward
  iter-head zero s = head s
  iter-head (suc n) s = iter-head n (tail s)

  iter-head-tabulate : ∀ (f : ℕ → ℕ) n → iter-head n (tabulate f) ≡ f n
  iter-head-tabulate f zero = refl
  iter-head-tabulate f (suc n) = iter-head-tabulate (f ∘ suc) n

  iter-head-value : ∀ s n → iter-head n (value s) ≡ solve s n
  iter-head-value s n = iter-head-tabulate (solve s) n

  -- HeadGen pattern for building stream orderings
  HeadGen : StreamR → StreamR → Set
  HeadGen s₁ s₂ = ∀ n → iter-head n s₁ ≤ iter-head n s₂

  shift-gen : ∀ {s₁ s₂} → HeadGen s₁ s₂ → HeadGen (tail s₁) (tail s₂)
  shift-gen gen n = gen (suc n)

  build-≤ₛ : ∀ (s₁ s₂ : StreamR) → HeadGen s₁ s₂ → s₁ ≤ₛ s₂
  head≤ (build-≤ₛ s₁ s₂ gen) = gen 0
  tail≤ (build-≤ₛ s₁ s₂ gen) = build-≤ₛ (tail s₁) (tail s₂) (shift-gen gen)

  ------------------------------------------------------------------------
  -- Absorbing State Properties (provided by instance)
  --
  -- These depend on the specific action list, so instances must provide them.
  ------------------------------------------------------------------------

  module WithAbsorbingLemmas
    -- solve Dead n = 0 for all n (Dead is absorbing with 0 reward)
    (solve-Dead-is-0 : ∀ n → solve Dead n ≡ 0)
    -- solve (Solved c) n = solved-reward for all n
    (solve-Solved-is-R : ∀ c n → solve (Solved c) n ≡ solved-reward)
    where

    -- iter-head at Dead is always 0
    iter-head-Dead-0 : ∀ n → iter-head n (value Dead) ≡ 0
    iter-head-Dead-0 n = 
      subst (λ x → x ≡ 0) (sym (iter-head-value Dead n)) (solve-Dead-is-0 n)

    -- iter-head at Solved is always solved-reward
    iter-head-Solved-R : ∀ c n → iter-head n (value (Solved c)) ≡ solved-reward
    iter-head-Solved-R c n = 
      subst (λ x → x ≡ solved-reward) (sym (iter-head-value (Solved c) n)) (solve-Solved-is-R c n)

    ----------------------------------------------------------------------
    -- Ordering: Dead ≤ anything, anything ≤ Solved
    ----------------------------------------------------------------------

    -- value Dead ≤ₛ value s for any s
    gen-Dead-≤-any : ∀ s → HeadGen (value Dead) (value s)
    gen-Dead-≤-any s n = 
      subst (λ x → x ≤ iter-head n (value s)) 
            (sym (iter-head-Dead-0 n)) 
            z≤n

    Dead-≤ₛ-any : ∀ s → value Dead ≤ₛ value s
    Dead-≤ₛ-any s = build-≤ₛ (value Dead) (value s) (gen-Dead-≤-any s)

  ----------------------------------------------------------------------
  -- Direct Preservation Module
  ----------------------------------------------------------------------

  module WithDirectPreservation
    (preserves-direct : ∀ a b s → 
                        s ranks a ≤ b → 
                        action-value s a ≤ₛ action-value s b)
    where

    instance
      PlacementMDPHomo : CoindHomo
      PlacementMDPHomo = record
        { _≤ₐ_ = _ranks_≤_
        ; preserves = preserves-direct
        }


