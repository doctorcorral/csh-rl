{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- Queens8Learning: 8-Queens solved via a materialized policy table
--
-- This module instantiates CSHRL.Learning.CombinatorialPlacementMDP
-- with the 8-Queens domain and demonstrates the full training →
-- deployment pipeline:
--
--   Training:    materialize-on-path builds a PolicyTable by calling
--                find-ranking once per board position along the optimal
--                path.  The table IS the learned policy — a concrete
--                list of (state, ranking) pairs.
--
--   Deployment:  run-policy looks up each board position in the table
--                and reads off the best action.  On a cache miss (a
--                state not seen during training), it falls back to
--                find-policy — the same verified Finder that built the
--                table.  No state is ever unhandled.
--
-- This is the verified analogue of trained weights in a DNN:
-- after training, the policy is a data structure, not a computation.
-- For novel states the Finder provides an online fallback, mirroring
-- how deployed systems combine cached policies with online search.
------------------------------------------------------------------------

module CSHRL.Tasks.Verified.Queens8Learning where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc)
import Data.Nat.Properties as ℕP
open import Data.List using (List; _∷_; []; length)
import Data.List.Properties as ListP
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Relation.Nullary using (Dec; yes; no)

------------------------------------------------------------------------
-- Import domain from Queens8
------------------------------------------------------------------------

import CSHRL.Tasks.Verified.Queens8 as Q8

open Q8 using ( Config; Action; C0; C1; C2; C3; C4; C5; C6; C7
              ; action-to-ℕ; all-actions; default-action
              ; is-dead-config; is-solved-config; place
              ; solved-reward; horizon; all-safe )

------------------------------------------------------------------------
-- Decidable equality for Actions (via ℕ-encoding round-trip)
------------------------------------------------------------------------

private
  from-ℕ : ℕ → Action
  from-ℕ 0 = C0
  from-ℕ 1 = C1
  from-ℕ 2 = C2
  from-ℕ 3 = C3
  from-ℕ 4 = C4
  from-ℕ 5 = C5
  from-ℕ 6 = C6
  from-ℕ 7 = C7
  from-ℕ _ = C0

  from-to : ∀ a → from-ℕ (action-to-ℕ a) ≡ a
  from-to C0 = refl
  from-to C1 = refl
  from-to C2 = refl
  from-to C3 = refl
  from-to C4 = refl
  from-to C5 = refl
  from-to C6 = refl
  from-to C7 = refl

  to-ℕ-injective : ∀ a b → action-to-ℕ a ≡ action-to-ℕ b → a ≡ b
  to-ℕ-injective a b p =
    trans (sym (from-to a)) (trans (cong from-ℕ p) (from-to b))

_≟ₐ_ : (a b : Action) → Dec (a ≡ b)
a ≟ₐ b with action-to-ℕ a ℕP.≟ action-to-ℕ b
... | yes p = yes (to-ℕ-injective a b p)
... | no ¬p = no (λ q → ¬p (cong action-to-ℕ q))

------------------------------------------------------------------------
-- Decidable equality for Config and State
--
-- Config = List ℕ  →  decidable via stdlib's ≡-dec
-- State  = Ongoing Config | Dead | Solved Config  →  by cases
------------------------------------------------------------------------

_≟c_ : (c₁ c₂ : Config) → Dec (c₁ ≡ c₂)
_≟c_ = ListP.≡-dec ℕP._≟_

------------------------------------------------------------------------
-- Instantiate CPMDP Learning
------------------------------------------------------------------------

open import CSHRL.Learning.CombinatorialPlacementMDP

open CPMDPLearning
  Config Action
  is-dead-config is-solved-config
  place solved-reward
  all-actions default-action horizon
  _≟ₐ_

------------------------------------------------------------------------
-- Decidable State equality (State comes from the EC via CPMDPLearning)
------------------------------------------------------------------------

_≟ₛ_ : (s₁ s₂ : State) → Dec (s₁ ≡ s₂)
Ongoing c₁ ≟ₛ Ongoing c₂ with c₁ ≟c c₂
... | yes p = yes (cong Ongoing p)
... | no ¬p = no (λ { refl → ¬p refl })
Dead       ≟ₛ Dead       = yes refl
Solved c₁  ≟ₛ Solved c₂  with c₁ ≟c c₂
... | yes p = yes (cong Solved p)
... | no ¬p = no (λ { refl → ¬p refl })
Ongoing _  ≟ₛ Dead       = no (λ ())
Ongoing _  ≟ₛ Solved _   = no (λ ())
Dead       ≟ₛ Ongoing _  = no (λ ())
Dead       ≟ₛ Solved _   = no (λ ())
Solved _   ≟ₛ Ongoing _  = no (λ ())
Solved _   ≟ₛ Dead       = no (λ ())

-- Bring table lookup into scope
open PolicyLookup _≟ₛ_

------------------------------------------------------------------------
-- TRAINING: Build the policy table
--
-- materialize-on-path follows the optimal path from the empty board,
-- calling find-ranking once per step and storing each result.
-- This is the expensive phase (~4 minutes): 8 game-tree searches.
------------------------------------------------------------------------

policy : PolicyTable
policy = materialize-on-path (Ongoing []) horizon horizon

------------------------------------------------------------------------
-- DEPLOYMENT: Roll out from the materialized table
--
-- Each step tries a table lookup first.  On a hit the action is
-- instant (no search).  On a miss — a state not seen during
-- training — we fall back to find-policy, the same verified Finder
-- that built the table.  No state is ever unhandled.
------------------------------------------------------------------------

private
  best : List Action → Action
  best []      = default-action
  best (a ∷ _) = a

run-policy : PolicyTable → ℕ → State → ℕ → List Action
run-policy _     _     _ zero    = []
run-policy table depth s (suc n) with lookup table s
... | just ranking =                            -- table hit: instant
  let a = best ranking
  in a ∷ run-policy table depth (proj₁ (step s a)) n
... | nothing =                                 -- miss: fall back to Finder
  let a = find-policy s depth
  in a ∷ run-policy table depth (proj₁ (step s a)) n

------------------------------------------------------------------------
-- THE MAIN RESULT
--
-- The materialized policy, built from a single training pass over the
-- optimal path, produces a valid 8-Queens solution from the empty board.
------------------------------------------------------------------------

test-solution : run-policy policy horizon (Ongoing []) horizon
              ≡ C0 ∷ C4 ∷ C7 ∷ C5 ∷ C2 ∷ C6 ∷ C1 ∷ C3 ∷ []
test-solution = refl

-- The discovered placement is a valid non-attacking configuration
test-valid : all-safe (0 ∷ 4 ∷ 7 ∷ 5 ∷ 2 ∷ 6 ∷ 1 ∷ 3 ∷ []) ≡ true
test-valid = refl

------------------------------------------------------------------------
-- POLICY INSPECTION
--
-- The policy table has exactly 8 entries — one per board position
-- along the solution path.  This is the complete learned policy.
------------------------------------------------------------------------

test-table-size : length policy ≡ 8
test-table-size = refl
