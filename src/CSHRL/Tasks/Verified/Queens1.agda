{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- 1-Queen: Trivial placement task to verify CombinatorialPlacementMDP
--
-- A single queen on a 1x1 board. Placing it always succeeds.
-- This is the simplest possible Queens variant.
------------------------------------------------------------------------

module CSHRL.Tasks.Verified.Queens1 where

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≡ᵇ_; _≤_; _⊔_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.List using (List; _∷_; []; length; map; _++_; foldr)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Codata.Guarded.Stream using (Stream; head; tail; tabulate)
open import Function using (_∘_)

------------------------------------------------------------------------
-- Configuration: 1-Queen on 1x1 board
------------------------------------------------------------------------

N : ℕ
N = 1

Config : Set
Config = List ℕ

------------------------------------------------------------------------
-- Constraint Checking (trivial for 1 queen)
------------------------------------------------------------------------

-- A single queen never attacks itself
is-dead-config : Config → Bool
is-dead-config _ = false  -- No queen attacks with just 1 queen

is-solved-config : Config → Bool
is-solved-config xs = length xs ≡ᵇ N

------------------------------------------------------------------------
-- Actions: Only column 0 on a 1x1 board
------------------------------------------------------------------------

data Action : Set where
  C0 : Action

action-to-ℕ : Action → ℕ
action-to-ℕ C0 = 0

all-actions : List Action
all-actions = C0 ∷ []

default-action : Action
default-action = C0

------------------------------------------------------------------------
-- Placement
------------------------------------------------------------------------

place : Config → Action → Config
place xs a = xs ++ (action-to-ℕ a ∷ [])

------------------------------------------------------------------------
-- Environment Class
------------------------------------------------------------------------

open import CSHRL.EnvironmentClass.CombinatorialPlacementMDP

solved-reward : ℕ
solved-reward = 100

horizon : ℕ
horizon = N

open CombinatorialPlacementMDP
  Config Action
  is-dead-config is-solved-config
  place
  solved-reward
  all-actions default-action
  horizon

------------------------------------------------------------------------
-- Absorbing State Proofs
------------------------------------------------------------------------

solve-Dead-0 : ∀ n → solve Dead n ≡ 0
solve-Dead-0 zero = refl
solve-Dead-0 (suc n) rewrite solve-Dead-0 n = refl

solve-Solved-R : ∀ c n → solve (Solved c) n ≡ solved-reward
solve-Solved-R c zero = refl
solve-Solved-R c (suc n) rewrite solve-Solved-R c n = refl

open WithAbsorbingLemmas solve-Dead-0 solve-Solved-R

------------------------------------------------------------------------
-- Stream Orderings
------------------------------------------------------------------------

gen-Solved-Solved : ∀ c₁ c₂ → HeadGen (value (Solved c₁)) (value (Solved c₂))
gen-Solved-Solved c₁ c₂ n =
  subst (λ x → x ≤ iter-head n (value (Solved c₂)))
        (sym (subst (λ x → x ≡ 100) (sym (iter-head-value (Solved c₁) n)) (solve-Solved-R c₁ n)))
        (subst (λ x → 100 ≤ x)
               (sym (subst (λ x → x ≡ 100) (sym (iter-head-value (Solved c₂) n)) (solve-Solved-R c₂ n)))
               ≤-refl)

Solved-≤ₛ-Solved : ∀ c₁ c₂ → value (Solved c₁) ≤ₛ value (Solved c₂)
Solved-≤ₛ-Solved c₁ c₂ = build-≤ₛ _ _ (gen-Solved-Solved c₁ c₂)

------------------------------------------------------------------------
-- Trace-Head Preservation
-- With propositional trace ordering, this is just projection!
------------------------------------------------------------------------

trace-≤ₜ-head : ∀ r₁ t₁ r₂ t₂ → 
                (r₁ ∷ t₁) ≤ₜ (r₂ ∷ t₂) →
                r₁ ≤ r₂
trace-≤ₜ-head r₁ t₁ r₂ t₂ (head≤ , _) = head≤

preserves-head : ∀ s a b →
  s ranks a ≤ b →
  head (action-value s a) ≤ᵣ head (action-value s b)
preserves-head s a b p = 
  trace-≤ₜ-head (proj₂ (step s a)) (best-trace (proj₁ (step s a)) horizon)
                (proj₂ (step s b)) (best-trace (proj₁ (step s b)) horizon) p

------------------------------------------------------------------------
-- Preservation Proof
--
-- For 1-Queen, there's only one action (C0), so all cases are trivial.
------------------------------------------------------------------------

direct-preserves : ∀ a b s → 
                   s ranks a ≤ b → 
                   action-value s a ≤ₛ action-value s b

-- Dead: trivial (same action)
head≤ (direct-preserves C0 C0 Dead p) = ≤-refl
tail≤ (direct-preserves C0 C0 Dead p) = ≤ₛ-refl (value Dead)

-- Solved: trivial (same action)
head≤ (direct-preserves C0 C0 (Solved c) p) = ≤-refl
tail≤ (direct-preserves C0 C0 (Solved c) p) = ≤ₛ-refl (value (Solved c))

-- Ongoing []: step gives (Solved [0], 100)
head≤ (direct-preserves C0 C0 (Ongoing []) p) = ≤-refl
tail≤ (direct-preserves C0 C0 (Ongoing []) p) = ≤ₛ-refl (value (Solved (0 ∷ [])))

-- Ongoing (x ∷ xs): length ≥ 1 = N, placing adds more
-- is-solved = (length ≡ᵇ 1) = false for length ≥ 2
-- But is-dead = false, so it stays Ongoing
head≤ (direct-preserves C0 C0 (Ongoing (x ∷ xs)) p) = ≤-refl
tail≤ (direct-preserves C0 C0 (Ongoing (x ∷ xs)) p) = ≤ₛ-refl _

------------------------------------------------------------------------
-- Verified Instance
------------------------------------------------------------------------

open WithDirectPreservation direct-preserves public

------------------------------------------------------------------------
-- Tests
------------------------------------------------------------------------

-- For 1-Queen, the only valid action is C0, which immediately solves
test-empty : find-policy (Ongoing []) horizon ≡ C0
test-empty = refl


