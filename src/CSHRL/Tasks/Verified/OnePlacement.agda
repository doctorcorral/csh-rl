{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- One-Placement: Ultra-Minimal Combinatorial Placement Example
--
-- A trivial task: place exactly 1 item to win.
-- Starting config is empty, any action leads to Solved.
-- Demonstrates CombinatorialPlacementMDP with complete proofs.
------------------------------------------------------------------------

module CSHRL.Tasks.Verified.OnePlacement where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc; _≤_; _⊔_; z≤n; s≤s; _≡ᵇ_)
open import Data.Nat.Properties using (≤-refl)
open import Data.List using (List; _∷_; []; length; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Codata.Guarded.Stream using (Stream; head; tail; tabulate)
open import Function using (_∘_)

------------------------------------------------------------------------
-- Domain: Single placement with 2 choices
------------------------------------------------------------------------

Config : Set
Config = List ℕ

data Action : Set where
  Place0 : Action
  Place1 : Action

action-to-ℕ : Action → ℕ
action-to-ℕ Place0 = 0
action-to-ℕ Place1 = 1

place : Config → Action → Config
place xs a = xs ++ (action-to-ℕ a ∷ [])

is-dead-config : Config → Bool
is-dead-config _ = false

-- Solved when length = 1 (one placement made)
is-solved-config : Config → Bool
is-solved-config xs = length xs ≡ᵇ 1

------------------------------------------------------------------------
-- Environment Class
------------------------------------------------------------------------

open import CSHRL.EnvironmentClass.CombinatorialPlacementMDP

all-actions : List Action
all-actions = Place0 ∷ Place1 ∷ []

default-action : Action
default-action = Place0

solved-reward : ℕ
solved-reward = 100

horizon : ℕ
horizon = 1

open CombinatorialPlacementMDP
  Config Action
  is-dead-config is-solved-config
  place
  solved-reward
  all-actions default-action
  horizon

------------------------------------------------------------------------
-- Absorbing Proofs
------------------------------------------------------------------------

solve-Dead-0 : ∀ n → solve Dead n ≡ 0
solve-Dead-0 zero = refl
solve-Dead-0 (suc n) rewrite solve-Dead-0 n = refl

solve-Solved-R : ∀ c n → solve (Solved c) n ≡ solved-reward
solve-Solved-R c zero = refl
solve-Solved-R c (suc n) rewrite solve-Solved-R c n = refl

open WithAbsorbingLemmas solve-Dead-0 solve-Solved-R

------------------------------------------------------------------------
-- All Solved streams are equal
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

-- Prove that solve (Ongoing (x ∷ xs)) n = 0 for all n
-- Base case: solve ... 0 = max(0, 0) = 0 (since all actions give reward 0)
-- Inductive case: solve ... (suc n) = max(solve next-state n, ...)
--   where next-state is also a long Ongoing config, so by IH = 0

solve-long : ∀ x xs n → solve (Ongoing (x ∷ xs)) n ≡ 0
solve-long x [] zero = refl
solve-long x (y ∷ ys) zero = refl
solve-long x [] (suc n) rewrite solve-long x (0 ∷ []) n | solve-long x (1 ∷ []) n = refl
solve-long x (y ∷ ys) (suc n) rewrite solve-long x (y ∷ ys ++ (0 ∷ [])) n | solve-long x (y ∷ ys ++ (1 ∷ [])) n = refl

-- iter-head for long Ongoing is always 0
iter-head-long-0 : ∀ x xs n → iter-head n (value (Ongoing (x ∷ xs))) ≡ 0
iter-head-long-0 x xs n = 
  subst (λ v → v ≡ 0) (sym (iter-head-value (Ongoing (x ∷ xs)) n)) (solve-long x xs n)

-- Now we can build long-≤ₛ using the HeadGen pattern
gen-long : ∀ x₁ xs₁ x₂ xs₂ → HeadGen (value (Ongoing (x₁ ∷ xs₁))) (value (Ongoing (x₂ ∷ xs₂)))
gen-long x₁ xs₁ x₂ xs₂ n = 
  subst (λ v → v ≤ iter-head n (value (Ongoing (x₂ ∷ xs₂))))
        (sym (iter-head-long-0 x₁ xs₁ n))
        (subst (λ v → 0 ≤ v)
               (sym (iter-head-long-0 x₂ xs₂ n))
               z≤n)

long-≤ₛ : ∀ {x₁ xs₁ x₂ xs₂} → value (Ongoing (x₁ ∷ xs₁)) ≤ₛ value (Ongoing (x₂ ∷ xs₂))
long-≤ₛ {x₁} {xs₁} {x₂} {xs₂} = build-≤ₛ _ _ (gen-long x₁ xs₁ x₂ xs₂)

------------------------------------------------------------------------
-- Preservation Proof
--
-- States:
-- - Dead: all actions give (Dead, 0), value = [0, 0, ...]
-- - Solved c: all actions give (Solved c, 100), value = [100, 100, ...]
-- - Ongoing []: step gives (Solved [a], 100), value = [100, 100, ...]
-- - Ongoing [x]: already solved length, step gives (Solved [x,a], 100)
-- - Ongoing [x,y,...]: past solved length, step gives (Ongoing [...], 0)
------------------------------------------------------------------------

direct-preserves : ∀ a b s → 
                   s ranks a ≤ b → 
                   action-value s a ≤ₛ action-value s b

-- Dead: trivial
head≤ (direct-preserves a b Dead p) = ≤-refl
tail≤ (direct-preserves a b Dead p) = ≤ₛ-refl (value Dead)

-- Solved: trivial
head≤ (direct-preserves a b (Solved c) p) = ≤-refl
tail≤ (direct-preserves a b (Solved c) p) = ≤ₛ-refl (value (Solved c))

-- Ongoing []: step gives (Solved [a], 100) for both actions
-- action-value (Ongoing []) a = 100 ∷ value (Solved [a])
head≤ (direct-preserves Place0 Place0 (Ongoing []) p) = ≤-refl
tail≤ (direct-preserves Place0 Place0 (Ongoing []) p) = ≤ₛ-refl (value (Solved (0 ∷ [])))
head≤ (direct-preserves Place0 Place1 (Ongoing []) p) = ≤-refl
tail≤ (direct-preserves Place0 Place1 (Ongoing []) p) = Solved-≤ₛ-Solved (0 ∷ []) (1 ∷ [])
head≤ (direct-preserves Place1 Place0 (Ongoing []) p) = ≤-refl
tail≤ (direct-preserves Place1 Place0 (Ongoing []) p) = Solved-≤ₛ-Solved (1 ∷ []) (0 ∷ [])
head≤ (direct-preserves Place1 Place1 (Ongoing []) p) = ≤-refl
tail≤ (direct-preserves Place1 Place1 (Ongoing []) p) = ≤ₛ-refl (value (Solved (1 ∷ [])))

-- Ongoing [x]: length = 1 ≥ 1 = N, but placing adds to [x, a]
-- is-solved [x, a] = (length ≡ᵇ 1) = (2 ≡ᵇ 1) = false
-- So step gives (Ongoing [x, a], 0)
head≤ (direct-preserves Place0 Place0 (Ongoing (x ∷ [])) p) = ≤-refl
tail≤ (direct-preserves Place0 Place0 (Ongoing (x ∷ [])) p) = ≤ₛ-refl _
head≤ (direct-preserves Place0 Place1 (Ongoing (x ∷ [])) p) = z≤n
tail≤ (direct-preserves Place0 Place1 (Ongoing (x ∷ [])) p) = long-≤ₛ
head≤ (direct-preserves Place1 Place0 (Ongoing (x ∷ [])) p) = z≤n
tail≤ (direct-preserves Place1 Place0 (Ongoing (x ∷ [])) p) = long-≤ₛ
head≤ (direct-preserves Place1 Place1 (Ongoing (x ∷ [])) p) = ≤-refl
tail≤ (direct-preserves Place1 Place1 (Ongoing (x ∷ [])) p) = ≤ₛ-refl _

-- Ongoing [x, y, ...]: length ≥ 2 > 1 = N
-- step gives (Ongoing [...], 0)
head≤ (direct-preserves Place0 Place0 (Ongoing (x ∷ y ∷ xs)) p) = ≤-refl
tail≤ (direct-preserves Place0 Place0 (Ongoing (x ∷ y ∷ xs)) p) = ≤ₛ-refl _
head≤ (direct-preserves Place0 Place1 (Ongoing (x ∷ y ∷ xs)) p) = z≤n
tail≤ (direct-preserves Place0 Place1 (Ongoing (x ∷ y ∷ xs)) p) = long-≤ₛ
head≤ (direct-preserves Place1 Place0 (Ongoing (x ∷ y ∷ xs)) p) = z≤n
tail≤ (direct-preserves Place1 Place0 (Ongoing (x ∷ y ∷ xs)) p) = long-≤ₛ
head≤ (direct-preserves Place1 Place1 (Ongoing (x ∷ y ∷ xs)) p) = ≤-refl
tail≤ (direct-preserves Place1 Place1 (Ongoing (x ∷ y ∷ xs)) p) = ≤ₛ-refl _

------------------------------------------------------------------------
-- Verified Instance
------------------------------------------------------------------------

open WithDirectPreservation direct-preserves public

------------------------------------------------------------------------
-- Tests
------------------------------------------------------------------------

test-empty : find-policy (Ongoing []) horizon ≡ Place0
test-empty = refl


