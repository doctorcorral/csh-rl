{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- Two-State MDP: Minimal Verified Example
------------------------------------------------------------------------

module CSHRL.Tasks.Verified.TwoState where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _≤_; _⊔_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; m≤m⊔n; n≤m⊔n)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; sym)
open import Codata.Guarded.Stream using (Stream; head; tail; tabulate)
open import Function using (_∘_)
open import Data.List using (List; _∷_; [])
open import Relation.Nullary using (Dec; yes; no; ¬_)

------------------------------------------------------------------------
-- Domain
------------------------------------------------------------------------

data State : Set where
  Start : State
  Goal  : State

data Action : Set where
  Go   : Action
  Stay : Action

Reward : Set
Reward = ℕ

_≤ᵣ_ : Reward → Reward → Set
n ≤ᵣ m = n ≤ m

-- Decidable ordering
_≤?_ : (m n : Reward) → Dec (m ≤ᵣ n)
zero  ≤? _     = yes z≤n
suc _ ≤? zero  = no λ()
suc m ≤? suc n with m ≤? n
... | yes p = yes (s≤s p)
... | no ¬p = no λ{ (s≤s p) → ¬p p }

move : State → Action → State
move Start Go   = Goal
move Start Stay = Start
move Goal  _    = Goal

reward-fn : State → Reward
reward-fn Goal  = 1
reward-fn Start = 0

step : State → Action → State × Reward
step s a = (move s a , reward-fn (move s a))

all-actions : List Action
all-actions = Go ∷ Stay ∷ []

------------------------------------------------------------------------
-- Environment Class
------------------------------------------------------------------------

open import CSHRL.EnvironmentClass.FiniteDeterministicMDP

horizon : ℕ
horizon = 1

open FiniteDeterministicMDP 
  State Action Reward step
  _≤ᵣ_ _≤?_ (λ {r} → ≤-refl) _⊔_ 0
  all-actions Go
  horizon

------------------------------------------------------------------------
-- solve is always 1 for this MDP (by induction)
------------------------------------------------------------------------

-- Key lemmas about ⊔
⊔-idem : ∀ n → n ⊔ n ≡ n
⊔-idem zero = refl
⊔-idem (suc n) = cong suc (⊔-idem n)

1⊔0≡1 : 1 ⊔ 0 ≡ 1
1⊔0≡1 = refl

1⊔1≡1 : 1 ⊔ 1 ≡ 1
1⊔1≡1 = refl

-- solve Goal n = 1 for all n (by induction)
solve-Goal-is-1 : ∀ n → solve Goal n ≡ 1
solve-Goal-is-1 zero = refl  -- 1 ⊔ 1 ⊔ 0 = 1
solve-Goal-is-1 (suc n) = 
  cong (λ x → x ⊔ (x ⊔ 0)) (solve-Goal-is-1 n)

-- solve Start n = 1 for all n (by induction, using solve-Goal-is-1)
solve-Start-is-1 : ∀ n → solve Start n ≡ 1
solve-Start-is-1 zero = refl  -- 1 ⊔ 0 ⊔ 0 = 1
solve-Start-is-1 (suc n) = 
  subst (λ x → x ⊔ (solve Start n ⊔ 0) ≡ 1) 
        (sym (solve-Goal-is-1 n))
        (subst (λ x → 1 ⊔ (x ⊔ 0) ≡ 1) 
               (sym (solve-Start-is-1 n)) 
               refl)

-- Unified: solve s n = 1 for all s, n
solve-is-1 : ∀ s n → solve s n ≡ 1
solve-is-1 Start = solve-Start-is-1
solve-is-1 Goal = solve-Goal-is-1

------------------------------------------------------------------------
-- iter-head at value streams
------------------------------------------------------------------------

iter-head : ℕ → StreamR → Reward
iter-head zero s = head s
iter-head (suc n) s = iter-head n (tail s)

-- iter-head n (value s) = solve s n
-- The proof relies on:
-- - value s = tabulate (solve s)
-- - head (tabulate f) = f 0
-- - tail (tabulate f) = tabulate (f ∘ suc)
-- - iter-head n (tabulate f) = f n

iter-head-tabulate : ∀ (f : ℕ → ℕ) n → iter-head n (tabulate f) ≡ f n
iter-head-tabulate f zero = refl
iter-head-tabulate f (suc n) = iter-head-tabulate (f ∘ suc) n

iter-head-value : ∀ s n → iter-head n (value s) ≡ solve s n
iter-head-value s n = iter-head-tabulate (solve s) n

-- Actually, let's check: head (tail (value s)) = solve s 1
-- tail (value s) = tabulate (solve s ∘ suc)
-- head (tail (value s)) = solve s 1
-- So iter-head 1 (value s) = head (tail (value s)) = solve s 1 ✓

-- iter-head n (value s) = 1 for all s, n
iter-head-is-1 : ∀ s n → iter-head n (value s) ≡ 1
iter-head-is-1 s n = subst (λ x → x ≡ 1) (sym (iter-head-value s n)) (solve-is-1 s n)

------------------------------------------------------------------------
-- Head Generator and Build
------------------------------------------------------------------------

HeadGen : StreamR → StreamR → Set
HeadGen s₁ s₂ = ∀ n → iter-head n s₁ ≤ iter-head n s₂

shift-gen : ∀ {s₁ s₂} → HeadGen s₁ s₂ → HeadGen (tail s₁) (tail s₂)
shift-gen gen n = gen (suc n)

build-≤ₛ : ∀ (s₁ s₂ : StreamR) → HeadGen s₁ s₂ → s₁ ≤ₛ s₂
head≤ (build-≤ₛ s₁ s₂ gen) = gen 0
tail≤ (build-≤ₛ s₁ s₂ gen) = build-≤ₛ (tail s₁) (tail s₂) (shift-gen gen)

------------------------------------------------------------------------
-- Head Generator for TwoState
------------------------------------------------------------------------

gen-Start-Goal : HeadGen (value Start) (value Goal)
gen-Start-Goal n = 
  subst (λ x → x ≤ iter-head n (value Goal)) 
        (sym (iter-head-is-1 Start n))  -- 1 ≡ iter-head n (value Start)
        (subst (λ x → 1 ≤ x) 
               (sym (iter-head-is-1 Goal n))  -- 1 ≡ iter-head n (value Goal)
               ≤-refl)

------------------------------------------------------------------------
-- Value Orderings
------------------------------------------------------------------------

Start-≤-Goal : value Start ≤ₛ value Goal
Start-≤-Goal = build-≤ₛ (value Start) (value Goal) gen-Start-Goal

------------------------------------------------------------------------
-- Preservation Proof
------------------------------------------------------------------------

direct-preserves : ∀ a b s → 
                   s ranks a ≤ b → 
                   action-value s a ≤ₛ action-value s b

-- From Goal
head≤ (direct-preserves Go   Go   Goal p) = ≤-refl
tail≤ (direct-preserves Go   Go   Goal p) = ≤ₛ-refl (value Goal)
head≤ (direct-preserves Go   Stay Goal p) = ≤-refl
tail≤ (direct-preserves Go   Stay Goal p) = ≤ₛ-refl (value Goal)
head≤ (direct-preserves Stay Go   Goal p) = ≤-refl
tail≤ (direct-preserves Stay Go   Goal p) = ≤ₛ-refl (value Goal)
head≤ (direct-preserves Stay Stay Goal p) = ≤-refl
tail≤ (direct-preserves Stay Stay Goal p) = ≤ₛ-refl (value Goal)

-- From Start
head≤ (direct-preserves Go   Go   Start p) = ≤-refl
tail≤ (direct-preserves Go   Go   Start p) = ≤ₛ-refl (value Goal)
head≤ (direct-preserves Go   Stay Start ())
head≤ (direct-preserves Stay Go   Start p) = z≤n
tail≤ (direct-preserves Stay Go   Start p) = Start-≤-Goal
head≤ (direct-preserves Stay Stay Start p) = ≤-refl
tail≤ (direct-preserves Stay Stay Start p) = ≤ₛ-refl (value Start)

------------------------------------------------------------------------
-- Verified Instance
------------------------------------------------------------------------

open WithDirectPreservation direct-preserves public

------------------------------------------------------------------------
-- Tests
------------------------------------------------------------------------

test-Start : find-policy Start horizon ≡ Go
test-Start = refl

