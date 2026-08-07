{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Core.SkillInvestment
--
-- A multi-stage "sacrifice now, gain later" environment with a chain
-- of investment decisions.
--
--   Novice ──Train(r=0)──▸ Apprentice ──Train(r=0)──▸ Expert ──Train(r=0)──▸ Master
--     ⟳ Work(r=1)            ⟳ Work(r=2)                ⟳ Work(r=3)          ⟳ Work(r=5)
--
-- At each level, the agent can Work (earn now, stay at current level)
-- or Train (sacrifice income, advance to the next level).
--
-- Optimal policy: Train at every non-Master state.
--
-- Value streams show a progression:
--   Master:     [5, 5, 5, 5, ...]
--   Expert:     [3, 5, 5, 5, ...]
--   Apprentice: [2, 3, 5, 5, ...]
--   Novice:     [1, 2, 3, 5, ...]
--
-- CoinductiveHomomorphism correctly ranks Train > Work everywhere:
--   value(Novice) ≤ₛ value(Apprentice) ≤ₛ value(Expert) ≤ₛ value(Master)
--
-- CoindHomo cannot rank Train ≥ Work at any non-Master state:
--   the immediate reward of Work always exceeds Train.
------------------------------------------------------------------------

module CSHRL.Tasks.Verified.SkillInvestment where

open import Data.Nat using (ℕ; zero; suc; _⊔_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Codata.Guarded.Stream using (Stream; head; tail; tabulate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)

open import CSHRL.Core
open import CSHRL.Core.CoinductiveHomomorphism

------------------------------------------------------------------------
-- MDP Definition
------------------------------------------------------------------------

data State : Set where
  Novice Apprentice Expert Master : State

data Action : Set where
  Work Train : Action

step : State → Action → State × ℕ
step Novice     Work  = Novice     , 1
step Novice     Train = Apprentice , 0
step Apprentice Work  = Apprentice , 2
step Apprentice Train = Expert     , 0
step Expert     Work  = Expert     , 3
step Expert     Train = Master     , 0
step Master     Work  = Master     , 5
step Master     Train = Master     , 5

all-actions : List Action
all-actions = Work ∷ Train ∷ []

open Core State Action ℕ step _≤_ _⊔_ 0 all-actions
open SuccessorCore State Action ℕ step _≤_ _⊔_ 0 all-actions

------------------------------------------------------------------------
-- Solve stabilization lemmas
--
-- Each state's solve stabilizes to 5 after enough steps.
------------------------------------------------------------------------

solve-master : ∀ n → solve Master n ≡ 5
solve-master zero    = refl
solve-master (suc n) rewrite solve-master n = refl

solve-expert-0 : solve Expert zero ≡ 3
solve-expert-0 = refl

solve-expert-suc : ∀ n → solve Expert (suc n) ≡ 5
solve-expert-suc zero rewrite solve-master zero = refl
solve-expert-suc (suc n) rewrite solve-expert-suc n | solve-master (suc n) = refl

solve-apprentice-0 : solve Apprentice zero ≡ 2
solve-apprentice-0 = refl

solve-apprentice-1 : solve Apprentice 1 ≡ 3
solve-apprentice-1 = refl

solve-apprentice-suc-suc : ∀ n → solve Apprentice (suc (suc n)) ≡ 5
solve-apprentice-suc-suc zero rewrite solve-expert-suc zero = refl
solve-apprentice-suc-suc (suc n)
  rewrite solve-apprentice-suc-suc n | solve-expert-suc (suc n) = refl

solve-novice-0 : solve Novice zero ≡ 1
solve-novice-0 = refl

solve-novice-1 : solve Novice 1 ≡ 2
solve-novice-1 = refl

solve-novice-2 : solve Novice 2 ≡ 3
solve-novice-2 = refl

solve-novice-suc-suc-suc : ∀ n → solve Novice (suc (suc (suc n))) ≡ 5
solve-novice-suc-suc-suc zero
  rewrite solve-apprentice-suc-suc zero = refl
solve-novice-suc-suc-suc (suc n)
  rewrite solve-novice-suc-suc-suc n | solve-apprentice-suc-suc (suc n) = refl

------------------------------------------------------------------------
-- Stream ordering infrastructure
------------------------------------------------------------------------

tabulate-≤ₛ : ∀ {f g : ℕ → ℕ} →
  (∀ n → f n ≤ g n) → tabulate f ≤ₛ tabulate g
head≤ (tabulate-≤ₛ pw) = pw zero
tail≤ (tabulate-≤ₛ pw) = tabulate-≤ₛ (λ n → pw (suc n))

≤ₛ-refl : ∀ (s : StreamR) → s ≤ₛ s
head≤ (≤ₛ-refl s) = ≤-refl
tail≤ (≤ₛ-refl s) = ≤ₛ-refl (tail s)

------------------------------------------------------------------------
-- Pointwise ordering: Novice ≤ Apprentice ≤ Expert ≤ Master
------------------------------------------------------------------------

novice≤apprentice : ∀ n → solve Novice n ≤ solve Apprentice n
novice≤apprentice zero = s≤s z≤n
novice≤apprentice (suc zero) = s≤s (s≤s z≤n)
novice≤apprentice (suc (suc zero)) = s≤s (s≤s (s≤s z≤n))
novice≤apprentice (suc (suc (suc n)))
  rewrite solve-novice-suc-suc-suc n | solve-apprentice-suc-suc (suc n) = ≤-refl

apprentice≤expert : ∀ n → solve Apprentice n ≤ solve Expert n
apprentice≤expert zero rewrite solve-apprentice-0 | solve-expert-0 = s≤s (s≤s z≤n)
apprentice≤expert (suc zero) rewrite solve-apprentice-1 | solve-expert-suc zero = s≤s (s≤s (s≤s z≤n))
apprentice≤expert (suc (suc n))
  rewrite solve-apprentice-suc-suc n | solve-expert-suc (suc n) = ≤-refl

expert≤master : ∀ n → solve Expert n ≤ solve Master n
expert≤master zero rewrite solve-expert-0 | solve-master zero = s≤s (s≤s (s≤s z≤n))
expert≤master (suc n) rewrite solve-expert-suc n | solve-master (suc n) = ≤-refl

------------------------------------------------------------------------
-- Value stream ordering
------------------------------------------------------------------------

value-novice≤apprentice : value Novice ≤ₛ value Apprentice
value-novice≤apprentice = tabulate-≤ₛ novice≤apprentice

value-apprentice≤expert : value Apprentice ≤ₛ value Expert
value-apprentice≤expert = tabulate-≤ₛ apprentice≤expert

value-expert≤master : value Expert ≤ₛ value Master
value-expert≤master = tabulate-≤ₛ expert≤master

------------------------------------------------------------------------
-- ✓ CoinductiveHomomorphism holds
--
-- Train is ranked above Work at every state (except Master
-- where both actions are equivalent and both ranked equally).
------------------------------------------------------------------------

ranking : State → Action → Action → Set
ranking Novice     Train Work = ⊥
ranking Apprentice Train Work = ⊥
ranking Expert     Train Work = ⊥
ranking Master     _ _        = ⊤
ranking _          Work Train = ⊤
ranking _          Work Work  = ⊤
ranking _          Train Train = ⊤

skill-homomorphism : CoinductiveHomomorphism
skill-homomorphism = record { _≤ₐ_ = ranking ; preserves = prf }
  where
    prf : ∀ a b s → ranking s a b →
          successor-value s a ≤ₛ successor-value s b
    prf Work  Train Novice     tt = value-novice≤apprentice
    prf Work  Train Apprentice tt = value-apprentice≤expert
    prf Work  Train Expert     tt = value-expert≤master
    prf Work  Work  Novice     tt = ≤ₛ-refl (value Novice)
    prf Work  Work  Apprentice tt = ≤ₛ-refl (value Apprentice)
    prf Work  Work  Expert     tt = ≤ₛ-refl (value Expert)
    prf Train Train Novice     tt = ≤ₛ-refl (value Apprentice)
    prf Train Train Apprentice tt = ≤ₛ-refl (value Expert)
    prf Train Train Expert     tt = ≤ₛ-refl (value Master)
    prf Train Work  Novice     ()
    prf Train Work  Apprentice ()
    prf Train Work  Expert     ()
    prf Work  Work  Master     tt = ≤ₛ-refl (value Master)
    prf Work  Train Master     tt = ≤ₛ-refl (value Master)
    prf Train Work  Master     tt = ≤ₛ-refl (value Master)
    prf Train Train Master     tt = ≤ₛ-refl (value Master)

------------------------------------------------------------------------
-- ✗ CoindHomo cannot rank Train ≥ Work at any non-Master state
--
-- At Novice: immediate reward Work=1 > Train=0 violates head≤
-- At Apprentice: immediate reward Work=2 > Train=0 violates head≤
-- At Expert: immediate reward Work=3 > Train=0 violates head≤
------------------------------------------------------------------------

coindHomo-novice-impossible :
  (homo : CoindHomo) →
  CoindHomo._≤ₐ_ homo Novice Work Train → ⊥
coindHomo-novice-impossible homo prf
  with head≤ (CoindHomo.preserves homo Work Train Novice prf)
... | ()

coindHomo-apprentice-impossible :
  (homo : CoindHomo) →
  CoindHomo._≤ₐ_ homo Apprentice Work Train → ⊥
coindHomo-apprentice-impossible homo prf
  with head≤ (CoindHomo.preserves homo Work Train Apprentice prf)
... | ()

coindHomo-expert-impossible :
  (homo : CoindHomo) →
  CoindHomo._≤ₐ_ homo Expert Work Train → ⊥
coindHomo-expert-impossible homo prf
  with head≤ (CoindHomo.preserves homo Work Train Expert prf)
... | ()
