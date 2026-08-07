{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Core.PreparationDilemma
--
-- A cyclic "sacrifice now, gain later" environment with regression
-- and context-dependent optimal actions.
--
--                Rush(r=1)
--                  ⟲
--   [Idle] ──Prepare(r=0)──▸ [Ready] ──Rush(r=3)──▸ [Producing] ⟲ (r=3)
--     ▲                        │
--     └────Prepare(r=0)────────┘
--            (over-prepare)
--
-- At Idle:  Rush earns 1 but stays idle forever (temptation).
--           Prepare sacrifices income to reach Ready.
-- At Ready: Rush capitalizes on preparation → enters Producing.
--           Over-preparing resets back to Idle (regression).
--
-- Optimal policy: Prepare at Idle, Rush at Ready.
--
-- Unlike the SkillInvestment chain, this environment features:
--   • Cyclic state transitions (Ready→Idle regression)
--   • Context-dependent optimal action (Prepare vs Rush flips)
--   • Temptation to abandon preparation at every step
--
-- Value streams:
--   Producing: [3, 3, 3, ...]
--   Ready:     [3, 3, 3, ...]
--   Idle:      [1, 3, 3, ...]
--
-- CoinductiveHomomorphism ranks Prepare > Rush at Idle because
--   value(Idle) ≤ₛ value(Ready)
-- and ranks Rush > Prepare at Ready because
--   value(Idle) ≤ₛ value(Producing)
--
-- CoindHomo cannot rank Rush ≤ Prepare at Idle in either direction.
------------------------------------------------------------------------

module CSHRL.Tasks.Verified.PreparationDilemma where

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
  Idle Ready Producing : State

data Action : Set where
  Rush Prepare : Action

step : State → Action → State × ℕ
step Idle      Rush    = Idle      , 1
step Idle      Prepare = Ready     , 0
step Ready     Rush    = Producing , 3
step Ready     Prepare = Idle      , 0
step Producing Rush    = Producing , 3
step Producing Prepare = Producing , 3

all-actions : List Action
all-actions = Rush ∷ Prepare ∷ []

open Core State Action ℕ step _≤_ _⊔_ 0 all-actions
open SuccessorCore State Action ℕ step _≤_ _⊔_ 0 all-actions

------------------------------------------------------------------------
-- Solve stabilization lemmas
------------------------------------------------------------------------

solve-producing : ∀ n → solve Producing n ≡ 3
solve-producing zero    = refl
solve-producing (suc n) rewrite solve-producing n = refl

solve-ready-zero : solve Ready zero ≡ 3
solve-ready-zero = refl

solve-idle-zero : solve Idle zero ≡ 1
solve-idle-zero = refl

-- Ready and Idle stabilize mutually after one step.
mutual
  solve-ready-suc : ∀ n → solve Ready (suc n) ≡ 3
  solve-ready-suc zero rewrite solve-producing zero = refl
  solve-ready-suc (suc n) rewrite solve-producing (suc n) | solve-idle-suc n = refl

  solve-idle-suc : ∀ n → solve Idle (suc n) ≡ 3
  solve-idle-suc zero rewrite solve-ready-zero = refl
  solve-idle-suc (suc n) rewrite solve-idle-suc n | solve-ready-suc n = refl

solve-ready : ∀ n → solve Ready n ≡ 3
solve-ready zero    = refl
solve-ready (suc n) = solve-ready-suc n

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
-- Pointwise ordering: Idle ≤ Ready = Producing
------------------------------------------------------------------------

idle≤ready : ∀ n → solve Idle n ≤ solve Ready n
idle≤ready zero = s≤s z≤n
idle≤ready (suc n) rewrite solve-idle-suc n | solve-ready-suc n = ≤-refl

idle≤producing : ∀ n → solve Idle n ≤ solve Producing n
idle≤producing zero = s≤s z≤n
idle≤producing (suc n) rewrite solve-idle-suc n | solve-producing (suc n) = ≤-refl

------------------------------------------------------------------------
-- Value stream orderings
------------------------------------------------------------------------

value-idle≤ready : value Idle ≤ₛ value Ready
value-idle≤ready = tabulate-≤ₛ idle≤ready

value-idle≤producing : value Idle ≤ₛ value Producing
value-idle≤producing = tabulate-≤ₛ idle≤producing

------------------------------------------------------------------------
-- ✓ CoinductiveHomomorphism holds
--
-- At Idle:      Prepare > Rush   (Ready is better than Idle)
-- At Ready:     Rush > Prepare   (Producing is better than Idle)
-- At Producing: both equivalent  (both lead to Producing)
------------------------------------------------------------------------

ranking : State → Action → Action → Set
ranking Idle      Rush    Prepare = ⊤
ranking Idle      Prepare Rush    = ⊥
ranking Ready     Prepare Rush    = ⊤
ranking Ready     Rush    Prepare = ⊥
ranking _         Rush    Rush    = ⊤
ranking _         Prepare Prepare = ⊤
ranking Producing Rush    Prepare = ⊤
ranking Producing Prepare Rush    = ⊤

preparation-homomorphism : CoinductiveHomomorphism
preparation-homomorphism = record { _≤ₐ_ = ranking ; preserves = prf }
  where
    prf : ∀ a b s → ranking s a b →
          successor-value s a ≤ₛ successor-value s b
    prf Rush    Prepare Idle      tt = value-idle≤ready
    prf Prepare Rush    Ready     tt = value-idle≤producing
    prf Rush    Rush    Idle      tt = ≤ₛ-refl (value Idle)
    prf Prepare Prepare Idle      tt = ≤ₛ-refl (value Ready)
    prf Rush    Rush    Ready     tt = ≤ₛ-refl (value Producing)
    prf Prepare Prepare Ready     tt = ≤ₛ-refl (value Idle)
    prf Rush    Rush    Producing tt = ≤ₛ-refl (value Producing)
    prf Rush    Prepare Producing tt = ≤ₛ-refl (value Producing)
    prf Prepare Rush    Producing tt = ≤ₛ-refl (value Producing)
    prf Prepare Prepare Producing tt = ≤ₛ-refl (value Producing)
    prf Prepare Rush    Idle      ()
    prf Rush    Prepare Ready     ()

------------------------------------------------------------------------
-- ✗ CoindHomo cannot rank Rush ≤ Prepare at Idle
--
-- Forward (Rush ≤ₐ Prepare): head≤ requires reward(Rush) ≤ reward(Prepare)
--   i.e. 1 ≤ 0 — absurd.
--
-- Reverse (Prepare ≤ₐ Rush): head≤ gives 0 ≤ 1 (ok), but tail≤
--   requires value(Ready) ≤ₛ value(Idle). At the head:
--   solve Ready 0 ≤ solve Idle 0 = 3 ≤ 1 — absurd.
------------------------------------------------------------------------

coindHomo-idle-forward-impossible :
  (homo : CoindHomo) →
  CoindHomo._≤ₐ_ homo Idle Rush Prepare → ⊥
coindHomo-idle-forward-impossible homo prf
  with head≤ (CoindHomo.preserves homo Rush Prepare Idle prf)
... | ()

coindHomo-idle-reverse-impossible :
  (homo : CoindHomo) →
  CoindHomo._≤ₐ_ homo Idle Prepare Rush → ⊥
coindHomo-idle-reverse-impossible homo prf
  with head≤ (tail≤ (CoindHomo.preserves homo Prepare Rush Idle prf))
... | s≤s ()
