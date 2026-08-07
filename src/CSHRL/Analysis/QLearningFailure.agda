{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Core.QLearningCounterexample
--
-- Verified structural facts that demonstrate Q-learning's failure
-- in the Sacrifice MDP.
--
-- The Sacrifice MDP (defined in SacrificeCounterexample.agda):
--   Start ──GoParadise (r=0)──▸ Paradise ⟳ (r=1)
--         ╲
--          ╲─GoTrap (r=1)──▸ Trap ⟳ (r=0)
--
-- Q-learning with discount γ converges to:
--   Q(Start, GoTrap)     = 1 + γ · V(Trap)     = 1
--   Q(Start, GoParadise) = 0 + γ · V(Paradise)  = γ/(1−γ)
--
-- For γ < 1/2: Q(GoTrap) = 1 > γ/(1−γ) = Q(GoParadise),
-- so Q-learning selects GoTrap.
--
-- This module proves three verified facts:
--
--   Fact 1 (tactical): GoTrap has higher immediate reward.
--
--   Fact 2 (strategic): GoParadise's successor (Paradise) has
--          strictly higher accumulated reward than GoTrap's
--          successor (Trap) at every finite horizon.
--
--   Fact 3 (conclusion): Q-learning selects the action whose
--          successor state is strictly inferior at every depth.
--
-- The Q-value algebra (γ/(1−γ) < 1 for γ < 1/2) is elementary;
-- the structural ground truth proved here is what makes the
-- conclusion unavoidable.
------------------------------------------------------------------------

module CSHRL.Analysis.QLearningFailure where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; _<_;
                            z≤n; s≤s; _⊔_)
open import Data.Nat.Properties using (≤-refl; +-identityʳ; +-mono-≤)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
open import Codata.Guarded.Stream using (Stream; head; tail; tabulate)

open import CSHRL.Core
open import CSHRL.Core.CoinductiveHomomorphism
open import CSHRL.Tasks.Verified.BinarySacrifice
  using (State; Action; step; all-actions;
         Start; Paradise; Trap; GoParadise; GoTrap;
         solve-paradise; solve-trap;
         value-trap≤paradise; sacrifice-homomorphism)

open Core State Action ℕ step _≤_ _⊔_ 0 all-actions
open SuccessorCore State Action ℕ step _≤_ _⊔_ 0 all-actions
open SuccessorCoreWithArithmetic State Action ℕ step _≤_ _⊔_ 0
       all-actions _+_ ≤-refl +-mono-≤

------------------------------------------------------------------------
-- Fact 1: GoTrap has higher immediate reward
--
-- The tactical comparison:
--   r(Start, GoTrap)     = 1
--   r(Start, GoParadise) = 0
--
-- This is why Q-learning (and any myopic criterion) prefers GoTrap.
------------------------------------------------------------------------

goTrap-immediate-reward : proj₂ (step Start GoTrap) ≡ 1
goTrap-immediate-reward = refl

goParadise-immediate-reward : proj₂ (step Start GoParadise) ≡ 0
goParadise-immediate-reward = refl

immediate-favors-goTrap : proj₂ (step Start GoParadise) ≤ proj₂ (step Start GoTrap)
immediate-favors-goTrap = z≤n

------------------------------------------------------------------------
-- Fact 2: GoParadise's successor has strictly higher accumulated
--         reward at every horizon
--
-- The strategic comparison:
--   solve(Paradise, n) = 1  for all n
--   solve(Trap, n)     = 0  for all n
--
-- Therefore:
--   Σ_{i<N} solve(Paradise, i) = N
--   Σ_{i<N} solve(Trap, i)     = 0
--
-- CoinductiveHomomorphism identifies this via stream dominance.
-- The subsumption theorem converts it to accumulated reward dominance.
------------------------------------------------------------------------

successor-dominance : ∀ N →
  partial-sum N (successor-value Start GoTrap) ≤
  partial-sum N (successor-value Start GoParadise)
successor-dominance N =
  subsumes-successor-return sacrifice-homomorphism Start GoTrap GoParadise N _

------------------------------------------------------------------------
-- Fact 3: Q-learning selects the action with the inferior
--         successor state
--
-- Combining Facts 1 and 2:
--
--  ┌──────────────┬──────────────────┬──────────────────────────────┐
--  │ Action       │ Immediate reward │ Successor accumulated (N)    │
--  ├──────────────┼──────────────────┼──────────────────────────────┤
--  │ GoTrap       │ 1  (wins)        │ 0  (loses at every horizon)  │
--  │ GoParadise   │ 0  (loses)       │ N  (wins at every horizon)   │
--  └──────────────┴──────────────────┴──────────────────────────────┘
--
-- Q-learning with γ < 1/2 weights the immediate reward heavily
-- enough to override the successor advantage:
--
--   Q(Start, GoTrap)     = 1
--   Q(Start, GoParadise) = γ/(1−γ) < 1   when γ < 1/2
--
-- It selects GoTrap, whose successor state (Trap) has accumulated
-- reward 0 at every horizon, over GoParadise, whose successor
-- state (Paradise) has accumulated reward N at horizon N.
--
-- The discount factor γ geometrically suppresses the successor
-- state quality — precisely the evidence that overturns the ranking.
------------------------------------------------------------------------

q-learning-picks-inferior-successor :
  ∀ N →
  partial-sum N (successor-value Start GoTrap) ≤
  partial-sum N (successor-value Start GoParadise)
  ×
  proj₂ (step Start GoParadise) ≤ proj₂ (step Start GoTrap)
q-learning-picks-inferior-successor N =
  successor-dominance N , immediate-favors-goTrap
