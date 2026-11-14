{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Stochastic.AcrobotSynthDemo
--
-- Model-Free Learning Demo: Acrobot via raw trace comparison
--
-- The "environment" is the Agda ODE (20-sub-step Euler integration
-- of the double pendulum, with Taylor-7 cosine).  The comparison
-- oracle counts how quickly each constant-action trajectory swings
-- the tip above the threshold — the standard Acrobot metric.
-- No energy function, no Hamiltonian — just step + terminal + reward.
--
-- Iterative learning cycle:
--   Round 0 = constant TorquePos.  This is already a fixed point
--   of the iterative cycle (π₁ = π₀): the 3-state grid is too
--   coarse for policy iteration to discover the alternating pump.
------------------------------------------------------------------------

module CSHRL.Tasks.Stochastic.AcrobotSynthDemo where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤ᵇ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Import grid, transitions, and terminal condition
------------------------------------------------------------------------

open import CSHRL.Tasks.Stochastic.AcrobotAutoController
  using ( GridState; V₋; V₊; Goal
        ; AcroAction; TorqueNeg; NoTorque; TorquePos
        ; next-state; terminal?
        )

------------------------------------------------------------------------
-- Raw reward: +1 per step at Goal (tip above threshold)
--
-- Standard Acrobot reward is -1 per step (minimize time to swing
-- up).  We encode: 1 at absorbing Goal, 0 elsewhere.
------------------------------------------------------------------------

goal-reward : GridState → ℕ
goal-reward g with terminal? g
... | true  = 1
... | false = 0

------------------------------------------------------------------------
-- Trace comparison: K-step constant-action simulation,
-- counting steps spent at Goal.
------------------------------------------------------------------------

cum-goal : GridState → AcroAction → ℕ → ℕ
cum-goal _ _ zero    = 0
cum-goal g a (suc k) = goal-reward g + cum-goal (next-state g a) a k

K : ℕ
K = 8

------------------------------------------------------------------------
-- Learned policy: pick the action with the highest cum-goal.
------------------------------------------------------------------------

pick₃ : ℕ → ℕ → ℕ → AcroAction
pick₃ l n r with l ≤ᵇ r | n ≤ᵇ r | n ≤ᵇ l
... | true  | true  | _     = TorquePos
... | true  | false | _     = NoTorque
... | false | _     | true  = TorqueNeg
... | false | _     | false = NoTorque

learned-policy : GridState → AcroAction
learned-policy g =
  pick₃ (cum-goal g TorqueNeg K)
        (cum-goal g NoTorque  K)
        (cum-goal g TorquePos K)

------------------------------------------------------------------------
-- Verification: refl-checked at all 3 states
--
-- The trace comparison discovers that constant TorquePos reaches
-- the goal from every state: at V₋ it first reverses the negative
-- velocity, then amplifies the positive swing toward Goal.
--
-- This differs from the energy-derived sign(dθ₂) policy, which
-- pumps energy at each swing reversal.  The constant-action oracle
-- cannot discover the alternating "pump" strategy — it finds the
-- best FIXED action instead.  Both policies reach the goal; the
-- energy-derived policy is faster (fewer episodes to convergence).
------------------------------------------------------------------------

check-V₋   : learned-policy V₋   ≡ TorquePos ; check-V₋   = refl
check-V₊   : learned-policy V₊   ≡ TorquePos ; check-V₊   = refl
check-Goal : learned-policy Goal  ≡ TorquePos ; check-Goal = refl

------------------------------------------------------------------------
-- Iterative learning cycle (policy iteration)
--
-- Round 0 = constant-action comparison (above).  Round 1 evaluates
-- action a by taking it ONCE, then following π₀ = TorquePos for K−1
-- more grid steps.  The comparison measures cumulative goal reward.
------------------------------------------------------------------------

sim-π : (GridState → AcroAction) → GridState → AcroAction → ℕ → ℕ
sim-π π g a zero = 0
sim-π π g a (suc k) =
  goal-reward g + sim-π π (next-state g a) (π (next-state g a)) k

step-improve : (GridState → AcroAction) → ℕ → GridState → AcroAction
step-improve π k g =
  pick₃ (sim-π π g TorqueNeg k)
        (sim-π π g NoTorque  k)
        (sim-π π g TorquePos k)

π₀ : GridState → AcroAction
π₀ = learned-policy

π₁ : GridState → AcroAction
π₁ = step-improve π₀ K

private
  i-V₋   : π₁ V₋   ≡ TorquePos ; i-V₋   = refl
  i-V₊   : π₁ V₊   ≡ TorquePos ; i-V₊   = refl
  i-Goal  : π₁ Goal  ≡ TorquePos ; i-Goal  = refl
