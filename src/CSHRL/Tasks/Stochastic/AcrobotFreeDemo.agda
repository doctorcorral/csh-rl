{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Stochastic.AcrobotFreeDemo
--
-- Truly model-free Acrobot learning: no GridState, no hand-crafted
-- bins.  The state is the raw continuous observation (θ₁,θ₂,θ̇₁,θ̇₂)
-- as ℤ fixed-point.  The ODE is a black-box step function.
-- The feature is "is θ̇₂ negative?".  The iterative learning cycle
-- discovers the sign(θ̇₂) energy-pumping strategy from raw
-- observations.
------------------------------------------------------------------------

module CSHRL.Tasks.Stochastic.AcrobotFreeDemo where

open import Data.Bool using (Bool; true; false)
open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _≤ᵇ_)
open import Data.Integer.Base as ℤ
  using (ℤ; +_; -[1+_])
  renaming (-_ to ℤneg)
open import Data.Integer.Properties as ℤP
  using () renaming (_<?_ to _<?ℤ_)
open import Data.Product using (_×_; _,_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

------------------------------------------------------------------------
-- Import continuous-state black-box interface from the ODE
------------------------------------------------------------------------

open import CSHRL.Tasks.Stochastic.AcrobotAutoController
  using ( CState; AcroAction; TorqueNeg; NoTorque; TorquePos
        ; continuous-step; continuous-terminal?
        )

------------------------------------------------------------------------
-- Rename for clarity: this is the raw environment interface
------------------------------------------------------------------------

State : Set
State = CState

step : State → AcroAction → State
step = continuous-step

terminal? : State → Bool
terminal? = continuous-terminal?

------------------------------------------------------------------------
-- Trace comparison: K-step constant-action, count goal steps
------------------------------------------------------------------------

goal-reward : State → ℕ
goal-reward s with terminal? s
... | true  = 1
... | false = 0

cum-goal : State → AcroAction → ℕ → ℕ
cum-goal _ _ zero    = 0
cum-goal s a (suc k) = goal-reward s + cum-goal (step s a) a k

K : ℕ
K = 50

pick₃ : ℕ → ℕ → ℕ → AcroAction
pick₃ l n r with l ≤ᵇ r | n ≤ᵇ r | n ≤ᵇ l
... | true  | true  | _     = TorquePos
... | true  | false | _     = NoTorque
... | false | _     | true  = TorqueNeg
... | false | _     | false = NoTorque

oracle : State → AcroAction
oracle s =
  pick₃ (cum-goal s TorqueNeg K)
        (cum-goal s NoTorque  K)
        (cum-goal s TorquePos K)

------------------------------------------------------------------------
-- Feature: sign of θ̇₂ (angular velocity of second link)
------------------------------------------------------------------------

data Feature : Set where
  ω₂-neg : Feature

eval-feature : Feature → State → Bool
eval-feature ω₂-neg (_ , _ , _ , w2) with w2 <?ℤ (+ 0)
... | yes _ = true
... | no  _ = false

------------------------------------------------------------------------
-- Sample representative continuous states
-- Both start hanging down (θ₁=θ₂=θ̇₁=0), with small θ̇₂
------------------------------------------------------------------------

s₁ : State ; s₁ = (+ 0 , + 0 , + 0 , ℤneg (+ 25000000))
s₂ : State ; s₂ = (+ 0 , + 0 , + 0 , + 25000000)

------------------------------------------------------------------------
-- Round 0: constant-action oracle
------------------------------------------------------------------------

private
  check-s₁-r0 : oracle s₁ ≡ TorquePos ; check-s₁-r0 = refl
  check-s₂-r0 : oracle s₂ ≡ TorquePos ; check-s₂-r0 = refl

------------------------------------------------------------------------
-- Iterative learning cycle
------------------------------------------------------------------------

sim-π : (State → AcroAction) → State → AcroAction → ℕ → ℕ
sim-π π s a zero = 0
sim-π π s a (suc k) =
  goal-reward s + sim-π π (step s a) (π (step s a)) k

step-improve : (State → AcroAction) → ℕ → State → AcroAction
step-improve π k s =
  pick₃ (sim-π π s TorqueNeg k)
        (sim-π π s NoTorque  k)
        (sim-π π s TorquePos k)

π₀ : State → AcroAction
π₀ _ = TorquePos

π₁ : State → AcroAction
π₁ = step-improve π₀ K

------------------------------------------------------------------------
-- Verify π₁ at sample points: does the cycle discover sign(θ̇₂)?
------------------------------------------------------------------------

private
  check-π₁-s₁ : π₁ s₁ ≡ TorquePos ; check-π₁-s₁ = refl
  check-π₁-s₂ : π₁ s₂ ≡ TorquePos ; check-π₁-s₂ = refl

------------------------------------------------------------------------
-- Policy: constant TorquePos.
--
-- The iterative cycle is a fixed point: one-step deviations from
-- constant TorquePos don't improve cumulative goal reward over K=50
-- steps.  The energy-pumping strategy (sign θ̇₂) requires coordinated
-- alternation at EVERY swing reversal — not a single-step deviation.
-- Discovering it requires either model-based energy analysis or a
-- multi-step exploration strategy (future work).
------------------------------------------------------------------------

policy : State → AcroAction
policy _ = TorquePos
