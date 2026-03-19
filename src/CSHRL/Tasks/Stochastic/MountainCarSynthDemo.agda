{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Stochastic.MountainCarSynthDemo
--
-- Model-Free Learning Demo: MountainCar via raw trace comparison
--
-- The "environment" is the Agda ODE (25-step Euler integration
-- with Taylor-7 cosine, verified in MountainCarAutoController).
-- The comparison oracle counts how quickly each constant-action
-- trajectory reaches the goal — the standard MountainCar metric.
-- No energy function, no Hamiltonian — just step + terminal + reward.
--
-- Iterative learning cycle:
--   Round 0 = constant PushRight (best fixed action).
--   Round 1 = "take a, then follow PushRight": discovers PushLeft
--   at VBN and NRN — the sign(v) swing strategy emerges from raw
--   observations.  Converges at round 1 (π₁ = π₂).
------------------------------------------------------------------------

module CSHRL.Tasks.Stochastic.MountainCarSynthDemo where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤ᵇ_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Import grid, transitions, and terminal condition
------------------------------------------------------------------------

open import CSHRL.Tasks.Stochastic.MountainCarAutoController
  using ( GridState
        ; FLN; FLP; MLN; MLP; VBN; VBP
        ; NRN; NRP; CRN; CRP; GoalN; Terminal
        ; MCAction; PushLeft; NoAction; PushRight
        ; next-state; terminal?
        )

------------------------------------------------------------------------
-- Raw reward: +1 per step at Terminal (goal reached)
--
-- MountainCar's standard reward is -1 per step (minimize time to
-- goal).  In ℕ, we encode this as: reward 1 at the absorbing
-- goal state, 0 elsewhere.  Cumulative reward = time spent at
-- goal = K minus steps-to-reach-goal.  Higher is better.
------------------------------------------------------------------------

goal-reward : GridState → ℕ
goal-reward g with terminal? g
... | true  = 1
... | false = 0

------------------------------------------------------------------------
-- Trace comparison: simulate K grid steps with constant action,
-- count steps spent at Terminal (absorbing goal state).
------------------------------------------------------------------------

cum-goal : GridState → MCAction → ℕ → ℕ
cum-goal _ _ zero    = 0
cum-goal g a (suc k) = goal-reward g + cum-goal (next-state g a) a k

K : ℕ
K = 8

------------------------------------------------------------------------
-- Learned policy: pick the action with the highest cum-goal.
-- With 3 actions, we compare all three and take the argmax.
------------------------------------------------------------------------

pick₃ : ℕ → ℕ → ℕ → MCAction
pick₃ l n r with l ≤ᵇ r | n ≤ᵇ r | n ≤ᵇ l
... | true  | true  | _     = PushRight
... | true  | false | _     = NoAction
... | false | _     | true  = PushLeft
... | false | _     | false = NoAction

learned-policy : GridState → MCAction
learned-policy g =
  pick₃ (cum-goal g PushLeft  K)
        (cum-goal g NoAction  K)
        (cum-goal g PushRight K)

------------------------------------------------------------------------
-- Verification: refl-checked at all 12 states
--
-- The trace comparison discovers that PushRight is the best
-- constant-action policy from every state: it consistently reaches
-- the goal faster than PushLeft or NoAction.
--
-- This is the model-free discovery: without knowing the energy
-- landscape, the oracle finds that pushing toward the goal is
-- optimal.  The car builds momentum by bouncing off the left wall
-- and riding the slope rightward to the goal.
------------------------------------------------------------------------

check-FLN   : learned-policy FLN   ≡ PushRight ; check-FLN   = refl
check-FLP   : learned-policy FLP   ≡ PushRight ; check-FLP   = refl
check-MLN   : learned-policy MLN   ≡ PushRight ; check-MLN   = refl
check-MLP   : learned-policy MLP   ≡ PushRight ; check-MLP   = refl
check-VBN   : learned-policy VBN   ≡ PushRight ; check-VBN   = refl
check-VBP   : learned-policy VBP   ≡ PushRight ; check-VBP   = refl
check-NRN   : learned-policy NRN   ≡ PushRight ; check-NRN   = refl
check-NRP   : learned-policy NRP   ≡ PushRight ; check-NRP   = refl
check-CRN   : learned-policy CRN   ≡ PushRight ; check-CRN   = refl
check-CRP   : learned-policy CRP   ≡ PushRight ; check-CRP   = refl
check-GoalN : learned-policy GoalN ≡ PushRight ; check-GoalN = refl
check-Term  : learned-policy Terminal ≡ PushRight ; check-Term = refl

------------------------------------------------------------------------
-- Iterative learning cycle (policy iteration)
--
-- Round 0 = constant-action comparison (above).  Round 1 evaluates
-- action a by taking it ONCE, then following π₀ = PushRight for K−1
-- more grid steps (each grid step = 25 Euler sub-steps = 1 env step).
-- The comparison measures cumulative goal reward: how quickly the
-- trajectory reaches Terminal.
------------------------------------------------------------------------

sim-π : (GridState → MCAction) → GridState → MCAction → ℕ → ℕ
sim-π π g a zero = 0
sim-π π g a (suc k) =
  goal-reward g + sim-π π (next-state g a) (π (next-state g a)) k

step-improve : (GridState → MCAction) → ℕ → GridState → MCAction
step-improve π k g =
  pick₃ (sim-π π g PushLeft  k)
        (sim-π π g NoAction  k)
        (sim-π π g PushRight k)

π₀ : GridState → MCAction
π₀ = learned-policy

π₁ : GridState → MCAction
π₁ = step-improve π₀ K

------------------------------------------------------------------------
-- Round 1 result: the cycle discovers PushLeft at two negative-
-- velocity states (VBN, NRN).  "PushLeft then PushRight" builds
-- leftward momentum for the swing — the trajectory bounces off the
-- left wall and rides PushRight up the right hill FASTER than
-- constant PushRight alone.  This is the sign(v) strategy emerging
-- from raw observations, with no energy function.
------------------------------------------------------------------------

private
  i-FLN   : π₁ FLN   ≡ PushRight ; i-FLN   = refl
  i-FLP   : π₁ FLP   ≡ PushRight ; i-FLP   = refl
  i-MLN   : π₁ MLN   ≡ PushRight ; i-MLN   = refl
  i-MLP   : π₁ MLP   ≡ PushRight ; i-MLP   = refl
  i-VBN   : π₁ VBN   ≡ PushLeft  ; i-VBN   = refl
  i-VBP   : π₁ VBP   ≡ PushRight ; i-VBP   = refl
  i-NRN   : π₁ NRN   ≡ PushLeft  ; i-NRN   = refl
  i-NRP   : π₁ NRP   ≡ PushRight ; i-NRP   = refl
  i-CRN   : π₁ CRN   ≡ PushRight ; i-CRN   = refl
  i-CRP   : π₁ CRP   ≡ PushRight ; i-CRP   = refl
  i-GoalN : π₁ GoalN ≡ PushRight ; i-GoalN = refl
  i-Term  : π₁ Terminal ≡ PushRight ; i-Term  = refl

-- Hard-coded lookup table for π₁ (avoids recomputation in π₂)
π₁-tab : GridState → MCAction
π₁-tab VBN = PushLeft
π₁-tab NRN = PushLeft
π₁-tab _   = PushRight

π₂ : GridState → MCAction
π₂ = step-improve π₁-tab K

private
  j-FLN   : π₂ FLN   ≡ PushRight ; j-FLN   = refl
  j-FLP   : π₂ FLP   ≡ PushRight ; j-FLP   = refl
  j-MLN   : π₂ MLN   ≡ PushRight ; j-MLN   = refl
  j-MLP   : π₂ MLP   ≡ PushRight ; j-MLP   = refl
  j-VBN   : π₂ VBN   ≡ PushLeft  ; j-VBN   = refl
  j-VBP   : π₂ VBP   ≡ PushRight ; j-VBP   = refl
  j-NRN   : π₂ NRN   ≡ PushLeft  ; j-NRN   = refl
  j-NRP   : π₂ NRP   ≡ PushRight ; j-NRP   = refl
  j-CRN   : π₂ CRN   ≡ PushRight ; j-CRN   = refl
  j-CRP   : π₂ CRP   ≡ PushRight ; j-CRP   = refl
  j-GoalN : π₂ GoalN ≡ PushRight ; j-GoalN = refl
  j-Term  : π₂ Terminal ≡ PushRight ; j-Term  = refl
