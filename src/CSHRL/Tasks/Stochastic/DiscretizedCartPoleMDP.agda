{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Stochastic.DiscretizedCartPoleMDP
--
-- Finite CartPole MDP with step dynamics for real learning.
--
-- State  = 16 angle bins (a0..a15). Left half (a0-a7), right half (a8-a15).
-- Terminal at a0 (fallen left) and a15 (fallen right).
-- Action = Left | Right
--
-- Dynamics: Left decreases angle (push cart left), Right increases.
-- Reward: 1 per step until terminal, 0 at terminal.
--
-- Integrates with StochasticFiniteMDP EC and Learning for the full
-- train-step / train-batch / FOSD synthesis pipeline.
------------------------------------------------------------------------

module CSHRL.Tasks.Stochastic.DiscretizedCartPoleMDP where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; _≤?_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)

open import CSHRL.Probability.Finite using (Dist; pure)

------------------------------------------------------------------------
-- State: 16 angle bins
------------------------------------------------------------------------

data State : Set where
  s0  : State
  s1  : State
  s2  : State
  s3  : State
  s4  : State
  s5  : State
  s6  : State
  s7  : State
  s8  : State
  s9  : State
  s10 : State
  s11 : State
  s12 : State
  s13 : State
  s14 : State
  s15 : State

------------------------------------------------------------------------
-- Actions
------------------------------------------------------------------------

data Action : Set where
  Left  : Action
  Right : Action

------------------------------------------------------------------------
-- Reward
------------------------------------------------------------------------

Reward : Set
Reward = ℕ

------------------------------------------------------------------------
-- Dynamics: pred/suc with clamping at terminals
------------------------------------------------------------------------

pred-angle : State → State
pred-angle s0  = s0
pred-angle s1  = s0
pred-angle s2  = s1
pred-angle s3  = s2
pred-angle s4  = s3
pred-angle s5  = s4
pred-angle s6  = s5
pred-angle s7  = s6
pred-angle s8  = s7
pred-angle s9  = s8
pred-angle s10 = s9
pred-angle s11 = s10
pred-angle s12 = s11
pred-angle s13 = s12
pred-angle s14 = s13
pred-angle s15 = s14

suc-angle : State → State
suc-angle s0  = s1
suc-angle s1  = s2
suc-angle s2  = s3
suc-angle s3  = s4
suc-angle s4  = s5
suc-angle s5  = s6
suc-angle s6  = s7
suc-angle s7  = s8
suc-angle s8  = s9
suc-angle s9  = s10
suc-angle s10 = s11
suc-angle s11 = s12
suc-angle s12 = s13
suc-angle s13 = s14
suc-angle s14 = s15
suc-angle s15 = s15

is-terminal : State → Bool
is-terminal s0  = true
is-terminal s15 = true
is-terminal _   = false

------------------------------------------------------------------------
-- Step function
------------------------------------------------------------------------

step : State → Action → Dist (State × Reward)
step s a with a
... | Left  = pure (pred-angle s , (if is-terminal (pred-angle s) then 0 else 1))
... | Right = pure (suc-angle s , (if is-terminal (suc-angle s) then 0 else 1))

------------------------------------------------------------------------
-- Reward structure
------------------------------------------------------------------------

_≤ᵣ_ : Reward → Reward → Set
_≤ᵣ_ = _≤_

≤ᵣ-dec : (r s : Reward) → Dec (r ≤ᵣ s)
≤ᵣ-dec = _≤?_

≤ᵣ-refl : ∀ {r} → r ≤ᵣ r
≤ᵣ-refl = ≤-refl

_+ᵣ_ : Reward → Reward → Reward
_+ᵣ_ = _+_

_*ᵣ_ : ℕ → Reward → Reward
_*ᵣ_ = _*_

zeroᵣ : Reward
zeroᵣ = 0

max : Reward → Reward → Reward
max m n with m ≤? n
... | yes _ = n
... | no  _ = m

bottom : Reward
bottom = 0

------------------------------------------------------------------------
-- Finiteness
------------------------------------------------------------------------

all-actions : List Action
all-actions = Left ∷ Right ∷ []

default-action : Action
default-action = Left

horizon : ℕ
horizon = 16

------------------------------------------------------------------------
-- Import EC
------------------------------------------------------------------------

open import CSHRL.EnvironmentClass.StochasticFiniteMDP

open StochasticFiniteMDP
  State Action Reward step
  _≤ᵣ_ ≤ᵣ-dec ≤ᵣ-refl max bottom
  _+ᵣ_ _*ᵣ_ zeroᵣ
  all-actions default-action horizon

------------------------------------------------------------------------
-- Policy check: Finder's optimal policy (verified by refl)
------------------------------------------------------------------------

test-left-half : find-policy s3 horizon ≡ Left
test-left-half = refl

test-right-half : find-policy s12 horizon ≡ Left
test-right-half = refl
