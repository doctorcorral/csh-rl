{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Stochastic.CartPoleDemo
--
-- CartPole-inspired environment: 4D discretized state, verified via
-- abstraction.
--
-- State  = ℕ × ℕ × ℕ × ℕ  (pos, vel, angle, avel) — discretized bins
-- Action = Left | Right
--
-- Abstraction: angle half (left 0-7 vs right 8-15).  Reward depends
-- only on abstract state, so marginal-invariance holds by construction.
-- Policy: left half → prefer Left (push toward upright)
--         right half → prefer Right
--
-- This is the full 4D CartPole structure (position, velocity, angle,
-- angular velocity) with discretization.  The abstraction framework
-- verifies the policy on 2 abstract states, then lifts to the full
-- discretized space.
--
-- All --safe, no postulates.
------------------------------------------------------------------------

module CSHRL.Tasks.Stochastic.CartPoleDemo where

open import Data.Nat using (ℕ; zero; suc; _≤_; _≤?_)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import CSHRL.Probability.Finite using (Dist)
open import CSHRL.Probability.SD using (_SD[_]≤_; SD-refl)
open import CSHRL.Probability.FOSD using (_FOSD≤_; fosd?-sound)
open import CSHRL.Core.Compose using (VerifiedRanking)
open import CSHRL.Core.Abstraction using (StateAbstraction; abstract-lift)

------------------------------------------------------------------------
-- State: 4D discretized (pos, vel, angle, avel)
------------------------------------------------------------------------

State : Set
State = ℕ × ℕ × ℕ × ℕ

------------------------------------------------------------------------
-- Actions: push direction
------------------------------------------------------------------------

data Action : Set where
  Left  : Action
  Right : Action

------------------------------------------------------------------------
-- Abstraction: angle half (left 0-7 vs right 8-15)
--
-- The angle component (3rd of 4) determines the abstract class.
------------------------------------------------------------------------

is-left-half : ℕ → Bool
is-left-half angle with angle ≤? 7
... | yes _ = true
... | no  _ = false

project : State → Bool
project (pos , vel , angle , avel) = is-left-half angle

------------------------------------------------------------------------
-- Marginal rewards by half (same as SimplePendulumDemo)
--
-- Left half:  Left is better  (push toward upright)
-- Right half: Right is better
------------------------------------------------------------------------

marginal-by-half : Bool → Action → ℕ → Dist ℕ
marginal-by-half true  Left  _ = (2 , 1) ∷ (1 , 1) ∷ []
marginal-by-half true  Right _ = (0 , 1) ∷ (0 , 1) ∷ []
marginal-by-half false Left  _ = (0 , 1) ∷ (0 , 1) ∷ []
marginal-by-half false Right _ = (2 , 1) ∷ (1 , 1) ∷ []

marginal : State → Action → ℕ → Dist ℕ
marginal s = marginal-by-half (project s)

------------------------------------------------------------------------
-- State Abstraction: State → Bool
------------------------------------------------------------------------

cartpole-abstraction : StateAbstraction State Bool
cartpole-abstraction = record
  { project = project
  ; embed   = λ { true → (0 , 0 , 0 , 0) ; false → (0 , 0 , 8 , 0) }
  ; section = λ { true → refl ; false → refl }
  }

------------------------------------------------------------------------
-- Marginal invariance
--
-- Reward depends only on abstract state (angle half), so states in
-- the same class have identical marginals.
------------------------------------------------------------------------

marginal-invariant : ∀ s₁ s₂ → project s₁ ≡ project s₂ →
  ∀ a t → marginal s₁ a t ≡ marginal s₂ a t
marginal-invariant s₁ s₂ eq a t = cong (λ b → marginal-by-half b a t) eq

------------------------------------------------------------------------
-- Abstract ordering
------------------------------------------------------------------------

order : Bool → Action → Action → Set
order true  Left  Left  = ⊤
order true  Right Left  = ⊤
order true  Right Right = ⊤
order true  Left  Right = ⊥
order false Left  Left  = ⊤
order false Left  Right = ⊤
order false Right Right = ⊤
order false Right Left  = ⊥

------------------------------------------------------------------------
-- FOSD proofs
------------------------------------------------------------------------

private
  left-good  right-bad : Dist ℕ
  left-good  = (2 , 1) ∷ (1 , 1) ∷ []
  right-bad  = (0 , 1) ∷ (0 , 1) ∷ []

right≤left-left-half : right-bad FOSD≤ left-good
right≤left-left-half = fosd?-sound right-bad left-good refl

left≤right-right-half : right-bad FOSD≤ left-good
left≤right-right-half = fosd?-sound right-bad left-good refl

------------------------------------------------------------------------
-- Abstract Verified Ranking
------------------------------------------------------------------------

private
  abs-marginal : Bool → Action → ℕ → Dist ℕ
  abs-marginal b = marginal (StateAbstraction.embed cartpole-abstraction b)

abstract-ranking : VerifiedRanking Bool Action abs-marginal 0
abstract-ranking = record
  { _≤ₐ_ = order
  ; preserves = preserves-abs
  }
  where
    preserves-abs : ∀ a b s → order s a b →
      ∀ n → abs-marginal s a n SD[ 0 ]≤ abs-marginal s b n
    preserves-abs Left  Left  true  _ n = SD-refl 0 left-good
    preserves-abs Right Left  true  _ n = right≤left-left-half
    preserves-abs Right Right true  _ n = SD-refl 0 right-bad
    preserves-abs Left  Left  false _ n = SD-refl 0 right-bad
    preserves-abs Left  Right false _ n = left≤right-right-half
    preserves-abs Right Right false _ n = SD-refl 0 left-good
    preserves-abs Left  Right true  () n
    preserves-abs Right Left  false () n

------------------------------------------------------------------------
-- Lifted ranking on full 4D state space
------------------------------------------------------------------------

cartpole-ranking : VerifiedRanking State Action marginal 0
cartpole-ranking =
  abstract-lift cartpole-abstraction marginal-invariant abstract-ranking

------------------------------------------------------------------------
-- Spot checks: various (pos, vel, angle, avel) configurations
------------------------------------------------------------------------

open VerifiedRanking cartpole-ranking

check-left-angle-0   : _≤ₐ_ (0 , 0 , 0 , 0)  Right Left
check-left-angle-0   = tt

check-left-angle-7   : _≤ₐ_ (3 , 1 , 7 , 2)  Right Left
check-left-angle-7   = tt

check-right-angle-8  : _≤ₐ_ (1 , 0 , 8 , 0)  Left Right
check-right-angle-8  = tt

check-right-angle-15 : _≤ₐ_ (2 , 5 , 15 , 3) Left Right
check-right-angle-15 = tt
