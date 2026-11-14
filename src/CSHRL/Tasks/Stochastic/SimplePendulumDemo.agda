{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Stochastic.SimplePendulumDemo
--
-- Discrete pendulum: 16 angle bins, 2 actions (push left/right).
--
-- State  = ℕ  (angle bin 0..15, with 0 and 8 = upright)
-- Action = Left | Right
--
-- Abstraction: left half (0-7) vs right half (8-15).
-- Policy: left half → prefer Left (push toward upright at 0)
--         right half → prefer Right (push toward upright at 8)
--
-- A step toward CartPole: pendulum-like structure (angle, push direction)
-- but fully discrete.  Marginal-invariance holds because reward depends
-- only on which half the angle falls into.
--
-- All --safe, no postulates.
------------------------------------------------------------------------

module CSHRL.Tasks.Stochastic.SimplePendulumDemo where

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
-- Actions: push direction
------------------------------------------------------------------------

data Action : Set where
  Left  : Action
  Right : Action

------------------------------------------------------------------------
-- Abstraction: left half (0-7) vs right half (8-15)
--
-- is-left n = true  iff n ≤ 7
------------------------------------------------------------------------

is-left : ℕ → Bool
is-left n with n ≤? 7
... | yes _ = true
... | no  _ = false

------------------------------------------------------------------------
-- Marginal rewards by half
--
-- Left half:  Left is better  (push toward upright at 0)
-- Right half: Right is better (push toward upright at 8)
------------------------------------------------------------------------

marginal-by-half : Bool → Action → ℕ → Dist ℕ
marginal-by-half true  Left  _ = (2 , 1) ∷ (1 , 1) ∷ []
marginal-by-half true  Right _ = (0 , 1) ∷ (0 , 1) ∷ []
marginal-by-half false Left  _ = (0 , 1) ∷ (0 , 1) ∷ []
marginal-by-half false Right _ = (2 , 1) ∷ (1 , 1) ∷ []

marginal : ℕ → Action → ℕ → Dist ℕ
marginal n = marginal-by-half (is-left n)

------------------------------------------------------------------------
-- State Abstraction: ℕ → Bool
------------------------------------------------------------------------

pendulum-abstraction : StateAbstraction ℕ Bool
pendulum-abstraction = record
  { project = is-left
  ; embed   = λ { true → 0 ; false → 8 }
  ; section = λ { true → refl ; false → refl }
  }

------------------------------------------------------------------------
-- Marginal invariance
------------------------------------------------------------------------

marginal-invariant : ∀ n₁ n₂ → is-left n₁ ≡ is-left n₂ →
  ∀ a t → marginal n₁ a t ≡ marginal n₂ a t
marginal-invariant n₁ n₂ eq a t = cong (λ b → marginal-by-half b a t) eq

------------------------------------------------------------------------
-- Abstract ordering
--
-- Left half (true):  Right ≤ Left  (prefer Left)
-- Right half (false): Left ≤ Right (prefer Right)
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
  abs-marginal b = marginal (StateAbstraction.embed pendulum-abstraction b)

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
-- Lifted ranking on ℕ (all 16 angle bins)
------------------------------------------------------------------------

pendulum-ranking : VerifiedRanking ℕ Action marginal 0
pendulum-ranking =
  abstract-lift pendulum-abstraction marginal-invariant abstract-ranking

------------------------------------------------------------------------
-- Spot checks
------------------------------------------------------------------------

open VerifiedRanking pendulum-ranking

check-left-0  : _≤ₐ_ 0  Right Left
check-left-0  = tt

check-left-5  : _≤ₐ_ 5  Right Left
check-left-5  = tt

check-right-8 : _≤ₐ_ 8  Left Right
check-right-8 = tt

check-right-15 : _≤ₐ_ 15 Left Right
check-right-15 = tt
