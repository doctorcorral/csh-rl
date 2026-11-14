{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Stochastic.RealCartPoleDemo
--
-- CartPole with rational state space: the "real" continuous structure.
--
-- State  = ℚ × ℚ × ℚ × ℚ  (pos, vel, angle, avel) — rationals
-- Action = Left | Right
--
-- Abstraction: angle sign (θ < 0 vs θ ≥ 0).  Reward depends only on
-- abstract state, so marginal-invariance holds by construction.
-- Policy: θ < 0 → prefer Left; θ ≥ 0 → prefer Right.
--
-- This uses Data.Rational for the state representation — the same
-- structure as the continuous CartPole (4D vector) but with exact
-- rational arithmetic.  No discretization of the state type.
--
-- All --safe, no postulates.
------------------------------------------------------------------------

module CSHRL.Tasks.Stochastic.RealCartPoleDemo where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 0ℚ; ½; -½; _/_; -_)
open import Data.Rational.Properties using (_<?_)

-- ¼ = 1/4, -¼ = -1/4 for spot checks
¼ : ℚ
¼ = + 1 / 4

-¼ : ℚ
-¼ = - ¼

open import CSHRL.Probability.Finite using (Dist)
open import CSHRL.Probability.SD using (_SD[_]≤_; SD-refl)
open import CSHRL.Probability.FOSD using (_FOSD≤_; fosd?-sound)
open import CSHRL.Core.Compose using (VerifiedRanking)
open import CSHRL.Core.Abstraction using (StateAbstraction; abstract-lift)

------------------------------------------------------------------------
-- State: 4D rational (pos, vel, angle, avel)
------------------------------------------------------------------------

State : Set
State = ℚ × ℚ × ℚ × ℚ

------------------------------------------------------------------------
-- Actions
------------------------------------------------------------------------

data Action : Set where
  Left  : Action
  Right : Action

------------------------------------------------------------------------
-- Abstraction: angle sign (θ < 0 = left half, θ ≥ 0 = right half)
------------------------------------------------------------------------

is-left-half : ℚ → Bool
is-left-half θ with θ <? 0ℚ
... | yes _ = true
... | no  _ = false

project : State → Bool
project (x , ẋ , θ , θ̇) = is-left-half θ

------------------------------------------------------------------------
-- Marginal rewards by half (same as CartPoleDemo)
------------------------------------------------------------------------

marginal-by-half : Bool → Action → ℕ → Dist ℕ
marginal-by-half true  Left  _ = (2 , 1) ∷ (1 , 1) ∷ []
marginal-by-half true  Right _ = (0 , 1) ∷ (0 , 1) ∷ []
marginal-by-half false Left  _ = (0 , 1) ∷ (0 , 1) ∷ []
marginal-by-half false Right _ = (2 , 1) ∷ (1 , 1) ∷ []

marginal : State → Action → ℕ → Dist ℕ
marginal s = marginal-by-half (project s)

------------------------------------------------------------------------
-- State Abstraction
------------------------------------------------------------------------

real-cartpole-abstraction : StateAbstraction State Bool
real-cartpole-abstraction = record
  { project = project
  ; embed   = λ { true → (0ℚ , 0ℚ , -½ , 0ℚ) ; false → (0ℚ , 0ℚ , ½ , 0ℚ) }
  ; section = λ { true → refl ; false → refl }
  }

------------------------------------------------------------------------
-- Marginal invariance
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
  abs-marginal b = marginal (StateAbstraction.embed real-cartpole-abstraction b)

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
-- Lifted ranking on ℚ⁴
------------------------------------------------------------------------

real-cartpole-ranking : VerifiedRanking State Action marginal 0
real-cartpole-ranking =
  abstract-lift real-cartpole-abstraction marginal-invariant abstract-ranking

------------------------------------------------------------------------
-- Spot checks: rational states
------------------------------------------------------------------------

open VerifiedRanking real-cartpole-ranking

check-left-neg  : _≤ₐ_ (0ℚ , 0ℚ , -½ , 0ℚ) Right Left
check-left-neg  = tt

check-left-small : _≤ₐ_ (½ , -½ , -¼ , ½) Right Left
check-left-small = tt

check-right-pos : _≤ₐ_ (0ℚ , 0ℚ , ½ , 0ℚ) Left Right
check-right-pos = tt

check-right-small : _≤ₐ_ (-½ , ½ , ¼ , -½) Left Right
check-right-small = tt
