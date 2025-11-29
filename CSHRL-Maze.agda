{-# OPTIONS --guardedness #-}

module CSHRL-Maze where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)
open import Relation.Nullary using (¬_)
open import Codata.Musical.Stream
open import Codata.Musical.Notation

-- 1. Domain Definitions
data State : Set where
  P0 : State
  P1 : State
  P2 : State

data Action : Set where
  Fwd : Action
  Bwd : Action

Reward : Set
Reward = ℕ

_≤ᵣ_ : Reward → Reward → Set
n ≤ᵣ m = n ≤ m

move : State → Action → State
move P0 Fwd = P1
move P0 Bwd = P0
move P1 Fwd = P2
move P1 Bwd = P0
move P2 Fwd = P2
move P2 Bwd = P1

reward-fn : State → Reward
reward-fn P2 = 1
reward-fn _  = 0

step : State → Action → State × Reward
step s a = (move s a , reward-fn (move s a))

-- 2. Import Core (No argmax needed)
open import CSHRL-Core State Action Reward step _≤ᵣ_

-- 3. Define the Homo

-- Manual ranking for pattern matching ease
my-rank : State → Action → Action → Bool
-- At P0: Fwd(P1) vs Bwd(P0). P1>P0. Fwd > Bwd.
my-rank P0 Fwd Fwd = true
my-rank P0 Fwd Bwd = false 
my-rank P0 Bwd Fwd = true 
my-rank P0 Bwd Bwd = true

-- At P1: Fwd(P2) vs Bwd(P0). P2>P0. Fwd > Bwd.
my-rank P1 Fwd Fwd = true
my-rank P1 Fwd Bwd = false
my-rank P1 Bwd Fwd = true
my-rank P1 Bwd Bwd = true

-- At P2: Fwd(P2) vs Bwd(P1). P2>P1. Fwd > Bwd.
my-rank P2 Fwd Fwd = true
my-rank P2 Fwd Bwd = false
my-rank P2 Bwd Fwd = true
my-rank P2 Bwd Bwd = true

-- Postulates for now to show structure
postulate
  strict-impl : ∀ a b s → a ≢ b → ¬ (value a s ≡ value b s)
  preserves-impl : ∀ a b s →
                  my-rank s a b ≡ true →
                  let (s₁ , r₁) = step s a
                      (s₂ , r₂) = step s b
                  in  r₁ ≤ᵣ r₂ × ∞ (value a s₁ ≤ₛ value b s₂)

instance
  MyHomo : CoindHomo
  MyHomo = record
    { _≤ₐ_ = my-rank
    ; strict = strict-impl
    ; preserves = preserves-impl
    }
