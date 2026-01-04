{-# OPTIONS --guardedness #-}

-- | Key-Door-Treasure World
-- | Demonstrates hierarchical planning via symmetry flips.
-- | The agent must backtrack to get a key before proceeding to treasure.

module CSHRL.Tasks.Classic.KeyDoor where

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; T)
open import Data.Nat using (ℕ; zero; suc; _≤_; _+_; _∸_; _⊔_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)
open import Relation.Nullary using (¬_)
open import Codata.Guarded.Stream using (Stream; head; tail)
open import Data.List using (List; _∷_; [])

-- 1. Domain Definitions

-- Positions: 0=Start, 1=Key, 2=Hall, 3=Door, 4=Treasure
Position : Set
Position = ℕ

data Action : Set where
  GoLeft  : Action
  GoRight : Action
  PickUp  : Action
  Unlock  : Action

-- State: (Position, HasKey)
State : Set
State = Position × Bool

Reward : Set
Reward = ℕ

_≤ᵣ_ : Reward → Reward → Set
n ≤ᵣ m = n ≤ m

-- Helper for boolean comparison
_<?_ : ℕ → ℕ → Bool
zero  <? zero  = false
zero  <? suc _ = true
suc _ <? zero  = false
suc n <? suc m = n <? m

-- Helper for clamping positions 0..4
clamp : ℕ → ℕ
clamp n = if n <? 5 then n else 4

-- Transition Dynamics
next-pos : Position → Action → Bool → Position
next-pos 0 GoRight _ = 1
next-pos 1 GoRight _ = 2
next-pos 2 GoRight _ = 3
next-pos 3 GoRight _ = 3 -- Blocked by door!
next-pos 4 GoRight _ = 4 -- Stay at treasure
next-pos 0 GoLeft  _ = 0 -- Wall
next-pos p GoLeft  _ = p ∸ 1
next-pos 3 Unlock  true  = 4 -- Open door!
next-pos 3 Unlock  false = 3 -- Locked
next-pos p _       _ = p     -- Other actions stay put

next-key : Position → Action → Bool → Bool
next-key 0 PickUp _ = true -- Get key at pos 0
next-key _ _      k = k    -- Keep key status

transition : State → Action → State
transition (p , k) a = (next-pos p a k , next-key p a k)

reward-fn : State → Reward
reward-fn (4 , _) = 100 -- Treasure!
reward-fn _       = 0

step : State → Action → State × Reward
step s a = 
  let s' = transition s a 
  in (s' , reward-fn s')

all-actions : List Action
all-actions = GoLeft ∷ GoRight ∷ PickUp ∷ Unlock ∷ []

-- 2. Import Core with new parameters
open import CSHRL.Core
open Core State Action Reward step _≤ᵣ_ _⊔_ 0 all-actions

-- 3. Define the Structural Symmetry (The "Strategy")

dist-to : Position → Position → ℕ
dist-to current target = 
  if current <? target 
  then target ∸ current 
  else current ∸ target

rank-score : State → Action → ℕ
rank-score (p , hasKey) a = 
  let (p' , k') = transition (p , hasKey) a
  in heuristic p' k'
  where
    heuristic : Position → Bool → ℕ
    heuristic pos k = 
      if k 
      then (100 ∸ (dist-to pos 4)) -- Have Key: Close to 4 is best
      else (50 ∸ (dist-to pos 0))  -- No Key: Close to 0 is best

-- Boolean LEQ for ranking check
_<=?_ : ℕ → ℕ → Bool
zero  <=? _     = true
suc _ <=? zero  = false
suc n <=? suc m = n <=? m

-- Boolean version of ranking
_≤_rankᵇ_ : State → Action → Action → Bool
s ≤ a rankᵇ b = (rank-score s a) <=? (rank-score s b)

-- Lift to a proposition
_≤_rank_ : State → Action → Action → Set
s ≤ a rank b = T (s ≤ a rankᵇ b)

-- Postulate the proofs
postulate
  preserves-impl : ∀ a b s →
                  s ≤ a rank b →
                  action-value s a ≤ₛ action-value s b

instance
  KeyDoorHomo : CoindHomo
  KeyDoorHomo = record
    { _≤ₐ_ = _≤_rank_
    ; preserves = preserves-impl
    }

