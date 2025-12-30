{-# OPTIONS --guardedness #-}

-- | The Delayed Gratification Task (a.k.a. "The Marshmallow Test")
-- | Tests the Finder algorithm on sparse rewards where the optimal
-- | action is only distinguishable by looking deeper into the future.

module CSHRL.Tasks.Classic.DelayedGratification where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _≤ᵇ_)
open import Data.List using (List; _∷_; [])
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- 1. Domain Definitions

data State : Set where
  Start : State
  PathA : State
  PathB : State
  End   : State

data Action : Set where
  GoA  : Action
  GoB  : Action
  Wait : Action

Reward : Set
Reward = ℕ

_≤?_ : Reward → Reward → Bool
_≤?_ = _≤ᵇ_

-- 2. The Environment
--    Path A: Instant flatness (0 forever)
--    Path B: Hidden gem (0 now, 1 later)

step : State → Action → State × Reward
step Start GoA = (PathA , 0)
step Start GoB = (PathB , 0)
step PathA _   = (PathA , 0) 
step PathB _   = (End , 1)   
step End   _   = (End , 1)   
step _     _   = (End , 0)   

all-actions : List Action
all-actions = GoA ∷ GoB ∷ [] 

-- 3. Import the Finder
import CSHRL.Finder
open CSHRL.Finder.Finder State Action Reward step _≤?_ GoA all-actions

-- 4. The Test Cases

-- Depth 1: Tie (both 0). Our insertion sort is not stable.
-- When traces are equal (t2 ≤ₜ t1 holds), the new element is placed first.
-- Processing order: GoA inserted into [], then GoB inserted.
-- GoB gets placed before GoA since traces are equal.
test-ranking-1 : find-ranking Start 1 ≡ GoB ∷ GoA ∷ []
test-ranking-1 = refl 

-- Depth 2: GoB (0,1) > GoA (0,0).
-- The sorting logic should put GoB first.
test-ranking-2 : find-ranking Start 2 ≡ GoB ∷ GoA ∷ []
test-ranking-2 = refl

-- Deep Test: Rewards delayed by 3 steps
data DeepState : Set where
  S0 : DeepState; S1 : DeepState; S2 : DeepState; S3 : DeepState; S4 : DeepState

step-deep : DeepState → Action → DeepState × Reward
step-deep S0 GoA  = (S1 , 0)
step-deep S0 GoB  = (S2 , 0)
step-deep S0 Wait = (S0 , 0)
step-deep S1 _    = (S1 , 0)
step-deep S2 _    = (S3 , 0)
step-deep S3 _    = (S4 , 1)
step-deep S4 _    = (S4 , 1)

open CSHRL.Finder.Finder DeepState Action Reward step-deep _≤?_ GoA all-actions renaming (find-ranking to find-deep-rank)

-- Depth 3: GoB wins.
test-deep-rank : find-deep-rank S0 3 ≡ GoB ∷ GoA ∷ []
test-deep-rank = refl

