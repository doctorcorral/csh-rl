{-# OPTIONS --guardedness #-}

module CSHRL-Finder-Test where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _<ᵇ_)
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
n ≤? m = n <ᵇ m Bool.∨ (n Data.Nat.== m)
  where open import Data.Nat using (_==_)
        open import Data.Bool using (_∨_)

-- 2. The Environment

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
open import CSHRL-Finder State Action Reward step _≤?_ GoA all-actions

-- 4. The Test Cases

-- Depth 1: Tie (both 0). Sort usually stable or implementation defined.
-- If stable sort and GoA comes first, GoA remains first? 
-- Our insert sort: if t2 <= t1 (0<=0) then (a1,t1)::(a2,t2).
-- So GoA stays before GoB.
test-ranking-1 : find-ranking Start 1 ≡ GoA ∷ GoB ∷ []
test-ranking-1 = refl 

-- Depth 2: GoB (0,1) > GoA (0,0).
-- The sorting logic should put GoB first.
test-ranking-2 : find-ranking Start 2 ≡ GoB ∷ GoA ∷ []
test-ranking-2 = refl

-- Deep Test
data DeepState : Set where
  S0 : DeepState; S1 : DeepState; S2 : DeepState; S3 : DeepState; S4 : DeepState

step-deep : DeepState → Action → DeepState × Reward
step-deep S0 GoA = (S1 , 0)
step-deep S0 GoB = (S2 , 0)
step-deep S1 _   = (S1 , 0)
step-deep S2 _   = (S3 , 0)
step-deep S3 _   = (S4 , 1)
step-deep S4 _   = (S4 , 1)

open CSHRL-Finder DeepState Action Reward step-deep _≤?_ GoA all-actions renaming (find-ranking to find-deep-rank)

-- Depth 3: GoB wins.
test-deep-rank : find-deep-rank S0 3 ≡ GoB ∷ GoA ∷ []
test-deep-rank = refl
