{-# OPTIONS --guardedness #-}

module CSHRL-Core 
  (State Action Reward : Set)
  (step                : State → Action → State × Reward)
  (_≤ᵣ_                : Reward → Reward → Set)
  where

open import Codata.Musical.Stream
open import Codata.Musical.Notation
open import Relation.Binary.PropositionalEquality
open import Data.Product using (proj₁; proj₂; _,_)
open import Data.Bool using (true; false)
open import Relation.Nullary using (¬_)

infix 4 _≤ᵣ_
infix 4 _≤ₛ_

StreamR : Set
StreamR = Stream Reward

------------------------------------------------------------------------
-- 1. Coinductive Value
-- The value of a policy is the stream of rewards it generates.
-- We define this for a constant action 'a' to simplify the core lemma.
------------------------------------------------------------------------

value : Action → State → StreamR
value a s with step s a
... | s' , r = r ∷ ♯ value a s'

------------------------------------------------------------------------
-- 2. Coinductive Order
-- A stream x is "better" than y if its head is better, and its tail is better.
------------------------------------------------------------------------

data _≤ₛ_ : StreamR → StreamR → Set where
  ≤ₛ-intro : ∀ {x y} →
             head x ≤ᵣ head y →
             ∞ (tail x ≤ₛ tail y) →
             x ≤ₛ y

------------------------------------------------------------------------
-- 3. The Symmetric Homomorphism
-- This is the heart of the theory. It defines what it means for a 
-- "Ranking of Actions" (_≤ₐ_) to be a valid symmetry of the world.
------------------------------------------------------------------------

record CoindHomo : Set₁ where
  field
    -- The Ranking: "Is action 'a' worse than or equal to 'b' in state 's'?"
    _≤ₐ_      : State → Action → Action → Bool
    
    -- Strictness: No two actions produce identical futures (Distinguishability)
    strict    : ∀ a b s → a ≢ b → ¬ (value a s ≡ value b s)
    
    -- Preservation (The Homomorphism Condition):
    -- If the ranking says 'a ≤ b', then the world MUST reflect this:
    -- 1. Immediate reward of a ≤ Immediate reward of b
    -- 2. Future stream of a ≤ Future stream of b
    preserves : ∀ a b s →
                _≤ₐ_ s a b ≡ true →
                let (s₁ , r₁) = step s a
                    (s₂ , r₂) = step s b
                in  r₁ ≤ᵣ r₂ × ∞ (value a s₁ ≤ₛ value b s₂)

open CoindHomo {{...}} public

------------------------------------------------------------------------
-- 4. The Optimality Theorem
-- We do not "search" for the optimum here. We prove a property about it.
-- Theorem: IF 'opt' is an action ranked higher than 'other',
-- THEN 'opt' yields a better reward stream than 'other'.
------------------------------------------------------------------------

optimality : ⦃ h : CoindHomo ⦄ (s : State) (other opt : Action) →
             (_ : _≤ₐ_ s other opt ≡ true) → -- Premise: Ranking holds
             value other s ≤ₛ value opt s
optimality ⦃ h ⦄ s other opt ranking-holds = ≤ₛ-intro r≤ tail≤
  where
    -- We use the 'preserves' field to extract the stream inequality
    result = preserves other opt s ranking-holds
    r≤     = proj₁ result
    tail≤  = proj₂ result
