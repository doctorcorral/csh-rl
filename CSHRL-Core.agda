{-# OPTIONS --guardedness -WnoUnknownNamesInFixityDecl #-}

module CSHRL-Core where

open import Data.List using (List; foldr) renaming (map to list-map)
open import Codata.Musical.Stream
open import Codata.Musical.Notation
open import Relation.Binary.PropositionalEquality
open import Data.Product using (proj₁; proj₂; _×_; _,_)
open import Data.Bool using (Bool; true; false)
open import Relation.Nullary using (¬_)
open import Function using (_∘_)

-- Inner module with parameters
module Core
  (State Action Reward : Set)
  (step                : State → Action → State × Reward)
  (_≤ᵣ_                : Reward → Reward → Set)
  -- Requirements for calculating optimal value
  (max                 : Reward → Reward → Reward)
  (bottom              : Reward)
  (all-actions         : List Action)
  where

  infix 4 _≤ᵣ_
  infix 4 _≤ₛ_

  StreamR : Set
  StreamR = Stream Reward

  ------------------------------------------------------------------------
  -- 1. Supremum of Streams
  -- Since we are constructive, we define "max" as a stream whose head
  -- is the max of heads, and whose tail is the supremum of tails.
  ------------------------------------------------------------------------

  max-list : List Reward → Reward
  max-list = foldr max bottom

  supremum : List StreamR → StreamR
  supremum xs = max-list (list-map head xs) ∷ ♯ supremum (list-map tail xs)

  ------------------------------------------------------------------------
  -- 2. Optimal Value and Action Value (Mutually Coinductive)
  ------------------------------------------------------------------------

  -- value s: The stream obtained by acting optimally from s forever.
  value : State → StreamR

  -- action-value s a: The stream obtained by doing 'a', then acting optimally.
  action-value : State → Action → StreamR

  {-# TERMINATING #-}
  value s = supremum (list-map (action-value s) all-actions)

  action-value s a = let (s' , r) = step s a in r ∷ ♯ value s'

  ------------------------------------------------------------------------
  -- 3. Coinductive Order
  ------------------------------------------------------------------------

  data _≤ₛ_ : StreamR → StreamR → Set where
    ≤ₛ-intro : ∀ {x y} →
               head x ≤ᵣ head y →
               ∞ (tail x ≤ₛ tail y) →
               x ≤ₛ y

  ------------------------------------------------------------------------
  -- 4. The Symmetric Homomorphism
  -- Updated to refer to the optimal action-value instead of inertial value.
  ------------------------------------------------------------------------

  record CoindHomo : Set₁ where
    field
      _≤ₐ_      : State → Action → Action → Bool
      
      -- Strictness: No two actions produce identical optimal futures
      strict    : ∀ a b s → a ≢ b → ¬ (action-value s a ≡ action-value s b)
      
      -- Preservation: The ranking mirrors the relation between action-values
      preserves : ∀ a b s →
                  _≤ₐ_ s a b ≡ true →
                  let v₁ = action-value s a
                      v₂ = action-value s b
                  in  head v₁ ≤ᵣ head v₂ × ∞ (tail v₁ ≤ₛ tail v₂)

  open CoindHomo {{...}} public

  ------------------------------------------------------------------------
  -- 5. The Optimality Theorem
  ------------------------------------------------------------------------

  optimality : ⦃ h : CoindHomo ⦄ (s : State) (other opt : Action) →
               (_ : _≤ₐ_ s other opt ≡ true) →
               action-value s other ≤ₛ action-value s opt
  optimality ⦃ h ⦄ s other opt ranking-holds = ≤ₛ-intro r≤ tail≤
    where
      result = preserves other opt s ranking-holds
      r≤     = proj₁ result
      tail≤  = proj₂ result
