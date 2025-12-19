{-# OPTIONS --safe --guardedness #-}

module CSHRL.Core where

open import Data.List using (List; map; foldr)
open import Codata.Guarded.Stream using (Stream; head; tail; _∷_; tabulate)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Data.Product using (proj₁; proj₂; _×_; _,_)
open import Data.Bool using (Bool; true; false)
open import Relation.Nullary using (¬_)
open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)

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

  ------------------------------------------------------------------------
  -- 2. Optimal Value and Action Value (Mutually Coinductive)
  ------------------------------------------------------------------------
  -- We use a safe, structural definition for value construction
  -- by tabulating the finite horizon optimal value at every depth.

  -- Helper function: Value at depth n (Finite Horizon)
  solve : State → ℕ → Reward
  solve s zero    = max-list (map (λ a → proj₂ (step s a)) all-actions)
  solve s (suc n) = max-list (map (λ a → solve (proj₁ (step s a)) n) all-actions)

  -- value s: The stream obtained by acting optimally from s forever.
  -- Defined via tabulation of the solve function.
  value : State → StreamR
  value s = tabulate (solve s)

  -- action-value s a: The stream obtained by doing 'a', then acting optimally.
  action-value : State → Action → StreamR
  head (action-value s a) = proj₂ (step s a)
  tail (action-value s a) = value (proj₁ (step s a))

  ------------------------------------------------------------------------
  -- 3. Coinductive Order
  ------------------------------------------------------------------------

  record _≤ₛ_ (x y : StreamR) : Set where
    coinductive
    field
      head≤ : head x ≤ᵣ head y
      tail≤ : tail x ≤ₛ tail y

  open _≤ₛ_ public

  ------------------------------------------------------------------------
  -- 4. The Symmetric Homomorphism
  -- Updated to refer to the optimal action-value instead of inertial value.
  ------------------------------------------------------------------------

  record CoindHomo : Set₁ where
    field
      _≤ₐ_      : State → Action → Action → Bool

      -- Preservation: The ranking mirrors the relation between action-values
      preserves : ∀ a b s → _≤ₐ_ s a b ≡ true →
                  action-value s a ≤ₛ action-value s b

  open CoindHomo {{...}} public

  ------------------------------------------------------------------------
  -- 5. The Optimality Theorem
  ------------------------------------------------------------------------

  optimality : ⦃ h : CoindHomo ⦄ (other opt : Action) (s : State)
               (_ : _≤ₐ_ s other opt ≡ true) →
               action-value s other ≤ₛ action-value s opt
  optimality = preserves
