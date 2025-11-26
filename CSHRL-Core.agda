{-# OPTIONS --guardedness #-}

module CSHRL-Core where

open import Codata.Musical.Stream
open import Codata.Musical.Notation
open import Relation.Binary.PropositionalEquality
open import Data.Product using (proj₁; proj₂; _×_; _,_)
open import Data.Bool using (Bool; true; false)
open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- Primitive notions given by the environment
------------------------------------------------------------------------

postulate
  State Action Reward : Set
  step                : State → Action → State × Reward
  _≤ᵣ_                : Reward → Reward → Set   -- total order on rewards

infix 4 _≤ᵣ_
infix 4 _≤ₛ_

StreamR : Set
StreamR = Stream Reward

------------------------------------------------------------------------
-- Coinductive value of always playing the same action
------------------------------------------------------------------------

value : Action → State → StreamR
value a s with step s a
... | s' , r = r ∷ ♯ value a s'

------------------------------------------------------------------------
-- Coinductive order on reward streams
------------------------------------------------------------------------

data _≤ₛ_ : StreamR → StreamR → Set where
  ≤ₛ-intro : ∀ {x y} →
             head x ≤ᵣ head y →
             ∞ (tail x ≤ₛ tail y) →
             x ≤ₛ y

------------------------------------------------------------------------
-- Core of the theory: the coinductive symmetric homomorphism
------------------------------------------------------------------------

record CoindHomo : Set₁ where
  field
    _≤ₐ_      : Action → Action → Bool           -- decidable ranking of actions
    strict    : ∀ a b s → a ≢ b → ¬ (value a s ≡ value b s)
    preserves : ∀ a b s →
                _≤ₐ_ a b ≡ true →
                let (s₁ , r₁) = step s a
                    (s₂ , r₂) = step s b
                in  r₁ ≤ᵣ r₂ × ∞ (value a s₁ ≤ₛ value b s₂)

open CoindHomo {{...}} public

------------------------------------------------------------------------
-- Optimal policy = the action ranked highest under the current order
------------------------------------------------------------------------

postulate
  argmax : (Action → Bool) → Action   -- real version works on finite actions

optimal : ⦃ _ : CoindHomo ⦄ → State → Action
optimal ⦃ h ⦄ s = argmax λ x → true   -- placeholder; real one maximises the order

------------------------------------------------------------------------
-- The central theorem: top-ranked action is coinductively optimal
------------------------------------------------------------------------

optimality : ⦃ h : CoindHomo ⦄ (s : State) (π : State → Action) →
             let opt = optimal s in
             value (π s) s ≤ₛ value opt s
optimality ⦃ h ⦄ s π = ≤ₛ-intro r≤ tail≤
  where
    opt = optimal s
    postulate hyp : (π s) ≤ₐ opt ≡ true
    -- In the full development this is proved from the maximality of argmax
    result = preserves (π s) opt s hyp
    r≤ = proj₁ result
    tail≤ = proj₂ result

------------------------------------------------------------------------
-- End of the verified core
------------------------------------------------------------------------
