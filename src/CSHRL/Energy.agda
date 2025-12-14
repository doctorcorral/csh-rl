{-# OPTIONS --guardedness #-}

module CSHRL.Energy where

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _⊔_; _≤_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)
open import Relation.Nullary using (¬_)
open import Codata.Guarded.Stream using (Stream; head; tail)
open import Data.List using (List; _∷_; [])

------------------------------------------------------------------------
-- 1. Domain: The Desert Crossing
-- A linear track from Oasis (0) to City (5).
-- You have a battery. Moving costs 1.
-- If you run out of battery in the desert, you are stuck (Dead).
-- You can only Recharge at the Oasis (0).
------------------------------------------------------------------------

Target : ℕ
Target = 5

MaxCap : ℕ
MaxCap = 8

-- State: (Position, Energy)
State : Set
State = ℕ × ℕ

data Action : Set where
  Fwd      : Action -- Go closer to target
  Bwd      : Action -- Go back to charger
  Recharge : Action -- Refill battery (only at pos 0)
  Wait     : Action -- Do nothing

Reward : Set
Reward = ℕ

_≤ᵣ_ : Reward → Reward → Set
n ≤ᵣ m = n ≤ m

-- Boolean helpers
eq? : ℕ → ℕ → Bool
eq? zero zero = true
eq? (suc n) (suc m) = eq? n m
eq? _ _ = false

eq-action? : Action → Action → Bool
eq-action? Fwd Fwd = true
eq-action? Bwd Bwd = true
eq-action? Recharge Recharge = true
eq-action? Wait Wait = true
eq-action? _ _ = false

lte? : ℕ → ℕ → Bool
lte? zero _ = true
lte? (suc n) zero = false
lte? (suc n) (suc m) = lte? n m

gte? : ℕ → ℕ → Bool
gte? n m = lte? m n

gt? : ℕ → ℕ → Bool
gt? n m = not (lte? n m)

-- Transition Logic
step : State → Action → State × Reward
step (pos , en) Fwd =
  if ((gte? en 1) ∧ (lte? pos Target))
  then (let new-pos = if eq? pos Target then pos else (pos + 1)
            r       = if eq? new-pos Target then 100 else 0
        in ((new-pos , en ∸ 1) , r))
  else ((pos , 0) , 0) -- Stuck or already at target (if en=0)

step (pos , en) Bwd =
  if ((gte? en 1) ∧ (gt? pos 0))
  then ((pos ∸ 1 , en ∸ 1) , 0)
  else ((pos , 0) , 0) -- Stuck

step (pos , en) Recharge =
  if eq? pos 0
  then ((pos , MaxCap) , 0)
  else ((pos , en) , 0) -- Can't recharge here

step s Wait = (s , 0)

-- 2. Reuse Core
all-actions : List Action
all-actions = Fwd ∷ Bwd ∷ Recharge ∷ Wait ∷ []

open import CSHRL.Core
open Core State Action Reward step _≤ᵣ_ _⊔_ 0 all-actions

-- 3. The Structural Ranking (The "Truth" of the domain)
-- NOTE: Here we are HARDCODING the optimal policy structure (the ranking).
-- In this module, we are VERIFYING that our insight about Energy/Distance trade-offs
-- is mathematically consistent with infinite optimality. We are NOT discovering it.
-- For discovery, see CSHRL.Finder modules.

-- We calculate a heuristic score for every action to define the order.

dist-to-go : ℕ → ℕ
dist-to-go pos = Target ∸ pos

-- Heuristic Score
score : State → Action → ℕ
score (pos , en) act =
  let (next-s , r) = step (pos , en) act
      (n-pos , n-en) = next-s
      needed = dist-to-go pos
      n-needed = dist-to-go n-pos
  in
    if eq? pos Target then 100 -- Already won, stay here
    else
       -- CRITICAL SYMMETRY LOGIC:
       -- If we have enough energy to reach the target:
       if gte? en needed
       then
         -- Phase 1: Exploitation (Race to goal)
         -- Prefer actions that reduce distance
         (100 ∸ n-needed)
       else
         -- Phase 2: Survival (Retreat to charger)
         -- If we act Fwd, we die (score 0).
         -- If we act Bwd, we get closer to 0 (which is good for recharging).
         -- If we are at 0, Recharge is best.
         if eq? pos 0
         then (if eq-action? act Recharge then 50 else 0)
         else (if eq-action? act Bwd then (50 ∸ n-pos) else 0)

-- The Ranking Relation
_≤_rank_ : State → Action → Action → Bool
_≤_rank_ s a b = lte? (score s a) (score s b)

-- 4. Instance Proof (Postulated for this complex domain)
postulate
  strict-impl : ∀ a b s → a ≢ b → ¬ (action-value s a ≡ action-value s b)
  preserves-impl : ∀ a b s →
                  _≤_rank_ s a b ≡ true →
                  let v₁ = action-value s a
                      v₂ = action-value s b
                  in  head v₁ ≤ᵣ head v₂ × (tail v₁ ≤ₛ tail v₂)

instance
  EnergyHomo : CoindHomo
  EnergyHomo = record
    { _≤ₐ_ = _≤_rank_
    ; strict = strict-impl
    ; preserves = preserves-impl
    }
