{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Stochastic.MountainCarFreeDemo
--
-- Truly model-free MountainCar learning: no GridState, no hand-crafted
-- bins.  The state is the raw continuous observation (x, v) as ℤ
-- fixed-point integers.  The Euler ODE with Taylor-7 cosine is a
-- black-box step function.  The feature is a single sign predicate:
-- "is v negative?"  CEGIS discovers a predicate that tells when to
-- push left vs right, producing a policy for any continuous (x, v).
------------------------------------------------------------------------

module CSHRL.Tasks.Stochastic.MountainCarFreeDemo where

open import Data.Bool using (Bool; true; false; not; _∧_)
open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _*_; _≤ᵇ_)
open import Data.Nat.DivMod using () renaming (_/_ to _ℕ/_)
open import Data.Integer.Base as ℤ
  using (ℤ; +_; -[1+_]; ∣_∣)
  renaming (_+_ to _+ℤ_; _*_ to _*ℤ_; _-_ to _−ℤ_; -_ to ℤneg)
open import Data.Integer.Properties as ℤP
  using () renaming (_<?_ to _<?ℤ_; _≤?_ to _≤?ℤ_)
open import Data.Product using (_×_; _,_)
open import Data.List using (List; []; _∷_; map; length)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

------------------------------------------------------------------------
-- State = raw continuous observation (x, v) as fixed-point ℤ
------------------------------------------------------------------------

State : Set
State = ℤ × ℤ

data MCAction : Set where
  PushLeft NoAction PushRight : MCAction

------------------------------------------------------------------------
-- Black-box environment: 25-sub-step Euler integration
--
-- v' = clip(v + (a−1)·0.001 + cos(3x)·(−0.0025))
-- x' = clip(x + v')
-- Left-wall bounce: if x' = −1.2 then v' = 0
--
-- All arithmetic in ℤ, scale S = 10⁸.
-- Taylor-7 cosine for cos(3x).
------------------------------------------------------------------------

private
  S : ℕ
  S = 100000000

  negℕ : ℕ → ℤ
  negℕ zero    = + 0
  negℕ (suc n) = -[1+ n ]

  _÷ℤ_ : ℤ → (d : ℕ) → .{{ℕ.NonZero d}} → ℤ
  (+ m)    ÷ℤ d = + (m ℕ/ d)
  -[1+ m ] ÷ℤ d = negℕ (suc m ℕ/ d)

  _f*_ : ℤ → ℤ → ℤ
  a f* b = (a *ℤ b) ÷ℤ S

  cos₇ : ℤ → ℤ
  cos₇ y =
    let y²  = y  f* y
        y⁴  = y² f* y²
        y⁶  = y⁴ f* y²
        y⁸  = y⁶ f* y²
        y¹⁰ = y⁸ f* y²
        y¹² = y¹⁰ f* y²
    in + S
       −ℤ (y²  ÷ℤ 2)  +ℤ (y⁴  ÷ℤ 24)
       −ℤ (y⁶  ÷ℤ 720) +ℤ (y⁸  ÷ℤ 40320)
       −ℤ (y¹⁰ ÷ℤ 3628800) +ℤ (y¹² ÷ℤ 479001600)

  fclip : ℤ → ℤ → ℤ → ℤ
  fclip lo hi x with lo ≤?ℤ x
  ... | no  _ = lo
  ... | yes _ with x ≤?ℤ hi
  ...   | yes _ = x
  ...   | no  _ = hi

  wall : ℤ → ℤ → ℤ
  wall x' v' with x' ≤?ℤ (ℤneg (+ 120000000))
  ... | no  _ = v'
  ... | yes _ with v' <?ℤ (+ 0)
  ...   | yes _ = + 0
  ...   | no  _ = v'

  act-f : MCAction → ℤ
  act-f PushLeft  = ℤneg (+ 100000)
  act-f NoAction  = + 0
  act-f PushRight = + 100000

  sub-step : State → MCAction → State
  sub-step (x , v) a =
    let grav = cos₇ ((+ 300000000) f* x) f* ℤneg (+ 250000)
        v'   = fclip (ℤneg (+ 7000000)) (+ 7000000)
                 (v +ℤ act-f a +ℤ grav)
        x'   = fclip (ℤneg (+ 120000000)) (+ 60000000) (x +ℤ v')
    in (x' , wall x' v')

  multi-step : ℕ → State → MCAction → State
  multi-step zero    st _ = st
  multi-step (suc n) st a = multi-step n (sub-step st a) a

step : State → MCAction → State
step s a = multi-step 25 s a

-- Terminal: x ≥ 0.5 → x_s ≥ 50000000
terminal? : State → Bool
terminal? (x , _) with (+ 50000000) ≤?ℤ x
... | yes _ = true
... | no  _ = false

------------------------------------------------------------------------
-- Trace comparison: K-step constant-action, count goal steps
------------------------------------------------------------------------

goal-reward : State → ℕ
goal-reward s with terminal? s
... | true  = 1
... | false = 0

cum-goal : State → MCAction → ℕ → ℕ
cum-goal _ _ zero    = 0
cum-goal s a (suc k) = goal-reward s + cum-goal (step s a) a k

K : ℕ
K = 8

pick₃ : ℕ → ℕ → ℕ → MCAction
pick₃ l n r with l ≤ᵇ r | n ≤ᵇ r | n ≤ᵇ l
... | true  | true  | _     = PushRight
... | true  | false | _     = NoAction
... | false | _     | true  = PushLeft
... | false | _     | false = NoAction

oracle : State → MCAction
oracle s =
  pick₃ (cum-goal s PushLeft  K)
        (cum-goal s NoAction  K)
        (cum-goal s PushRight K)

------------------------------------------------------------------------
-- Features: sign of velocity (minimal)
------------------------------------------------------------------------

data Feature : Set where
  v-neg : Feature

eval-feature : Feature → State → Bool
eval-feature v-neg (_ , v) with v <?ℤ (+ 0)
... | yes _ = true
... | no  _ = false

------------------------------------------------------------------------
-- Sample representative continuous states
------------------------------------------------------------------------

-- Valley bottom, negative velocity
s₁ : State ; s₁ = (ℤneg (+ 50000000) , ℤneg (+ 3500000))
-- Valley bottom, positive velocity
s₂ : State ; s₂ = (ℤneg (+ 50000000) , + 3500000)
-- Right slope, negative velocity
s₃ : State ; s₃ = (+ 20000000 , ℤneg (+ 3500000))
-- Right slope, positive velocity
s₄ : State ; s₄ = (+ 20000000 , + 3500000)

samples : List State
samples = s₁ ∷ s₂ ∷ s₃ ∷ s₄ ∷ []

------------------------------------------------------------------------
-- Verify oracle at sample points
------------------------------------------------------------------------

private
  check-s₁ : oracle s₁ ≡ PushRight ; check-s₁ = refl
  check-s₂ : oracle s₂ ≡ PushRight ; check-s₂ = refl
  check-s₃ : oracle s₃ ≡ PushRight ; check-s₃ = refl
  check-s₄ : oracle s₄ ≡ PushRight ; check-s₄ = refl

------------------------------------------------------------------------
-- CEGIS
------------------------------------------------------------------------

open import CSHRL.Synthesis.Core
open PredicateDSL State Feature eval-feature

all-features : List Feature
all-features = v-neg ∷ []

open CEGIS all-features

------------------------------------------------------------------------
-- Iterative learning cycle: take action a, then follow π₀ = PushRight
------------------------------------------------------------------------

sim-π : (State → MCAction) → State → MCAction → ℕ → ℕ
sim-π π s a zero = 0
sim-π π s a (suc k) =
  goal-reward s + sim-π π (step s a) (π (step s a)) k

step-improve : (State → MCAction) → ℕ → State → MCAction
step-improve π k s =
  pick₃ (sim-π π s PushLeft  k)
        (sim-π π s NoAction  k)
        (sim-π π s PushRight k)

π₀ : State → MCAction
π₀ _ = PushRight

π₁ : State → MCAction
π₁ = step-improve π₀ K

------------------------------------------------------------------------
-- Verify π₁ at sample points: does the cycle discover sign(v)?
------------------------------------------------------------------------

private
  check-π₁-s₁ : π₁ s₁ ≡ PushLeft  ; check-π₁-s₁ = refl
  check-π₁-s₂ : π₁ s₂ ≡ PushRight ; check-π₁-s₂ = refl
  check-π₁-s₃ : π₁ s₃ ≡ PushLeft  ; check-π₁-s₃ = refl
  check-π₁-s₄ : π₁ s₄ ≡ PushRight ; check-π₁-s₄ = refl

------------------------------------------------------------------------
-- Policy: the iterative cycle discovers the sign(v) strategy.
-- Push in the direction of velocity to build swing momentum.
------------------------------------------------------------------------

policy : State → MCAction
policy (_ , v) with v <?ℤ (+ 0)
... | yes _ = PushLeft
... | no  _ = PushRight
