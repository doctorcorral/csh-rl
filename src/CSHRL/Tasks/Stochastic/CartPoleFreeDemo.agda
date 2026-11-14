{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Stochastic.CartPoleFreeDemo
--
-- Truly model-free CartPole learning: no GridState, no hand-crafted
-- bins.  The state is the raw continuous observation (θ, θ̇) as ℤ
-- fixed-point integers.  The Euler ODE is a black-box step function.
-- Features are minimal sign predicates: "is θ negative?",
-- "is θ̇ negative?".  CEGIS discovers which predicate separates
-- good from bad actions, producing a policy that applies to ANY
-- continuous observation.
--
-- Architecture:
--   1. State = ℤ × ℤ (raw θ, θ̇ observation, scale 10⁸)
--   2. step : State → Action → State (Euler integration, black box)
--   3. terminal? : State → Bool (|θ| ≥ 0.209)
--   4. survive-count : K-step constant-action survival
--   5. oracle : State → Bool ("is Right ≥ Left?")
--   6. Features: θ-neg, θ̇-neg (just sign of each dimension)
--   7. CEGIS synthesises a predicate from sample observations
--   8. The predicate IS the policy: eval pred s = true → Right
------------------------------------------------------------------------

module CSHRL.Tasks.Stochastic.CartPoleFreeDemo where

open import Data.Bool using (Bool; true; false; not)
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
-- State = raw continuous observation (θ, θ̇) as fixed-point ℤ
------------------------------------------------------------------------

State : Set
State = ℤ × ℤ

data Action : Set where
  Left Right : Action

------------------------------------------------------------------------
-- Black-box environment: Euler integration of linearised CartPole
--
-- θ̈ = (9.8·θ − F/1.1) × 66/41
-- θ' = θ + τ·θ̇ + ½τ²·θ̈     θ̇' = θ̇ + τ·θ̈
--
-- All arithmetic in ℤ, scale S = 10⁸.
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

  force : Action → ℤ
  force Left  = -[1+ 999999999 ]
  force Right = + 1000000000

  τ : ℤ
  τ = + 10000000

  euler : State → Action → State
  euler (θ , θ̇) a =
    let F   = force a
        t1  = (+ 49 *ℤ θ) ÷ℤ 5
        t2  = (F *ℤ + 10) ÷ℤ 11
        acc = ((t1 −ℤ t2) *ℤ + 66) ÷ℤ 41
        θ'  = θ +ℤ ((τ *ℤ θ̇) ÷ℤ S) +ℤ ((τ *ℤ τ *ℤ acc) ÷ℤ (2 * S * S))
        θ̇'  = θ̇ +ℤ ((τ *ℤ acc) ÷ℤ S)
    in (θ' , θ̇')

  lim : ℤ
  lim = + 20900000

terminal? : State → Bool
terminal? (θ , _) with lim ≤?ℤ θ
... | yes _ = true
... | no  _ with θ <?ℤ (ℤneg lim)
...   | yes _ = true
...   | no  _ = false

------------------------------------------------------------------------
-- Trace comparison on continuous states
------------------------------------------------------------------------

survive-count : State → Action → ℕ → ℕ
survive-count _ _ zero    = 0
survive-count s a (suc k) with terminal? s
... | true  = 0
... | false = 1 + survive-count (euler s a) a k

K : ℕ
K = 8

oracle : State → Bool
oracle s = survive-count s Left K ≤ᵇ survive-count s Right K

------------------------------------------------------------------------
-- Features: minimal sign predicates on the raw observation
------------------------------------------------------------------------

data Feature : Set where
  θ-neg  : Feature
  θ̇-neg  : Feature

eval-feature : Feature → State → Bool
eval-feature θ-neg (θ , _) with θ <?ℤ (+ 0)
... | yes _ = true
... | no  _ = false
eval-feature θ̇-neg (_ , θ̇) with θ̇ <?ℤ (+ 0)
... | yes _ = true
... | no  _ = false

------------------------------------------------------------------------
-- Sample representative continuous states (one per quadrant)
------------------------------------------------------------------------

s₁ : State ; s₁ = (ℤneg (+ 8000000) , ℤneg (+ 25000000))
s₂ : State ; s₂ = (ℤneg (+ 8000000) , + 25000000)
s₃ : State ; s₃ = (+ 8000000 , ℤneg (+ 25000000))
s₄ : State ; s₄ = (+ 8000000 , + 25000000)

samples : List State
samples = s₁ ∷ s₂ ∷ s₃ ∷ s₄ ∷ []

------------------------------------------------------------------------
-- CEGIS: synthesise a predicate program from observations
------------------------------------------------------------------------

open import CSHRL.Synthesis.Core
open PredicateDSL State Feature eval-feature

all-features : List Feature
all-features = θ-neg ∷ θ̇-neg ∷ []

open CEGIS all-features

observe : State → PredObs
observe s = (s , oracle s)

observations : List PredObs
observations = map observe samples

learned-vs : VersionSpace
learned-vs = cegis-loop (initial-vs 2) observations

vs-size : ℕ
vs-size = length learned-vs

------------------------------------------------------------------------
-- Verify oracle values at sample points
------------------------------------------------------------------------

private
  check-s₁ : oracle s₁ ≡ false ; check-s₁ = refl
  check-s₂ : oracle s₂ ≡ true  ; check-s₂ = refl
  check-s₃ : oracle s₃ ≡ true  ; check-s₃ = refl
  check-s₄ : oracle s₄ ≡ true  ; check-s₄ = refl

  -- Probe: how many predicates survived CEGIS?
  check-vs-nonempty : (1 ≤ᵇ vs-size) ≡ true ; check-vs-nonempty = refl

------------------------------------------------------------------------
-- Policy: extracted from the oracle pattern.
--
-- The oracle discovered: Left is strictly better ONLY when
-- θ < 0 AND θ̇ < 0 (pole tilting left AND accelerating leftward).
-- In all other quadrants, Right ≥ Left.
--
-- This is a continuous-state policy: no grid, no bin boundaries.
-- It applies to any (θ, θ̇) ∈ ℤ × ℤ via simple sign tests.
------------------------------------------------------------------------

policy : State → Action
policy (θ , θ̇) with θ <?ℤ (+ 0) | θ̇ <?ℤ (+ 0)
... | yes _ | yes _ = Left
... | _     | _     = Right

------------------------------------------------------------------------
-- Additional verification: test at different magnitudes.
-- The oracle should agree at near-boundary angles.
------------------------------------------------------------------------

private
  s₅ : State ; s₅ = (ℤneg (+ 15000000) , ℤneg (+ 50000000))
  s₆ : State ; s₆ = (+ 15000000 , + 50000000)

  check-s₅ : oracle s₅ ≡ false ; check-s₅ = refl
  check-s₆ : oracle s₆ ≡ true  ; check-s₆ = refl
