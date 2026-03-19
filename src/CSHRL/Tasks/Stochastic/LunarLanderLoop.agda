{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Stochastic.LunarLanderLoop
--
-- Gridless CoindHomo search for Gymnasium LunarLander-v3.
--
-- Simplified 2D point-mass model (no Box2D):
--   State: (x, y, vx, vy, θ, ω)  —  6 continuous dimensions
--   Gravity, main engine thrust, side engine torque.
--
-- Constants calibrated from Gymnasium observation-space measurements.
--
-- Binary search: MainEngine vs Noop (the core vertical control).
-- Discovers "when to fire the main engine" — the primary landing skill.
------------------------------------------------------------------------

module CSHRL.Tasks.Stochastic.LunarLanderLoop where

open import Data.Bool using (Bool; true; false; not; _∧_)
open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _*_; _≤ᵇ_; _∸_)
open import Data.Nat.DivMod using () renaming (_/_ to _ℕ/_)
open import Data.Integer.Base as ℤ
  using (ℤ; +_; -[1+_]; ∣_∣)
  renaming (_+_ to _+ℤ_; _*_ to _*ℤ_; _-_ to _−ℤ_; -_ to ℤneg)
open import Data.Integer.Properties as ℤP
  using () renaming (_<?_ to _<?ℤ_; _≤?_ to _≤?ℤ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; map; length)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

open import CSHRL.Synthesis.ContinuousFeatures
open import CSHRL.Synthesis.CSHRLLoop

------------------------------------------------------------------------
-- State, Action
------------------------------------------------------------------------

-- (x, y, vx, vy, θ, ω) in fixed-point scale 10⁸
State : Set
State = ℤ × ℤ × ℤ × ℤ × ℤ × ℤ

data LLAction : Set where
  Noop MainEngine : LLAction

------------------------------------------------------------------------
-- Simplified dynamics
--
-- Measured from Gymnasium LunarLander-v3 (observation space):
--   gravity   ≈ 0.0267/step  (Δvy under Noop)
--   main_thrust ≈ 0.050/step  (Δvy from main engine, at θ≈0)
--   x_factor  ≈ 0.01         (Δx/vx per step)
--   y_factor  ≈ 0.02         (Δy/vy per step)
--   θ_factor  ≈ 0.05         (Δθ/ω per step)
--
-- Angle-dependent thrust ignored at depth 0 (small angle regime).
-- Side engines omitted (only Main vs Noop here).
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

  gravity : ℤ
  gravity = + 2667000

  main-thrust : ℤ
  main-thrust = + 5000000

  x-factor : ℤ
  x-factor = + 1000000

  y-factor : ℤ
  y-factor = + 2000000

  θ-factor : ℤ
  θ-factor = + 5000000

  ay-of : LLAction → ℤ
  ay-of Noop       = ℤneg gravity
  ay-of MainEngine = main-thrust −ℤ gravity

step : State → LLAction → State
step (x , y , vx , vy , θ , ω) a =
  let ay  = ay-of a
      vy' = vy +ℤ ay
      vx' = vx
      x'  = x +ℤ vx' f* x-factor
      y'  = y +ℤ vy' f* y-factor
      ω'  = ω
      θ'  = θ +ℤ ω' f* θ-factor
  in (x' , y' , vx' , vy' , θ' , ω')

------------------------------------------------------------------------
-- Terminal: reached ground (y ≤ 0) or off course (|x| > 1.0)
------------------------------------------------------------------------

private
  x-limit : ℤ
  x-limit = + 100000000

terminal? : State → Bool
terminal? (_ , y , _ , _ , _ , _) with y ≤?ℤ (+ 0)
... | yes _ = true
... | no  _ = false

------------------------------------------------------------------------
-- Feature instantiation (6 dimensions)
------------------------------------------------------------------------

private
  get-dim : State → ℕ → ℤ
  get-dim (x , _ , _ , _ , _ , _) zero                            = x
  get-dim (_ , y , _ , _ , _ , _) (suc zero)                      = y
  get-dim (_ , _ , vx , _ , _ , _) (suc (suc zero))               = vx
  get-dim (_ , _ , _ , vy , _ , _) (suc (suc (suc zero)))         = vy
  get-dim (_ , _ , _ , _ , θ , _) (suc (suc (suc (suc zero))))    = θ
  get-dim (_ , _ , _ , _ , _ , ω) (suc (suc (suc (suc (suc _))))) = ω

module LL = ContFeatures State 6 get-dim

------------------------------------------------------------------------
-- CSHRL loop: MainEngine vs Noop
--
-- p(s) = true → MainEngine, p(s) = false → Noop
-- "When should we fire the main engine?"
------------------------------------------------------------------------

open Loop State LL.CFeature LL.eval-cf
open LL.ActionChain LLAction

private
  pol-of : PredProg → State → LLAction
  pol-of p = eval-chain ((p , MainEngine) ∷ []) Noop

  s₀ : State
  s₀ = (+ 0 , + 140000000 , + 0 , + 0 , + 0 , + 0)

  H : ℕ
  H = 200

  K : ℕ
  K = 50

  goal-score : State → (State → LLAction) → ℕ → ℕ
  goal-score _ _ zero    = 0
  goal-score s π (suc k) with terminal? s
  ... | true  = suc k
  ... | false = goal-score (step s (π s)) π k

  goal-rollout : State → LLAction → (State → LLAction) → ℕ → ℕ
  goal-rollout _ _ _ zero    = 0
  goal-rollout s a π (suc k) with terminal? s
  ... | true  = suc k
  ... | false = let s' = step s a
                in goal-rollout s' (π s') π k

  collect : State → (State → LLAction) → ℕ → List State
  collect _ _ zero    = []
  collect s π (suc n) with terminal? s
  ... | true  = []
  ... | false = s ∷ collect (step s (π s)) π n

  score-ll : PredProg → ℕ
  score-ll p = goal-score s₀ (pol-of p) H

  oracle-ll : PredProg → State → Bool
  oracle-ll p s = goal-rollout s Noop (pol-of p) K
              ≤ᵇ goal-rollout s MainEngine (pol-of p) K

  traj-ll : PredProg → List State
  traj-ll p = collect s₀ (pol-of p) 20

  feats-ll : List State → List LL.CFeature
  feats-ll = LL.adaptive-features 0

open Iterate score-ll oracle-ll traj-ll feats-ll

------------------------------------------------------------------------
-- Run the search — depth 1 (conjunctions/disjunctions)
--
-- Depth 0 hits cegar-needed: no single axis threshold suffices.
-- Landing requires combining height and velocity, e.g.:
--   (vy < threshold) ∧ (y < threshold)
-- Depth 1 can express these 2D predicates.
------------------------------------------------------------------------

result : Result
result = run 1

rank★ : PredProg
rank★ = rank-of result

π★ : State → LLAction
π★ = pol-of rank★

------------------------------------------------------------------------
-- Diagnostics
------------------------------------------------------------------------

open LL using (axis)

convergence : result ≡ converged rank★
convergence = refl

-- Reveal the predicate (falsep as dummy; error shows actual)
rank-check : rank★ ≡ falsep
rank-check = refl
