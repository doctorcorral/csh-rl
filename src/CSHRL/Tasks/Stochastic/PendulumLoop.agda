{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Stochastic.PendulumLoop
--
-- Gridless CoindHomo search for the Pendulum swing-up task.
--
-- 2 dimensions: θ (angle), ω (angular velocity)
-- 2 actions: TorqueNeg (-2), TorquePos (+2)
--
-- Gymnasium Pendulum-v1 dynamics:
--   θ̈ = -3g/(2l) sin(θ + π) + 3/(ml²) u
--     = 15 sin(θ) + 3u         (with g=10, m=1, l=1)
--   ω' = clip(ω + θ̈·dt, -8, 8)
--   θ' = θ + ω'·dt
--
-- Start: θ = π (hanging down), ω = 0.
-- Terminal: cos(θ) > 0.95 (within ~18° of upright).
--
-- dt = 0.05 (Gymnasium default), 1 sub-step per action.
------------------------------------------------------------------------

module CSHRL.Tasks.Stochastic.PendulumLoop where

open import Data.Bool using (Bool; true; false; not; _∧_)
open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _*_; _≤ᵇ_)
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

State : Set
State = ℤ × ℤ   -- (θ, ω) in fixed-point scale 10⁸

data PAction : Set where
  TorqueNeg TorquePos : PAction

------------------------------------------------------------------------
-- Fixed-point arithmetic and ODE
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

  sin₇ : ℤ → ℤ
  sin₇ y =
    let y² = y f* y
        y³ = y² f* y
        y⁵ = y³ f* y²
        y⁷ = y⁵ f* y²
        y⁹ = y⁷ f* y²
        y¹¹ = y⁹ f* y²
        y¹³ = y¹¹ f* y²
    in y −ℤ (y³  ÷ℤ 6) +ℤ (y⁵  ÷ℤ 120)
       −ℤ (y⁷  ÷ℤ 5040) +ℤ (y⁹  ÷ℤ 362880)
       −ℤ (y¹¹ ÷ℤ 39916800) +ℤ (y¹³ ÷ℤ 6227020800)

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

  -- Gymnasium: θ̈ = -3g/(2l) sin(θ+π) + 3/(ml²) u
  --   sin(θ+π) = -sin(θ), so θ̈ = 15 sin(θ) + 3u
  -- Fixed-point: 15 = 1500000000, 3 = 300000000
  -- dt = 0.05 = 5000000, ω_max = 8 = 800000000
  act-f : PAction → ℤ
  act-f TorqueNeg = ℤneg (+ 200000000)   -- u = -2
  act-f TorquePos = + 200000000           -- u = +2

  dt : ℤ
  dt = + 5000000                           -- 0.05

  ω-max : ℤ
  ω-max = + 800000000                      -- 8.0

step : State → PAction → State
step (θ , ω) a =
  let grav = (+ 1500000000) f* sin₇ θ     -- 15 · sin(θ) in fixed-point
      u    = (+ 300000000) f* act-f a      -- 3 · u in fixed-point
      acc  = grav +ℤ u                     -- θ̈ in fixed-point
      ω'   = fclip (ℤneg ω-max) ω-max (ω +ℤ acc f* dt)
      θ'   = θ +ℤ ω' f* dt
  in (θ' , ω')

-- Terminal: cos(θ) > 0.95 (within ~18° of upright)
-- cos(θ) > 95000000 in fixed-point
terminal? : State → Bool
terminal? (θ , _) with (+ 95000000) ≤?ℤ cos₇ θ
... | yes _ = true
... | no  _ = false

------------------------------------------------------------------------
-- Feature instantiation via ContinuousFeatures
------------------------------------------------------------------------

private
  get-dim : State → ℕ → ℤ
  get-dim (θ , _) zero          = θ
  get-dim (_ , ω) (suc zero)    = ω
  get-dim _       (suc (suc _)) = + 0

module PC = ContFeatures State 2 get-dim

------------------------------------------------------------------------
-- Generic CSHRL loop instantiation
------------------------------------------------------------------------

open Loop State PC.CFeature PC.eval-cf
open PC.ActionChain PAction

private
  pol-of : PredProg → State → PAction
  pol-of p = eval-chain ((p , TorqueNeg) ∷ []) TorquePos

  -- Start: θ = π (hanging down), ω = 0
  s₀ : State
  s₀ = (+ 314159265 , + 0)                -- (π, 0)

  H : ℕ
  H = 200

  K : ℕ
  K = 50

  goal-score : State → (State → PAction) → ℕ → ℕ
  goal-score _ _ zero    = 0
  goal-score s π (suc k) with terminal? s
  ... | true  = suc k
  ... | false = goal-score (step s (π s)) π k

  goal-rollout : State → PAction → (State → PAction) → ℕ → ℕ
  goal-rollout _ _ _ zero    = 0
  goal-rollout s a π (suc k) with terminal? s
  ... | true  = suc k
  ... | false = let s' = step s a
                in goal-rollout s' (π s') π k

  collect : State → (State → PAction) → ℕ → List State
  collect _ _ zero    = []
  collect s π (suc n) with terminal? s
  ... | true  = []
  ... | false = s ∷ collect (step s (π s)) π n

  score-p : PredProg → ℕ
  score-p p = goal-score s₀ (pol-of p) H

  oracle-p : PredProg → State → Bool
  oracle-p p s = goal-rollout s TorquePos (pol-of p) K
               ≤ᵇ goal-rollout s TorqueNeg (pol-of p) K

  traj-p : PredProg → List State
  traj-p p = collect s₀ (pol-of p) 10

  feats-p : List State → List PC.CFeature
  feats-p = PC.adaptive-features 2

open Iterate score-p oracle-p traj-p feats-p

------------------------------------------------------------------------
-- Run the CSHRL loop — depth 0
------------------------------------------------------------------------

result : Result
result = run 0

rank★ : PredProg
rank★ = rank-of result

-- The discovered ranking: ω < 0.855 (velocity threshold)
-- Policy: TorqueNeg when ω < 0.855, TorquePos when ω ≥ 0.855
open PC using (axis)

rank-is : rank★ ≡ feat (axis 1 (+ 85548331))
rank-is = refl
