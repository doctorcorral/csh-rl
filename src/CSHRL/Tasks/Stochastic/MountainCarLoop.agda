{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Stochastic.MountainCarLoop
--
-- Model-free CSHRL learning on continuous MountainCar, purely in Agda.
--
-- Uses the generic CSHRLLoop with adaptive features.
-- Features are derived automatically from trajectory states
-- (axis thresholds + diagonal linear combinations).
--
-- The CoindHomo search checks each candidate for self-consistency:
-- does eval(rank, s) = oracle(rank, s) at every trajectory state?
--
-- At depth 0, no candidate is both self-consistent AND reaches the
-- goal, so the result is cegar-needed — a genuine CEGAR trigger.
-- The depth-0 barrier reflects non-monotonic oracle dynamics:
-- the optimal action depends on both position and velocity in ways
-- that a single threshold predicate cannot capture.
------------------------------------------------------------------------

module CSHRL.Tasks.Stochastic.MountainCarLoop where

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
-- State, Action, ODE
------------------------------------------------------------------------

State : Set
State = ℤ × ℤ

data MCAction : Set where
  PushLeft PushRight : MCAction

------------------------------------------------------------------------
-- Black-box environment: 25-sub-step Euler integration
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

terminal? : State → Bool
terminal? (x , _) with (+ 50000000) ≤?ℤ x
... | yes _ = true
... | no  _ = false

------------------------------------------------------------------------
-- Feature instantiation via ContinuousFeatures
------------------------------------------------------------------------

private
  get-dim-mc : State → ℕ → ℤ
  get-dim-mc (x , _) zero          = x
  get-dim-mc (_ , v) (suc zero)    = v
  get-dim-mc _       (suc (suc _)) = + 0

module MC = ContFeatures State 2 get-dim-mc

------------------------------------------------------------------------
-- Generic CSHRL loop instantiation (adaptive features)
------------------------------------------------------------------------

open Loop State MC.CFeature MC.eval-cf
open MC.ActionChain MCAction

private
  pol-of : PredProg → State → MCAction
  pol-of p = eval-chain ((p , PushLeft) ∷ []) PushRight

  s₀ : State
  s₀ = (ℤneg (+ 50000000) , + 0)

  H : ℕ
  H = 200

  K : ℕ
  K = 50

  goal-score : State → (State → MCAction) → ℕ → ℕ
  goal-score _ _ zero    = 0
  goal-score s π (suc k) with terminal? s
  ... | true  = suc k
  ... | false = goal-score (step s (π s)) π k

  goal-rollout : State → MCAction → (State → MCAction) → ℕ → ℕ
  goal-rollout _ _ _ zero    = 0
  goal-rollout s a π (suc k) with terminal? s
  ... | true  = suc k
  ... | false = let s' = step s a
                in goal-rollout s' (π s') π k

  collect : State → (State → MCAction) → ℕ → List State
  collect _ _ zero    = []
  collect s π (suc n) with terminal? s
  ... | true  = []
  ... | false = s ∷ collect (step s (π s)) π n

  score-mc : PredProg → ℕ
  score-mc p = goal-score s₀ (pol-of p) H

  oracle-mc : PredProg → State → Bool
  oracle-mc p s = goal-rollout s PushRight (pol-of p) K
               ≤ᵇ goal-rollout s PushLeft  (pol-of p) K

  traj-mc : PredProg → List State
  traj-mc p = collect s₀ (pol-of p) 6

  feats-mc : List State → List MC.CFeature
  feats-mc = MC.adaptive-features 2

open Iterate score-mc oracle-mc traj-mc feats-mc

------------------------------------------------------------------------
-- Run the CSHRL loop
------------------------------------------------------------------------

result : Result
result = run 0

rank★ : PredProg
rank★ = rank-of result

π★ : State → MCAction
π★ = pol-of rank★

------------------------------------------------------------------------
-- Verification
------------------------------------------------------------------------

private
  cegar-barrier : result ≡ cegar-needed rank★
  cegar-barrier = refl
