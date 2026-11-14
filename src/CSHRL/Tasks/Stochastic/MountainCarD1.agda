{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Stochastic.MountainCarD1
--
-- Depth-1 CSHRL CoindHomo search for MountainCar.
--
-- Since depth 0 yields cegar-needed (MountainCarLoop), this module
-- attempts depth 1 with adaptive features (axis + diagonal).
--
-- NOTE: depth 1 generates O(n²) candidates where n ≈ 30 atoms.
-- Each candidate requires a full self-consistency check (trajectory +
-- oracle evaluation with 25-sub-step Euler integration).
-- Type-checking is computationally very expensive.
------------------------------------------------------------------------

module CSHRL.Tasks.Stochastic.MountainCarD1 where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _*_; _≤ᵇ_)
open import Data.Integer.Base as ℤ using (ℤ; +_; -[1+_])
  renaming (_+_ to _+ℤ_; _*_ to _*ℤ_; _-_ to _−ℤ_; -_ to ℤneg)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import CSHRL.Synthesis.ContinuousFeatures
open import CSHRL.Synthesis.CSHRLLoop

open import CSHRL.Tasks.Stochastic.MountainCarLoop
  using (State; MCAction; PushLeft; PushRight; step; terminal?)

------------------------------------------------------------------------
-- Feature instantiation (same as MountainCarLoop)
------------------------------------------------------------------------

private
  get-dim-mc : State → ℕ → ℤ
  get-dim-mc (x , _) zero          = x
  get-dim-mc (_ , v) (suc zero)    = v
  get-dim-mc _       (suc (suc _)) = + 0

module MC = ContFeatures State 2 get-dim-mc

------------------------------------------------------------------------
-- CSHRL loop instantiation (adaptive features)
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
-- Depth-1 attempt
------------------------------------------------------------------------

result-d1 : Result
result-d1 = run 1

rank-d1 : PredProg
rank-d1 = rank-of result-d1

convergence-d1 : result-d1 ≡ converged rank-d1
convergence-d1 = refl

-- The discovered ranking: ¬(x < -31846297), i.e., x ≥ -0.318
-- Policy: PushLeft when x ≥ -0.318, PushRight otherwise (swing-up)
rank-is : rank-d1 ≡ ¬p feat (axis 0 -[1+ 31846296 ])
  where open MC.DSL; open MC
rank-is = refl
