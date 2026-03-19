{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Stochastic.PendulumReward3Loop
--
-- Full 3-action reward-based gridless CoindHomo search for Pendulum
-- stabilization, at depth 1 (conjunctions/disjunctions).
--
-- Three pairwise searches (all C(3,2) = 3 pairs):
--   S1: TorqueNeg vs TorquePos   — swing direction
--   S2: NoTorque  vs TorquePos   — coast vs push
--   S3: TorqueNeg vs NoTorque    — brake vs coast (stabilization core)
--
-- Oracle: cumulative penalty over full horizon K (no early termination).
--   penalty(s) = θ² + ω²/10
-- This forces the search to discover predicates that STABILIZE, not
-- just swing up.
------------------------------------------------------------------------

module CSHRL.Tasks.Stochastic.PendulumReward3Loop where

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

State : Set
State = ℤ × ℤ

data P3Action : Set where
  TorqueNeg NoTorque TorquePos : P3Action

------------------------------------------------------------------------
-- Dynamics (identical to Pendulum3Loop / PendulumRewardLoop)
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

  fclip : ℤ → ℤ → ℤ → ℤ
  fclip lo hi x with lo ≤?ℤ x
  ... | no  _ = lo
  ... | yes _ with x ≤?ℤ hi
  ...   | yes _ = x
  ...   | no  _ = hi

  act-f : P3Action → ℤ
  act-f TorqueNeg = ℤneg (+ 200000000)
  act-f NoTorque  = + 0
  act-f TorquePos = + 200000000

  dt : ℤ
  dt = + 5000000

  ω-max : ℤ
  ω-max = + 800000000

step : State → P3Action → State
step (θ , ω) a =
  let grav = (+ 1500000000) f* sin₇ θ
      u    = (+ 300000000) f* act-f a
      acc  = grav +ℤ u
      ω'   = fclip (ℤneg ω-max) ω-max (ω +ℤ acc f* dt)
      θ'   = θ +ℤ ω' f* dt
  in (θ' , ω')

------------------------------------------------------------------------
-- Reward-based penalty (same as PendulumRewardLoop)
------------------------------------------------------------------------

private
  scale-down : ℤ → ℕ
  scale-down x = ∣ x ∣ ℕ/ 1000000

  penalty : State → ℕ
  penalty (θ , ω) =
    let θr = scale-down θ
        ωr = scale-down ω
    in θr * θr + (ωr * ωr) ℕ/ 10

  max-penalty-per-step : ℕ
  max-penalty-per-step = 200000

------------------------------------------------------------------------
-- Feature instantiation
------------------------------------------------------------------------

private
  get-dim : State → ℕ → ℤ
  get-dim (θ , _) zero          = θ
  get-dim (_ , ω) (suc zero)    = ω
  get-dim _       (suc (suc _)) = + 0

module PC = ContFeatures State 2 get-dim

------------------------------------------------------------------------
-- Shared infrastructure
------------------------------------------------------------------------

open Loop State PC.CFeature PC.eval-cf
open PC.ActionChain P3Action

private
  s₀ : State
  s₀ = (+ 314159265 , + 0)

  H : ℕ
  H = 200

  K : ℕ
  K = 100

  penalty-rollout : State → P3Action → (State → P3Action) → ℕ → ℕ
  penalty-rollout _ _ _ zero    = 0
  penalty-rollout s a π (suc k) =
    let s' = step s a
    in penalty s + penalty-rollout s' (π s') π k

  penalty-score : State → (State → P3Action) → ℕ → ℕ
  penalty-score _ _ zero    = 0
  penalty-score s π (suc k) =
    let s' = step s (π s)
    in (max-penalty-per-step ∸ penalty s) + penalty-score s' π k

  collect : State → (State → P3Action) → ℕ → List State
  collect _ _ zero    = []
  collect s π (suc n) = s ∷ collect (step s (π s)) π n

------------------------------------------------------------------------
-- Stage 1: TorqueNeg vs TorquePos
------------------------------------------------------------------------

private
  pol-s1 : PredProg → State → P3Action
  pol-s1 p = eval-chain ((p , TorqueNeg) ∷ []) TorquePos

  score-s1 : PredProg → ℕ
  score-s1 p = penalty-score s₀ (pol-s1 p) H

  oracle-s1 : PredProg → State → Bool
  oracle-s1 p s =
    penalty-rollout s TorqueNeg (pol-s1 p) K
    ≤ᵇ penalty-rollout s TorquePos (pol-s1 p) K

  traj-s1 : PredProg → List State
  traj-s1 p = collect s₀ (pol-s1 p) 30

  feats-s1 : List State → List PC.CFeature
  feats-s1 = PC.adaptive-features 2

module S1 = Iterate score-s1 oracle-s1 traj-s1 feats-s1

result-s1 : Result
result-s1 = S1.run 1

p₁ : PredProg
p₁ = rank-of result-s1

------------------------------------------------------------------------
-- Stage 2: NoTorque vs TorquePos
------------------------------------------------------------------------

private
  pol-s2 : PredProg → State → P3Action
  pol-s2 p = eval-chain ((p , NoTorque) ∷ []) TorquePos

  score-s2 : PredProg → ℕ
  score-s2 p = penalty-score s₀ (pol-s2 p) H

  oracle-s2 : PredProg → State → Bool
  oracle-s2 p s =
    penalty-rollout s NoTorque (pol-s2 p) K
    ≤ᵇ penalty-rollout s TorquePos (pol-s2 p) K

  traj-s2 : PredProg → List State
  traj-s2 p = collect s₀ (pol-s2 p) 30

  feats-s2 : List State → List PC.CFeature
  feats-s2 = PC.adaptive-features 2

module S2 = Iterate score-s2 oracle-s2 traj-s2 feats-s2

result-s2 : Result
result-s2 = S2.run 1

p₂ : PredProg
p₂ = rank-of result-s2

------------------------------------------------------------------------
-- Stage 3: TorqueNeg vs NoTorque
------------------------------------------------------------------------

private
  pol-s3 : PredProg → State → P3Action
  pol-s3 p = eval-chain ((p , TorqueNeg) ∷ []) NoTorque

  score-s3 : PredProg → ℕ
  score-s3 p = penalty-score s₀ (pol-s3 p) H

  oracle-s3 : PredProg → State → Bool
  oracle-s3 p s =
    penalty-rollout s TorqueNeg (pol-s3 p) K
    ≤ᵇ penalty-rollout s NoTorque (pol-s3 p) K

  traj-s3 : PredProg → List State
  traj-s3 p = collect s₀ (pol-s3 p) 30

  feats-s3 : List State → List PC.CFeature
  feats-s3 = PC.adaptive-features 2

module S3 = Iterate score-s3 oracle-s3 traj-s3 feats-s3

result-s3 : Result
result-s3 = S3.run 1

p₃ : PredProg
p₃ = rank-of result-s3

------------------------------------------------------------------------
-- Full ranking composition
------------------------------------------------------------------------

open import CSHRL.Synthesis.PairwiseRanking

open ThreeActions State P3Action TorqueNeg NoTorque TorquePos

ranking : FullRanking
ranking = record
  { cmp₁₂ = λ s → eval p₃ s   -- TorqueNeg ≥ NoTorque?
  ; cmp₁₃ = λ s → eval p₁ s   -- TorqueNeg ≥ TorquePos?
  ; cmp₂₃ = λ s → eval p₂ s   -- NoTorque  ≥ TorquePos?
  }

π★ : State → P3Action
π★ = best ranking

------------------------------------------------------------------------
-- Diagnostics — reveal discovered predicates
------------------------------------------------------------------------

open PC using (axis)

s1-converged : result-s1 ≡ converged p₁
s1-converged = refl

s2-converged : result-s2 ≡ converged p₂
s2-converged = refl

s3-converged : result-s3 ≡ converged p₃
s3-converged = refl

-- Reveal predicates (falsep is a dummy; Agda error shows actual)
p₁-check : p₁ ≡ falsep
p₁-check = refl

p₂-check : p₂ ≡ falsep
p₂-check = refl

p₃-check : p₃ ≡ falsep
p₃-check = refl
