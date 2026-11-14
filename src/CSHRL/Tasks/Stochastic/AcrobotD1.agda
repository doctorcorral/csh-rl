{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Stochastic.AcrobotD1
--
-- Depth-1 CSHRL CoindHomo search for Acrobot swing-up.
--
-- Since depth 0 yields cegar-needed (AcrobotLoop), this module
-- attempts depth 1.  To keep the candidate space manageable
-- (O(n²) at depth 1), we use shorter trajectory collection (5 steps)
-- and no diagonal features (max-coeff = 0).
--
-- Result: ¬(axis 2 (+ 0)), i.e., ¬(dθ₁ < 0), i.e., sign(dθ₁).
-- Interestingly, the gridless search discovers sign(dθ₁) rather
-- than sign(dθ₂) from the grid-based controller.  Both angular
-- velocities capture the energy-pumping strategy.
------------------------------------------------------------------------

module CSHRL.Tasks.Stochastic.AcrobotD1 where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _*_; _≤ᵇ_)
open import Data.Integer.Base as ℤ using (ℤ; +_; -[1+_])
  renaming (_+_ to _+ℤ_; _*_ to _*ℤ_; _-_ to _−ℤ_; -_ to ℤneg)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import CSHRL.Synthesis.ContinuousFeatures
open import CSHRL.Synthesis.CSHRLLoop

open import CSHRL.Tasks.Stochastic.AcrobotAutoController
  using ( CState; AcroAction; TorqueNeg; NoTorque; TorquePos
        ; continuous-step; continuous-terminal?
        )

------------------------------------------------------------------------
-- State, step, terminal
------------------------------------------------------------------------

State : Set
State = CState

step : State → AcroAction → State
step = continuous-step

terminal? : State → Bool
terminal? = continuous-terminal?

------------------------------------------------------------------------
-- Feature instantiation: 4 dimensions
------------------------------------------------------------------------

private
  get-dim : State → ℕ → ℤ
  get-dim (θ₁ , _  , _  , _  ) zero                      = θ₁
  get-dim (_  , θ₂ , _  , _  ) (suc zero)                 = θ₂
  get-dim (_  , _  , dθ₁ , _ ) (suc (suc zero))           = dθ₁
  get-dim (_  , _  , _  , dθ₂) (suc (suc (suc zero)))     = dθ₂
  get-dim _                    (suc (suc (suc (suc _))))   = + 0

module AC = ContFeatures State 4 get-dim

------------------------------------------------------------------------
-- CSHRL loop instantiation
------------------------------------------------------------------------

open Loop State AC.CFeature AC.eval-cf
open AC.ActionChain AcroAction

private
  pol-of : PredProg → State → AcroAction
  pol-of p = eval-chain ((p , TorqueNeg) ∷ []) TorquePos

  s₀ : State
  s₀ = (+ 0 , + 0 , + 0 , + 0)

  H : ℕ
  H = 200

  K : ℕ
  K = 50

  goal-score : State → (State → AcroAction) → ℕ → ℕ
  goal-score _ _ zero    = 0
  goal-score s π (suc k) with terminal? s
  ... | true  = suc k
  ... | false = goal-score (step s (π s)) π k

  goal-rollout : State → AcroAction → (State → AcroAction) → ℕ → ℕ
  goal-rollout _ _ _ zero    = 0
  goal-rollout s a π (suc k) with terminal? s
  ... | true  = suc k
  ... | false = let s' = step s a
                in goal-rollout s' (π s') π k

  collect : State → (State → AcroAction) → ℕ → List State
  collect _ _ zero    = []
  collect s π (suc n) with terminal? s
  ... | true  = []
  ... | false = s ∷ collect (step s (π s)) π n

  score-ac : PredProg → ℕ
  score-ac p = goal-score s₀ (pol-of p) H

  oracle-ac : PredProg → State → Bool
  oracle-ac p s = goal-rollout s TorquePos (pol-of p) K
               ≤ᵇ goal-rollout s TorqueNeg (pol-of p) K

  traj-ac : PredProg → List State
  traj-ac p = collect s₀ (pol-of p) 2

  feats-ac : List State → List AC.CFeature
  feats-ac = AC.adaptive-features 0

open Iterate score-ac oracle-ac traj-ac feats-ac

------------------------------------------------------------------------
-- Depth-1 attempt
------------------------------------------------------------------------

result-d1 : Result
result-d1 = run 1

rank-d1 : PredProg
rank-d1 = rank-of result-d1

-- The discovered ranking: ¬(dθ₁ < 0), i.e., dθ₁ ≥ 0
-- Policy: TorqueNeg when dθ₁ ≥ 0, TorquePos when dθ₁ < 0
open AC using (axis)

rank-is : rank-d1 ≡ ¬p feat (axis 2 (+ 0))
rank-is = refl
