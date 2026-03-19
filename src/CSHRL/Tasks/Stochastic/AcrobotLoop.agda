{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Stochastic.AcrobotLoop
--
-- Gridless CoindHomo search for Acrobot swing-up.
--
-- 4 dimensions: θ₁, θ₂, θ̇₁, θ̇₂
-- 2 actions: TorqueNeg, TorquePos (NoTorque omitted — the grid-based
--   controller never uses it outside terminal states)
--
-- The grid-based controller discovers sign(θ̇₂): TorqueNeg when
-- θ̇₂ < 0, TorquePos when θ̇₂ ≥ 0.  Can the gridless search
-- rediscover this from the CoindHomo self-consistency condition?
------------------------------------------------------------------------

module CSHRL.Tasks.Stochastic.AcrobotLoop where

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
  traj-ac p = collect s₀ (pol-of p) 10

  feats-ac : List State → List AC.CFeature
  feats-ac = AC.adaptive-features 2

open Iterate score-ac oracle-ac traj-ac feats-ac

------------------------------------------------------------------------
-- Run the CSHRL loop — depth 0
------------------------------------------------------------------------

result : Result
result = run 0

rank★ : PredProg
rank★ = rank-of result

π★ : State → AcroAction
π★ = pol-of rank★

-- Depth 0 hits CEGAR: no single atom is self-consistent among
-- 102 features (78 axis + 24 diagonal).
-- Confirmed by: attempting `result ≡ converged rank★` yields
-- the type error showing `cegar-needed _ != converged _`.
-- Proceed to AcrobotD1.agda for depth-1 search.
