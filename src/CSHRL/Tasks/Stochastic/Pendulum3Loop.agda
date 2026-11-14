{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Stochastic.Pendulum3Loop
--
-- Gridless CoindHomo search for Pendulum with 3 actions:
--   TorqueNeg (-2), NoTorque (0), TorquePos (+2)
--
-- Demonstrates the ActionChain mechanism for k = 3 actions.
-- The ranking is a DECISION CHAIN of two predicates:
--
--   eval-chain ((p₁, TorqueNeg) ∷ (p₂, NoTorque) ∷ []) TorquePos
--
--   ≡ if p₁(s) then TorqueNeg
--     else if p₂(s) then NoTorque
--     else TorquePos
--
-- Two-stage search:
--   Stage 1: find p₁ separating TorqueNeg from TorquePos
--            (expected: ω < 0.855, same as 2-action PendulumLoop)
--   Stage 2: find p₂ — when to coast (NoTorque) instead of pushing
------------------------------------------------------------------------

module CSHRL.Tasks.Stochastic.Pendulum3Loop where

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
-- State, Action (3 actions)
------------------------------------------------------------------------

State : Set
State = ℤ × ℤ   -- (θ, ω) in fixed-point scale 10⁸

data P3Action : Set where
  TorqueNeg NoTorque TorquePos : P3Action

------------------------------------------------------------------------
-- Fixed-point arithmetic and ODE (same as PendulumLoop)
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

  act-f : P3Action → ℤ
  act-f TorqueNeg = ℤneg (+ 200000000)   -- u = -2
  act-f NoTorque  = + 0                   -- u =  0
  act-f TorquePos = + 200000000           -- u = +2

  dt : ℤ
  dt = + 5000000                           -- 0.05

  ω-max : ℤ
  ω-max = + 800000000                      -- 8.0

step : State → P3Action → State
step (θ , ω) a =
  let grav = (+ 1500000000) f* sin₇ θ     -- 15 · sin(θ)
      u    = (+ 300000000) f* act-f a      -- 3 · u
      acc  = grav +ℤ u
      ω'   = fclip (ℤneg ω-max) ω-max (ω +ℤ acc f* dt)
      θ'   = θ +ℤ ω' f* dt
  in (θ' , ω')

terminal? : State → Bool
terminal? (θ , _) with (+ 95000000) ≤?ℤ cos₇ θ
... | yes _ = true
... | no  _ = false

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
-- CSHRL loop instantiation
------------------------------------------------------------------------

open Loop State PC.CFeature PC.eval-cf
open PC.ActionChain P3Action

private
  -- Binary policy for Stage 1 (TorqueNeg vs TorquePos only)
  pol-of-binary : PredProg → State → P3Action
  pol-of-binary p = eval-chain ((p , TorqueNeg) ∷ []) TorquePos

  s₀ : State
  s₀ = (+ 314159265 , + 0)                -- (π, 0)

  H : ℕ
  H = 200

  K : ℕ
  K = 50

  goal-score : State → (State → P3Action) → ℕ → ℕ
  goal-score _ _ zero    = 0
  goal-score s π (suc k) with terminal? s
  ... | true  = suc k
  ... | false = goal-score (step s (π s)) π k

  goal-rollout : State → P3Action → (State → P3Action) → ℕ → ℕ
  goal-rollout _ _ _ zero    = 0
  goal-rollout s a π (suc k) with terminal? s
  ... | true  = suc k
  ... | false = let s' = step s a
                in goal-rollout s' (π s') π k

  collect : State → (State → P3Action) → ℕ → List State
  collect _ _ zero    = []
  collect s π (suc n) with terminal? s
  ... | true  = []
  ... | false = s ∷ collect (step s (π s)) π n

------------------------------------------------------------------------
-- Stage 1: find p₁ (TorqueNeg vs TorquePos)
------------------------------------------------------------------------

private
  score-s1 : PredProg → ℕ
  score-s1 p = goal-score s₀ (pol-of-binary p) H

  oracle-s1 : PredProg → State → Bool
  oracle-s1 p s = goal-rollout s TorquePos (pol-of-binary p) K
               ≤ᵇ goal-rollout s TorqueNeg (pol-of-binary p) K

  traj-s1 : PredProg → List State
  traj-s1 p = collect s₀ (pol-of-binary p) 10

  feats-s1 : List State → List PC.CFeature
  feats-s1 = PC.adaptive-features 2

module S1 = Iterate score-s1 oracle-s1 traj-s1 feats-s1

------------------------------------------------------------------------
-- Stage 1 result
------------------------------------------------------------------------

result-s1 : Result
result-s1 = S1.run 0

p₁ : PredProg
p₁ = rank-of result-s1

------------------------------------------------------------------------
-- Stage 2: find p₂ — when to coast (NoTorque) instead of TorquePos
--
-- Full 3-action policy:
--   eval-chain ((p₁, TorqueNeg) ∷ (p₂, NoTorque) ∷ []) TorquePos
------------------------------------------------------------------------

private
  pol-of-3 : PredProg → PredProg → State → P3Action
  pol-of-3 q₁ q₂ = eval-chain ((q₁ , TorqueNeg) ∷ (q₂ , NoTorque) ∷ []) TorquePos

  score-s2 : PredProg → ℕ
  score-s2 p₂ = goal-score s₀ (pol-of-3 p₁ p₂) H

  oracle-s2 : PredProg → State → Bool
  oracle-s2 p₂ s =
    goal-rollout s TorquePos (pol-of-3 p₁ p₂) K
    ≤ᵇ goal-rollout s NoTorque (pol-of-3 p₁ p₂) K

  traj-s2 : PredProg → List State
  traj-s2 p₂ = collect s₀ (pol-of-3 p₁ p₂) 10

  feats-s2 : List State → List PC.CFeature
  feats-s2 = PC.adaptive-features 2

module S2 = Iterate score-s2 oracle-s2 traj-s2 feats-s2

------------------------------------------------------------------------
-- Stage 2 result
------------------------------------------------------------------------

result-s2 : Result
result-s2 = S2.run 0

p₂ : PredProg
p₂ = rank-of result-s2

------------------------------------------------------------------------
-- The full 3-action policy
------------------------------------------------------------------------

π★ : State → P3Action
π★ = pol-of-3 p₁ p₂

------------------------------------------------------------------------
-- Stage 3: find p₃ — TorqueNeg vs NoTorque (the missing pair)
--
-- This completes the FULL RANKING (all C(3,2) = 3 pairwise comparisons):
--   p₁: TorqueNeg vs TorquePos  (Stage 1)
--   p₂: NoTorque  vs TorquePos  (Stage 2)
--   p₃: TorqueNeg vs NoTorque   (Stage 3)
--
-- The full ranking enables ACTION UNAVAILABILITY resilience:
-- if the best action is unavailable, fall back to the next-best.
------------------------------------------------------------------------

private
  pol-of-neg-no : PredProg → State → P3Action
  pol-of-neg-no p = eval-chain ((p , TorqueNeg) ∷ []) NoTorque

  score-s3 : PredProg → ℕ
  score-s3 p₃ = goal-score s₀ (pol-of-neg-no p₃) H

  oracle-s3 : PredProg → State → Bool
  oracle-s3 p₃ s =
    goal-rollout s NoTorque (pol-of-neg-no p₃) K
    ≤ᵇ goal-rollout s TorqueNeg (pol-of-neg-no p₃) K

  traj-s3 : PredProg → List State
  traj-s3 p₃ = collect s₀ (pol-of-neg-no p₃) 10

  feats-s3 : List State → List PC.CFeature
  feats-s3 = PC.adaptive-features 2

module S3 = Iterate score-s3 oracle-s3 traj-s3 feats-s3

------------------------------------------------------------------------
-- Stage 3 result
------------------------------------------------------------------------

result-s3 : Result
result-s3 = S3.run 0

p₃ : PredProg
p₃ = rank-of result-s3

------------------------------------------------------------------------
-- Verification of all three pairwise predicates
------------------------------------------------------------------------

open PC using (axis)

-- p₁: TorqueNeg > TorquePos when ω < 0.855
p₁-is : p₁ ≡ feat (axis 1 (+ 85548331))
p₁-is = refl

-- p₂: NoTorque > TorquePos always
s2-converged : result-s2 ≡ converged p₂
s2-converged = refl

p₂-is : p₂ ≡ truep
p₂-is = refl

-- p₃: TorqueNeg > NoTorque when ω < ~0 (assist negative swing)
-- Threshold 1586 / 10⁸ ≈ 0 → essentially sign(ω)
p₃-is : p₃ ≡ feat (axis 1 (+ 1586))
p₃-is = refl

------------------------------------------------------------------------
-- Restricted Preservation via PairwiseRanking
--
-- The 3 pairwise predicates compose into a FullRanking.
-- Restriction to any 2 actions yields the corresponding pairwise
-- predicate — which was independently verified as a CoindHomo.
-- Action unavailability fallback is O(1): evaluate one predicate.
------------------------------------------------------------------------

open import CSHRL.Synthesis.PairwiseRanking

open ThreeActions State P3Action TorqueNeg NoTorque TorquePos

ranking : FullRanking
ranking = record
  { cmp₁₂ = λ s → eval p₃ s   -- TorqueNeg ≥ NoTorque?
  ; cmp₁₃ = λ s → eval p₁ s   -- TorqueNeg ≥ TorquePos?
  ; cmp₂₃ = λ s → eval p₂ s   -- NoTorque  ≥ TorquePos?
  }

-- Full ranking (3 regions):
--
--   ω < ~0       : TorqueNeg > NoTorque > TorquePos
--   0 ≤ ω < 0.855: NoTorque > TorqueNeg > TorquePos
--   ω ≥ 0.855    : NoTorque > TorquePos > TorqueNeg
--
-- Action unavailability (from PairwiseRanking.restrict-preserves-*):
--   TorqueNeg unavailable → use p₂ (NoTorque vs TorquePos = truep)
--   NoTorque  unavailable → use p₁ (TorqueNeg vs TorquePos = ω<0.855)
--   TorquePos unavailable → use p₃ (TorqueNeg vs NoTorque = ω<~0)
