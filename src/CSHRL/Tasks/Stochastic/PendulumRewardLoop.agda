{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Stochastic.PendulumRewardLoop
--
-- Reward-based gridless CoindHomo search for Pendulum stabilization.
--
-- Unlike PendulumLoop/Pendulum3Loop (which optimize goal-reaching time),
-- this module uses Gymnasium's per-step reward to induce the ranking:
--
--   r(s) = -(θ² + 0.1·ω²)
--
-- In CSHRL terms: the reward comparison induces the ordinal ranking.
-- The oracle compares cumulative penalties over K steps — whichever
-- action leads to less penalty (more time near upright, less velocity)
-- is ranked higher.
--
-- No terminal condition: episodes run for full H steps, matching
-- Gymnasium's Pendulum-v1.  This forces the search to discover
-- predicates that STABILIZE at the top, not just swing up.
--
-- 3 actions: TorqueNeg (-2), NoTorque (0), TorquePos (+2).
-- 2-stage search: (1) TorqueNeg vs TorquePos, (2) NoTorque vs TorquePos.
------------------------------------------------------------------------

module CSHRL.Tasks.Stochastic.PendulumRewardLoop where

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
State = ℤ × ℤ   -- (θ, ω) in fixed-point scale 10⁸

data P3Action : Set where
  TorqueNeg NoTorque TorquePos : P3Action

------------------------------------------------------------------------
-- Fixed-point arithmetic and ODE (same dynamics as Pendulum3Loop)
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
-- Reward-based penalty
--
-- Gymnasium: r = -(θ² + 0.1·ω² + 0.001·u²)
-- We use penalty = θ² + ω²/10 (ignoring tiny u² term).
-- Reduced scale: divide by 10⁶ before squaring for ℕ tractability.
--
--   θ_r = |θ| / 10⁶   (range: 0..314 for θ∈[0,π])
--   ω_r = |ω| / 10⁶   (range: 0..800 for ω∈[0,8])
--   penalty = θ_r² + ω_r²/10
--   Per step: max ≈ 163000.  Over 200 steps: max ≈ 32.6M.
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
-- CSHRL loop instantiation (reward-based)
--
-- Key insight: the STABILIZATION question is TorqueNeg vs NoTorque —
-- when to apply torque vs coast.  TorquePos is dominated by TorqueNeg
-- for swing-up (truep), so the interesting search is the binary
-- TorqueNeg/NoTorque comparison.
------------------------------------------------------------------------

open Loop State PC.CFeature PC.eval-cf
open PC.ActionChain P3Action

private
  -- Start hanging down, same as PendulumLoop — no tricks.
  -- The trajectory naturally passes through upright during swing-up.
  -- The reward-based oracle (no terminal) captures stabilization:
  -- actions that KEEP the pendulum near upright accumulate less penalty.
  s₀ : State
  s₀ = (+ 314159265 , + 0)                -- (π, 0)

  H : ℕ
  H = 200

  -- K must be large enough that the pendulum reaches upright AND
  -- the oracle sees the difference between "stays" and "passes through".
  -- At ~10 steps to swing up, K=100 gives 90 steps of post-swing-up
  -- signal for the oracle to evaluate stabilization.
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
  -- Binary search: TorqueNeg vs NoTorque
  --
  -- p(s) = true → TorqueNeg (-2), p(s) = false → NoTorque (0)
  -- This is the core stabilization question:
  -- "when should we apply torque vs coast?"
  ------------------------------------------------------------------------

  pol-of : PredProg → State → P3Action
  pol-of p = eval-chain ((p , TorqueNeg) ∷ []) NoTorque

  score-rw : PredProg → ℕ
  score-rw p = penalty-score s₀ (pol-of p) H

  oracle-rw : PredProg → State → Bool
  oracle-rw p s =
    penalty-rollout s TorqueNeg (pol-of p) K
    ≤ᵇ penalty-rollout s NoTorque (pol-of p) K

  -- Longer trajectory to capture both swing-up AND post-swing-up states.
  -- At 20+ steps, the pendulum has passed through upright at least once
  -- under most policies, so we get stabilization-relevant states.
  traj-rw : PredProg → List State
  traj-rw p = collect s₀ (pol-of p) 30

  feats-rw : List State → List PC.CFeature
  feats-rw = PC.adaptive-features 2

open Iterate score-rw oracle-rw traj-rw feats-rw

------------------------------------------------------------------------
-- Run the search — depth 0 (for reference)
------------------------------------------------------------------------

result-d0 : Result
result-d0 = run 0

p-d0 : PredProg
p-d0 = rank-of result-d0

------------------------------------------------------------------------
-- Run the search — depth 1 (conjunctions/disjunctions of axis thresholds)
--
-- Depth 1 can express predicates like:
--   (θ < t₁) ∧ (ω < t₂)  — "near upright AND slow"
--   (θ < t₁) ∨ (ω < t₂)  — "near upright OR slow"
-- These capture the 2D structure needed for stabilization.
------------------------------------------------------------------------

result-d1 : Result
result-d1 = run 1

p★ : PredProg
p★ = rank-of result-d1

π★ : State → P3Action
π★ = pol-of p★

------------------------------------------------------------------------
-- Diagnostics
------------------------------------------------------------------------

open PC using (axis; diag)

-- Depth 0 result: ω < -0.048 (velocity-only, essentially same as ω < 0)
d0-is : p-d0 ≡ feat (axis 1 -[1+ 4832331 ])
d0-is = refl

-- Did depth 1 converge?
d1-converged : result-d1 ≡ converged p★
d1-converged = refl

-- Depth-1 predicate: (θ < 0.305) ∨ (ω < 0.022)
-- A disjunction combining angle and velocity — exactly the 2D structure
-- needed for stabilization: apply TorqueNeg when near-upright OR slow.
p★-is : p★ ≡ feat (axis 0 (+ 305438784)) ∨p feat (axis 1 (+ 21575924))
p★-is = refl
