{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Stochastic.MountainCar3Loop
--
-- Gridless CoindHomo search for MountainCar with ALL 3 actions:
--   PushLeft (0), NoAction (1), PushRight (2)
--
-- Demonstrates the ActionChain mechanism for k > 2 actions.
-- The ranking becomes a DECISION CHAIN of two predicates:
--
--   eval-chain ((p₁, PushLeft) ∷ (p₂, NoAction) ∷ []) PushRight
--
--   ≡ if p₁(s) then PushLeft
--     else if p₂(s) then NoAction
--     else PushRight
--
-- Two predicates = full ranking over 3 actions at each state.
--
-- Search strategy: two-stage binary decomposition.
--   Stage 1: find p₁ separating PushLeft from PushRight
--            (ignoring NoAction — the extreme actions)
--   Stage 2: find p₂ separating NoAction from the Stage-1 policy
--            (when should we coast instead of pushing?)
------------------------------------------------------------------------

module CSHRL.Tasks.Stochastic.MountainCar3Loop where

open import Data.Bool using (Bool; true; false; not; _∧_)
open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _*_; _≤ᵇ_)
open import Data.Nat.DivMod using () renaming (_/_ to _ℕ/_)
open import Data.Integer.Base as ℤ
  using (ℤ; +_; -[1+_]; ∣_∣)
  renaming (_+_ to _+ℤ_; _*_ to _*ℤ_; _-_ to _−ℤ_; -_ to ℤneg)
open import Data.Integer.Properties as ℤP
  using () renaming (_<?_ to _<?ℤ_; _≤?_ to _≤?ℤ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; map; length; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

open import CSHRL.Synthesis.ContinuousFeatures
open import CSHRL.Synthesis.CSHRLLoop

------------------------------------------------------------------------
-- State, Action, ODE  (3 actions)
------------------------------------------------------------------------

State : Set
State = ℤ × ℤ

data MC3Action : Set where
  PushLeft NoAction PushRight : MC3Action

------------------------------------------------------------------------
-- Dynamics (same as MountainCarLoop, but with 3 actions)
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

  act-f : MC3Action → ℤ
  act-f PushLeft  = ℤneg (+ 100000)
  act-f NoAction  = + 0
  act-f PushRight = + 100000

  sub-step : State → MC3Action → State
  sub-step (x , v) a =
    let grav = cos₇ ((+ 300000000) f* x) f* ℤneg (+ 250000)
        v'   = fclip (ℤneg (+ 7000000)) (+ 7000000)
                 (v +ℤ act-f a +ℤ grav)
        x'   = fclip (ℤneg (+ 120000000)) (+ 60000000) (x +ℤ v')
    in (x' , wall x' v')

  multi-step : ℕ → State → MC3Action → State
  multi-step zero    st _ = st
  multi-step (suc n) st a = multi-step n (sub-step st a) a

step : State → MC3Action → State
step s a = multi-step 25 s a

terminal? : State → Bool
terminal? (x , _) with (+ 50000000) ≤?ℤ x
... | yes _ = true
... | no  _ = false

------------------------------------------------------------------------
-- Feature instantiation
------------------------------------------------------------------------

private
  get-dim : State → ℕ → ℤ
  get-dim (x , _) zero          = x
  get-dim (_ , v) (suc zero)    = v
  get-dim _       (suc (suc _)) = + 0

module MC = ContFeatures State 2 get-dim

------------------------------------------------------------------------
-- Stage 1: Binary search (PushLeft vs PushRight)
-- Same as the 2-action MountainCarLoop
------------------------------------------------------------------------

open Loop State MC.CFeature MC.eval-cf
open MC.ActionChain MC3Action

private
  -- Stage 1 policy: binary PushLeft vs PushRight
  pol-of-binary : PredProg → State → MC3Action
  pol-of-binary p = eval-chain ((p , PushLeft) ∷ []) PushRight

  s₀ : State
  s₀ = (ℤneg (+ 50000000) , + 0)

  H : ℕ
  H = 200

  K : ℕ
  K = 50

  goal-score : (State → MC3Action) → ℕ → State → ℕ
  goal-score _ zero    _ = 0
  goal-score π (suc k) s with terminal? s
  ... | true  = suc k
  ... | false = goal-score π k (step s (π s))

  goal-rollout : MC3Action → (State → MC3Action) → ℕ → State → ℕ
  goal-rollout _ _ zero    _ = 0
  goal-rollout a π (suc k) s with terminal? s
  ... | true  = suc k
  ... | false = let s' = step s a
                in goal-rollout (π s') π k s'

  collect-gen : (State → MC3Action) → ℕ → State → List State
  collect-gen _ zero    _ = []
  collect-gen π (suc n) s with terminal? s
  ... | true  = []
  ... | false = s ∷ collect-gen π n (step s (π s))

  -- Stage 1 instantiation
  score-s1 : PredProg → ℕ
  score-s1 p = goal-score (pol-of-binary p) H s₀

  oracle-s1 : PredProg → State → Bool
  oracle-s1 p s = goal-rollout PushRight (pol-of-binary p) K s
               ≤ᵇ goal-rollout PushLeft  (pol-of-binary p) K s

  traj-s1 : PredProg → List State
  traj-s1 p = collect-gen (pol-of-binary p) 6 s₀

  feats-s1 : List State → List MC.CFeature
  feats-s1 = MC.adaptive-features 2

module S1 = Iterate score-s1 oracle-s1 traj-s1 feats-s1

------------------------------------------------------------------------
-- Stage 1 result
------------------------------------------------------------------------

result-s1 : Result
result-s1 = S1.run 1

p₁ : PredProg
p₁ = rank-of result-s1

------------------------------------------------------------------------
-- Stage 2: find p₂ — when to coast (NoAction) instead of pushing
--
-- The 3-action policy is:
--   eval-chain ((p₁, PushLeft) ∷ (p₂, NoAction) ∷ []) PushRight
--
-- p₂ fires in the region where p₁ is false (would push Right).
-- The oracle compares NoAction vs PushRight at each state.
------------------------------------------------------------------------

private
  pol-of-3 : PredProg → PredProg → State → MC3Action
  pol-of-3 q₁ q₂ = eval-chain ((q₁ , PushLeft) ∷ (q₂ , NoAction) ∷ []) PushRight

  -- Stage 2: search for p₂ given the fixed p₁
  score-s2 : PredProg → ℕ
  score-s2 p₂ = goal-score (pol-of-3 p₁ p₂) H s₀

  oracle-s2 : PredProg → State → Bool
  oracle-s2 p₂ s =
    goal-rollout PushRight (pol-of-3 p₁ p₂) K s
    ≤ᵇ goal-rollout NoAction (pol-of-3 p₁ p₂) K s

  traj-s2 : PredProg → List State
  traj-s2 p₂ = collect-gen (pol-of-3 p₁ p₂) 6 s₀

  feats-s2 : List State → List MC.CFeature
  feats-s2 = MC.adaptive-features 2

module S2 = Iterate score-s2 oracle-s2 traj-s2 feats-s2

------------------------------------------------------------------------
-- Stage 2 result
------------------------------------------------------------------------

result-s2 : Result
result-s2 = S2.run 1

p₂ : PredProg
p₂ = rank-of result-s2

------------------------------------------------------------------------
-- The full 3-action policy
------------------------------------------------------------------------

π★ : State → MC3Action
π★ = pol-of-3 p₁ p₂

-- Diagnostics: reveal both predicates
show-p₁ : p₁ ≡ falsep
show-p₁ = refl

show-p₂ : p₂ ≡ falsep
show-p₂ = refl
