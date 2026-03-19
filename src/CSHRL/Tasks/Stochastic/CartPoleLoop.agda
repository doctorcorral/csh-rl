{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Stochastic.CartPoleLoop
--
-- Model-free CSHRL learning on continuous CartPole, purely in Agda.
--
-- Uses the generic CSHRLLoop with adaptive features — features are
-- derived automatically from trajectory states each iteration.
-- No manual threshold selection.
--
-- The loop seeds with truep (trivial ranking), collects a trajectory,
-- derives axis-threshold features from visited states, enumerates
-- predicates, filters by oracle, and iterates until convergence.
------------------------------------------------------------------------

module CSHRL.Tasks.Stochastic.CartPoleLoop where

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

data Action : Set where
  Left Right : Action

private
  S : ℕ
  S = 100000000

  negℕ : ℕ → ℤ
  negℕ zero    = + 0
  negℕ (suc n) = -[1+ n ]

  _÷ℤ_ : ℤ → (d : ℕ) → .{{ℕ.NonZero d}} → ℤ
  (+ m)    ÷ℤ d = + (m ℕ/ d)
  -[1+ m ] ÷ℤ d = negℕ (suc m ℕ/ d)

  force : Action → ℤ
  force Left  = -[1+ 999999999 ]
  force Right = + 1000000000

  τ : ℤ
  τ = + 10000000

euler : State → Action → State
euler (θ , θ̇) a =
  let F   = force a
      t1  = (+ 49 *ℤ θ) ÷ℤ 5
      t2  = (F *ℤ + 10) ÷ℤ 11
      acc = ((t1 −ℤ t2) *ℤ + 66) ÷ℤ 41
      θ'  = θ +ℤ ((τ *ℤ θ̇) ÷ℤ S) +ℤ ((τ *ℤ τ *ℤ acc) ÷ℤ (2 * S * S))
      θ̇'  = θ̇ +ℤ ((τ *ℤ acc) ÷ℤ S)
  in (θ' , θ̇')

private
  lim : ℤ
  lim = + 20900000

terminal? : State → Bool
terminal? (θ , _) with lim ≤?ℤ θ
... | yes _ = true
... | no  _ with θ <?ℤ (ℤneg lim)
...   | yes _ = true
...   | no  _ = false

------------------------------------------------------------------------
-- Feature instantiation via ContinuousFeatures
------------------------------------------------------------------------

private
  get-dim-cp : State → ℕ → ℤ
  get-dim-cp (θ , _) zero          = θ
  get-dim-cp (_ , θ̇) (suc zero)    = θ̇
  get-dim-cp _       (suc (suc _)) = + 0

module CP = ContFeatures State 2 get-dim-cp

------------------------------------------------------------------------
-- Generic CSHRL loop instantiation (adaptive features)
------------------------------------------------------------------------

open Loop State CP.CFeature CP.eval-cf
open CP.ActionChain Action

private
  pol-of : PredProg → State → Action
  pol-of p = eval-chain ((p , Left) ∷ []) Right

  s₀ : State
  s₀ = (+ 0 , + 0)

  H : ℕ
  H = 200

  K : ℕ
  K = 100

  traj-len : State → (State → Action) → ℕ → ℕ
  traj-len _ _ zero    = 0
  traj-len s π (suc n) with terminal? s
  ... | true  = 0
  ... | false = 1 + traj-len (euler s (π s)) π n

  rollout : State → Action → (State → Action) → ℕ → ℕ
  rollout _ _ _ zero    = 0
  rollout s a π (suc k) with terminal? s
  ... | true  = 0
  ... | false = let s' = euler s a
                in 1 + rollout s' (π s') π k

  collect : State → (State → Action) → ℕ → List State
  collect _ _ zero    = []
  collect s π (suc n) with terminal? s
  ... | true  = []
  ... | false = s ∷ collect (euler s (π s)) π n

  score-cp : PredProg → ℕ
  score-cp p = traj-len s₀ (pol-of p) H

  oracle-cp : PredProg → State → Bool
  oracle-cp p s = rollout s Right (pol-of p) K
               ≤ᵇ rollout s Left  (pol-of p) K

  traj-cp : PredProg → List State
  traj-cp p = collect (euler s₀ (pol-of p s₀)) (pol-of p) 10

  feats-cp : List State → List CP.CFeature
  feats-cp = CP.adaptive-features 10

open Iterate score-cp oracle-cp traj-cp feats-cp

------------------------------------------------------------------------
-- Run the CSHRL loop
------------------------------------------------------------------------

result : Result
result = run 0

rank★ : PredProg
rank★ = rank-of result

π★ : State → Action
π★ = pol-of rank★

------------------------------------------------------------------------
-- Verification
------------------------------------------------------------------------

private
  convergence : result ≡ converged rank★
  convergence = refl

  perf★ : traj-len s₀ π★ 200 ≡ 200
  perf★ = refl

  perf★-500 : traj-len s₀ π★ 500 ≡ 500
  perf★-500 = refl
