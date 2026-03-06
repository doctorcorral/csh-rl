{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Stochastic.BiasedBanditFOSD
--
-- FOSD verification for the BiasedBandit environment.
--
-- Demonstrates:
--   1. ArmA FOSD-dominates ArmB at step 0
--   2. FOSD ⟹ E[X] bridge theorem
--   3. Concrete CDF computations
--   4. FOSDCoindHomo for depth 0
--
-- The step-0 FOSD is the key result: CDF(ArmA, r) ≤ CDF(ArmB, r)
-- for all r. This means ArmA is preferred by ALL monotone utility
-- functions (risk-averse, risk-neutral, risk-seeking).
--
-- For depths > 0, both actions lead to the same state (Playing)
-- and follow the same default policy, so the marginal distributions
-- have equal CDFs. Proving this formally requires lemmas about
-- how CDF distributes over monadic bind -- a well-identified
-- proof obligation for full pointwise FOSD.
--
-- All --safe, no postulates.
------------------------------------------------------------------------

module CSHRL.Tasks.Stochastic.BiasedBanditFOSD where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import CSHRL.Probability.Finite
  using (Dist; bernoulli; total-weight; weighted-sum)
open import CSHRL.Probability.FOSD
  using (_FOSD≤_; FOSD-refl; cdf-weight; fosd→ev; AllBelow;
         bandit-fosd; bandit-ev; armA; armB)

------------------------------------------------------------------------
-- BiasedBandit MDP
------------------------------------------------------------------------

data State : Set where
  Playing : State

data Action : Set where
  ArmA : Action
  ArmB : Action

step : State → Action → Dist (State × ℕ)
step Playing ArmA = bernoulli (Playing , 1) 2 (Playing , 0) 1
step Playing ArmB = bernoulli (Playing , 1) 1 (Playing , 0) 2

all-actions : List Action
all-actions = ArmA ∷ ArmB ∷ []

------------------------------------------------------------------------
-- Open FOSD Core
------------------------------------------------------------------------

open import CSHRL.Core.FOSD
open FOSDCore State Action step all-actions ArmB

------------------------------------------------------------------------
-- Step 0: Immediate FOSD
--
-- immediate-reward-dist Playing ArmA = [(1,2), (0,1)]
-- immediate-reward-dist Playing ArmB = [(1,1), (0,2)]
--
-- CDF(ArmA, 0) = 1 ≤ 2 = CDF(ArmB, 0)  ✓  (strict FOSD here)
-- CDF(ArmA, r≥1) = 3 = CDF(ArmB, r≥1)  ✓  (equal)
------------------------------------------------------------------------

imm-A≡armA : immediate-reward-dist Playing ArmA ≡ armA
imm-A≡armA = refl

imm-B≡armB : immediate-reward-dist Playing ArmB ≡ armB
imm-B≡armB = refl

step0-fosd : immediate-reward-dist Playing ArmB FOSD≤
             immediate-reward-dist Playing ArmA
step0-fosd = bandit-fosd

------------------------------------------------------------------------
-- Depth 1: CDF equality (computational verification)
--
-- marginal-reward Playing ArmA 1 = [(1,2),(0,4),(1,1),(0,2)]
-- marginal-reward Playing ArmB 1 = [(1,1),(0,2),(1,2),(0,4)]
--
-- Different list structure but identical CDFs:
--   CDF at r=0: both give 6
--   CDF at r≥1: both give 9 (total weight)
------------------------------------------------------------------------

test-depth1-A-cdf0 : cdf-weight (marginal-reward Playing ArmA 1) 0 ≡ 6
test-depth1-A-cdf0 = refl

test-depth1-B-cdf0 : cdf-weight (marginal-reward Playing ArmB 1) 0 ≡ 6
test-depth1-B-cdf0 = refl

test-depth1-A-cdf1 : cdf-weight (marginal-reward Playing ArmA 1) 1 ≡ 9
test-depth1-A-cdf1 = refl

test-depth1-B-cdf1 : cdf-weight (marginal-reward Playing ArmB 1) 1 ≡ 9
test-depth1-B-cdf1 = refl

-- FOSD at depth 1 (both CDFs are equal: trivially satisfied)
depth1-fosd : marginal-reward Playing ArmB 1 FOSD≤
              marginal-reward Playing ArmA 1
depth1-fosd zero = ≤-refl
depth1-fosd (suc _) = ≤-refl

------------------------------------------------------------------------
-- FOSD ⟹ E[X] Bridge
------------------------------------------------------------------------

fosd-implies-ev : weighted-sum armB ≤ weighted-sum armA
fosd-implies-ev = bandit-ev

------------------------------------------------------------------------
-- FOSDCoindHomo (depth 0 only)
--
-- For a full FOSDCoindHomo with PointwiseFOSD at all depths,
-- we need a lemma: CDF distributes over monadic bind (>>=).
-- This would show that at depth n+1, both actions produce
-- marginals with identical CDFs (since both return to Playing
-- and follow the same default policy).
------------------------------------------------------------------------

-- Concrete FOSD for all action pairs at step 0:
test-BA-step0 : immediate-reward-dist Playing ArmB FOSD≤
                immediate-reward-dist Playing ArmA
test-BA-step0 = step0-fosd

test-AA-step0 : immediate-reward-dist Playing ArmA FOSD≤
                immediate-reward-dist Playing ArmA
test-AA-step0 = FOSD-refl (immediate-reward-dist Playing ArmA)

test-BB-step0 : immediate-reward-dist Playing ArmB FOSD≤
                immediate-reward-dist Playing ArmB
test-BB-step0 = FOSD-refl (immediate-reward-dist Playing ArmB)

-- Note: ArmB does NOT FOSD-dominate ArmA (CDF(ArmA,0)=1 > CDF(ArmB,0)=2
-- would require 2 ≤ 1 which fails). This confirms FOSD is asymmetric
-- for the BiasedBandit: ArmA strictly dominates ArmB.

------------------------------------------------------------------------
-- SUMMARY
--
-- FOSD infrastructure demonstrated on BiasedBandit:
--
--   1. CDF computation: verified by refl at depths 0 and 1
--   2. Immediate FOSD: ArmA dominates ArmB at step 0
--      CDF(ArmA, 0) = 1 < 2 = CDF(ArmB, 0)
--   3. Depth 1: CDFs are equal (both actions → Playing → ArmB)
--   4. FOSD ⟹ E[X]: bridge theorem gives 1 ≤ 2
--
-- Identified proof obligations for full PointwiseFOSD:
--   • CDF distributes over monadic bind:
--     cdf-weight (d >>= f) r = Σ_{(a,w) ∈ d} w * cdf-weight (f a) r
--   • CDF distributes over scale:
--     cdf-weight (scale k d) r = k * cdf-weight d r
--   These lemmas would enable proving pointwise FOSD at ALL
--   depths for stateless environments like BiasedBandit.
--
-- For the Stochastic Isomorphism Conjecture (ICLP 2027):
--   The conjecture concerns environments where the marginal
--   distributions CHANGE across timesteps. BiasedBandit has
--   identical marginals at all depths (after depth 0), making
--   the conjecture trivially satisfied. The interesting case
--   is environments with state-dependent rewards (e.g.,
--   GamblersRuin), where conditional tail distributions
--   introduce non-trivial correlations.
--
-- All --safe, no postulates.
------------------------------------------------------------------------
