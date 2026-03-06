{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Stochastic.CompositionalDemo
--
-- Compositional verification demo: BiasedBandit × CoinFlip.
--
-- An agent simultaneously operates two independent stochastic
-- environments.  In environment 1 (BiasedBandit), it chooses
-- ArmA or ArmB.  In environment 2 (CoinFlip), it chooses Flip
-- or Stay.  The Compositional Ranking Algebra automatically
-- verifies the product ranking from the individual FOSD proofs.
--
-- Exercises all six operations of the algebra:
--   1. VerifiedRanking extraction from FOSDCoindHomo
--   2. Product composition (++-product)
--   3. Hierarchy subsumption (ranking-subsumes: FOSD → SOSD → TOSD)
--   4. Scaling (scale-ranking)
--   5. Scaled product (scaled-product = scale ∘ product)
--   6. Sum composition (SumCompose.sum-ranking)
--
-- All tests pass by refl or trivial constructors.
-- All --safe, no postulates.
------------------------------------------------------------------------

module CSHRL.Tasks.Stochastic.CompositionalDemo where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import CSHRL.Probability.Finite using (Dist; scale)
open import CSHRL.Probability.FOSD using (cdf-weight)

------------------------------------------------------------------------
-- Import both environments
------------------------------------------------------------------------

import CSHRL.Tasks.Stochastic.BiasedBanditFOSD as BB
import CSHRL.Tasks.Stochastic.CoinFlipFOSD as CF

------------------------------------------------------------------------
-- Open FOSDCore for each environment (qualified)
--
-- BBCore provides marginal-reward, PointwiseFOSD, etc.
-- for the BiasedBandit (default-action = ArmB).
-- CFCore provides the same for CoinFlip (default-action = Stay).
------------------------------------------------------------------------

open import CSHRL.Core.FOSD

module BBCore = FOSDCore
  BB.State BB.Action BB.step BB.all-actions BB.ArmB

module CFCore = FOSDCore
  CF.State CF.Action CF.step-fosd CF.all-actions CF.default-action

------------------------------------------------------------------------
-- Import the Compositional Algebra
------------------------------------------------------------------------

open import CSHRL.Core.Compose

------------------------------------------------------------------------
-- 1. Extract VerifiedRankings from FOSDCoindHomo records
--
-- Since FOSD≤ = SD[0]≤ definitionally, the extraction is direct:
-- the preserves-fosd field of FOSDCoindHomo has exactly the type
-- needed by VerifiedRanking.preserves at k=0.
------------------------------------------------------------------------

bandit-verified : VerifiedRanking BB.State BB.Action BBCore.marginal-reward 0
bandit-verified = record
  { _≤ₐ_     = BB.bandit-≤ₐ
  ; preserves = BB.bandit-preserves
  }

coinflip-verified : VerifiedRanking CF.State CF.Action CFCore.marginal-reward 0
coinflip-verified = record
  { _≤ₐ_     = CF.coinflip-≤ₐ
  ; preserves = CF.coinflip-preserves
  }

------------------------------------------------------------------------
-- 2. Product Composition: BiasedBandit × CoinFlip
--
-- The "portfolio" environment has:
--   State  = BB.State × CF.State
--   Action = BB.Action × CF.Action  (4 combinations)
--   Marginal reward = bandit marginal ++ coinflip marginal
--
-- The product ranking requires BOTH components to rank favorably:
--   (a₁,a₂) ≤ (b₁,b₂)  iff  a₁ ≤₁ b₁  AND  a₂ ≤₂ b₂
------------------------------------------------------------------------

portfolio : VerifiedRanking
  (BB.State × CF.State) (BB.Action × CF.Action)
  (λ { (s₁ , s₂) (a₁ , a₂) n →
    BBCore.marginal-reward s₁ a₁ n ++ CFCore.marginal-reward s₂ a₂ n })
  0
portfolio = ++-product bandit-verified coinflip-verified

------------------------------------------------------------------------
-- 3. Hierarchy Subsumption: FOSD → SOSD → TOSD (free upgrades)
--
-- The portfolio ranking, verified at FOSD (k=0), is automatically
-- valid at every weaker SD level.  Each call to ranking-subsumes
-- moves up one level in the hierarchy.
------------------------------------------------------------------------

portfolio-sosd : VerifiedRanking
  (BB.State × CF.State) (BB.Action × CF.Action)
  (λ { (s₁ , s₂) (a₁ , a₂) n →
    BBCore.marginal-reward s₁ a₁ n ++ CFCore.marginal-reward s₂ a₂ n })
  1
portfolio-sosd = ranking-subsumes portfolio

portfolio-tosd : VerifiedRanking
  (BB.State × CF.State) (BB.Action × CF.Action)
  (λ { (s₁ , s₂) (a₁ , a₂) n →
    BBCore.marginal-reward s₁ a₁ n ++ CFCore.marginal-reward s₂ a₂ n })
  2
portfolio-tosd = ranking-subsumes portfolio-sosd

------------------------------------------------------------------------
-- 4. Scaling: Reward Amplification
--
-- Multiply all bandit rewards by 3.  The ranking is preserved.
------------------------------------------------------------------------

bandit-scaled : VerifiedRanking BB.State BB.Action
  (λ s a n → scale 3 (BBCore.marginal-reward s a n)) 0
bandit-scaled = scale-ranking 3 bandit-verified

------------------------------------------------------------------------
-- 5. Scaled Product: Compose then Scale
--
-- Compose the two environments, then amplify all rewards by 3.
-- Demonstrates composability: scaled-product = scale ∘ ++-product.
------------------------------------------------------------------------

scaled-portfolio : VerifiedRanking
  (BB.State × CF.State) (BB.Action × CF.Action)
  (λ { (s₁ , s₂) (a₁ , a₂) n →
    scale 3 (BBCore.marginal-reward s₁ a₁ n ++
             CFCore.marginal-reward s₂ a₂ n) })
  0
scaled-portfolio = scaled-product 3 bandit-verified coinflip-verified

------------------------------------------------------------------------
-- 6. Sum Composition: Phased Environment
--
-- A "phased" environment: in phase 1, the agent plays BiasedBandit;
-- in phase 2, it plays CoinFlip.  The dispatched ranking uses the
-- bandit ranking in phase 1 and the coinflip ranking in phase 2.
-- Mismatched state/action pairs are excluded by ⊥.
------------------------------------------------------------------------

open module Sum = SumCompose
  {S₁ = BB.State} {A₁ = BB.Action} {S₂ = CF.State} {A₂ = CF.Action}
  {m₁ = BBCore.marginal-reward} {m₂ = CFCore.marginal-reward} {k = 0}

phased : VerifiedRanking
  (BB.State ⊎ CF.State) (BB.Action ⊎ CF.Action)
  sum-marginal 0
phased = sum-ranking bandit-verified coinflip-verified

------------------------------------------------------------------------
-- Computational Tests: Product Ranking
------------------------------------------------------------------------

private
  portfolio-rank = VerifiedRanking._≤ₐ_ portfolio

-- (ArmB, Stay) ≤ (ArmA, Flip): both components rank favorably.
-- ArmB ≤ ArmA in bandit (⊤) and Stay ≤ Flip in coinflip (⊤).
test-best-dominates-worst :
  portfolio-rank (BB.Playing , CF.Ready) (BB.ArmB , CF.Stay) (BB.ArmA , CF.Flip)
test-best-dominates-worst = tt , tt

-- (ArmA, Stay) ≤ (ArmA, Flip): bandit is reflexive, coinflip ranks.
test-flip-beats-stay :
  portfolio-rank (BB.Playing , CF.Ready) (BB.ArmA , CF.Stay) (BB.ArmA , CF.Flip)
test-flip-beats-stay = tt , tt

-- (ArmB, Flip) ≤ (ArmA, Flip): coinflip is reflexive, bandit ranks.
test-armA-beats-armB :
  portfolio-rank (BB.Playing , CF.Ready) (BB.ArmB , CF.Flip) (BB.ArmA , CF.Flip)
test-armA-beats-armB = tt , tt

-- Reflexivity: any action pair ≤ itself.
test-refl :
  portfolio-rank (BB.Playing , CF.Ready) (BB.ArmA , CF.Flip) (BB.ArmA , CF.Flip)
test-refl = tt , tt

------------------------------------------------------------------------
-- Computational Tests: Sum (Phased) Ranking
------------------------------------------------------------------------

private
  phased-rank = VerifiedRanking._≤ₐ_ phased

-- In bandit phase: ArmB ≤ ArmA dispatches to bandit ranking.
test-phase1-rank :
  phased-rank (inj₁ BB.Playing) (inj₁ BB.ArmB) (inj₁ BB.ArmA)
test-phase1-rank = tt

-- In coinflip phase: Stay ≤ Flip dispatches to coinflip ranking.
test-phase2-rank :
  phased-rank (inj₂ CF.Ready) (inj₂ CF.Stay) (inj₂ CF.Flip)
test-phase2-rank = tt

------------------------------------------------------------------------
-- Computational Tests: Marginal Reward Shape
--
-- The product marginal at depth 0 is the concatenation of the
-- component marginals.  Verify the CDF values.
--
-- BiasedBandit ArmA depth 0: [(1,2),(0,1)]  → CDF(0)=1, CDF(1)=3
-- CoinFlip Flip depth 0:     [(1,1),(0,1)]  → CDF(0)=1, CDF(1)=2
-- Product (ArmA,Flip):       [(1,2),(0,1),(1,1),(0,1)]
--                             → CDF(0)=1+1=2, CDF(1)=3+2=5
------------------------------------------------------------------------

private
  product-marginal-0 : Dist ℕ
  product-marginal-0 =
    BBCore.marginal-reward BB.Playing BB.ArmA 0 ++
    CFCore.marginal-reward CF.Ready CF.Flip 0

test-product-cdf-0 : cdf-weight product-marginal-0 0 ≡ 2
test-product-cdf-0 = refl

test-product-cdf-1 : cdf-weight product-marginal-0 1 ≡ 5
test-product-cdf-1 = refl

-- Dominated action pair: (ArmB, Stay) at depth 0
-- BiasedBandit ArmB: [(1,1),(0,2)]  → CDF(0)=2, CDF(1)=3
-- CoinFlip Stay:     [(0,2)]        → CDF(0)=2, CDF(1)=2
-- Product:           [(1,1),(0,2),(0,2)]
--                     → CDF(0)=2+2=4, CDF(1)=3+2=5

private
  dominated-marginal-0 : Dist ℕ
  dominated-marginal-0 =
    BBCore.marginal-reward BB.Playing BB.ArmB 0 ++
    CFCore.marginal-reward CF.Ready CF.Stay 0

test-dominated-cdf-0 : cdf-weight dominated-marginal-0 0 ≡ 4
test-dominated-cdf-0 = refl

test-dominated-cdf-1 : cdf-weight dominated-marginal-0 1 ≡ 5
test-dominated-cdf-1 = refl

-- FOSD verified: CDF of (ArmA,Flip) ≤ CDF of (ArmB,Stay) at each r.
-- CDF(0): 2 ≤ 4 ✓   CDF(1): 5 ≤ 5 ✓
-- The dominated pair has more mass in the left tail, confirming
-- that (ArmA,Flip) stochastically dominates (ArmB,Stay).

test-fosd-at-0 : cdf-weight product-marginal-0 0 ≤
                 cdf-weight dominated-marginal-0 0
test-fosd-at-0 = s≤s (s≤s z≤n)

test-fosd-at-1 : cdf-weight product-marginal-0 1 ≤
                 cdf-weight dominated-marginal-0 1
test-fosd-at-1 = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))

------------------------------------------------------------------------
-- Computational Tests: Scaled Rewards
--
-- Scaling by 3 multiplies all weights by 3.
-- Product (ArmA,Flip) CDF(0) = 2 → scaled CDF(0) = 6
------------------------------------------------------------------------

private
  scaled-marginal-0 : Dist ℕ
  scaled-marginal-0 =
    scale 3 (BBCore.marginal-reward BB.Playing BB.ArmA 0 ++
             CFCore.marginal-reward CF.Ready CF.Flip 0)

test-scaled-cdf-0 : cdf-weight scaled-marginal-0 0 ≡ 6
test-scaled-cdf-0 = refl

test-scaled-cdf-1 : cdf-weight scaled-marginal-0 1 ≡ 15
test-scaled-cdf-1 = refl
