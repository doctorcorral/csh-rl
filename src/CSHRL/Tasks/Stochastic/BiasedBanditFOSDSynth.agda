{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Stochastic.BiasedBanditFOSDSynth
--
-- FOSD-BASED SYNTHESIS OBSERVATION LAYER
--
-- Same pipeline as BiasedBanditSynth, but observations are generated
-- from FOSD comparison (fosd?) instead of expected trace comparison.
--
-- Key: PredicateDSL and CEGIS are UNCHANGED. Only the observation
-- generation differs:
--   Expected-value: (s, E[trace(a)] ≤ E[trace(b)])
--   FOSD:           (s, fosd? (marginal a) (marginal b))
--
-- For BiasedBandit at depth 0, both yield identical observations
-- (ArmB FOSD≤ ArmA and E[ArmB] ≤ E[ArmA] agree). This demonstrates
-- that the FOSD observation layer plugs into the same synthesis.
--
-- All --safe, no postulates.
------------------------------------------------------------------------

module CSHRL.Tasks.Stochastic.BiasedBanditFOSDSynth where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ)
open import Data.List using (List; _∷_; [])
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import CSHRL.Probability.Finite using (Dist; bernoulli; fmap)
open import CSHRL.Probability.FOSD using (fosd?)

------------------------------------------------------------------------
-- BiasedBandit (same as BiasedBanditSynth)
------------------------------------------------------------------------

data State : Set where
  Playing : State

data Action : Set where
  ArmA ArmB : Action

step : State → Action → Dist (State × ℕ)
step Playing ArmA = bernoulli (Playing , 1) 2 (Playing , 0) 1
step Playing ArmB = bernoulli (Playing , 1) 1 (Playing , 0) 2

-- Immediate reward distribution (depth 0)
imm-dist : State → Action → Dist ℕ
imm-dist s a = fmap proj₂ (step s a)

------------------------------------------------------------------------
-- FOSD observation layer
--
-- fosd? μ ν ≡ true means μ FOSD≤ ν (ν stochastically dominates μ).
-- For "ArmB ≤ ArmA" we want ArmB FOSD≤ ArmA, i.e. fosd? armB armA.
------------------------------------------------------------------------

fosd-compare : State → Action → Action → ℕ → Bool
fosd-compare s a b n = fosd? (imm-dist s a) (imm-dist s b)
  -- "a ≤ b" means a is dominated by b. fosd? μ ν = true iff μ FOSD≤ ν.
  -- So fosd? (marginal a) (marginal b) = true iff a FOSD≤ b, i.e. b dominates a.

obs-b≤a-fosd : List (State × Bool)
obs-b≤a-fosd = (Playing , fosd-compare Playing ArmB ArmA 0) ∷ []

obs-a≤b-fosd : List (State × Bool)
obs-a≤b-fosd = (Playing , fosd-compare Playing ArmA ArmB 0) ∷ []

-- FOSD agrees with expected-value for BiasedBandit at depth 0
test-fosd-b≤a : fosd-compare Playing ArmB ArmA 0 ≡ true
test-fosd-b≤a = refl

test-fosd-a≤b : fosd-compare Playing ArmA ArmB 0 ≡ false
test-fosd-a≤b = refl

------------------------------------------------------------------------
-- These observations feed into the same CEGIS as BiasedBanditSynth.
-- The Synthesis.StochasticFiniteMDP module would use expected-trace-compare;
-- an FOSD-synthesis variant would use fosd-compare instead.
--
-- The PredObs format (State × Bool) is identical. All propagation,
-- dissolution, and tight-bound theorems apply unchanged.
------------------------------------------------------------------------
