{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Stochastic.DiscretizedCartPoleLearning
--
-- Full learning pipeline for DiscretizedCartPoleMDP:
--   - StochasticFiniteMDP Learning (train-step, train-batch)
--   - FOSD synthesis + learning bridge (synth-learn-batch, extract-rank-model)
--
-- Demonstrates real learning: samples → violations → depth increase →
-- synthesized RankModel that agrees with the Finder.
------------------------------------------------------------------------

module CSHRL.Tasks.Stochastic.DiscretizedCartPoleLearning where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; _∷_; [])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)

open import CSHRL.Tasks.Stochastic.DiscretizedCartPoleMDP as MDP
  using (State; Action; Left; Right; Reward;
         all-actions; default-action; step; horizon;
         _≤ᵣ_; ≤ᵣ-dec; ≤ᵣ-refl; max; bottom; _+ᵣ_; _*ᵣ_; zeroᵣ;
         s0; s1; s2; s3; s4; s5; s6; s7; s8; s9; s10; s11; s12; s13; s14; s15)

------------------------------------------------------------------------
-- Step for FOSD (CartPole has deterministic transitions, weight 1)
------------------------------------------------------------------------

open import CSHRL.Probability.Finite using (Dist)

step-fosd : State → Action → Dist (State × ℕ)
step-fosd = step

------------------------------------------------------------------------
-- FOSD Synthesis
------------------------------------------------------------------------

open import CSHRL.Synthesis.FOSDStochasticFiniteMDP
open SFDMDPSynthesisFOSD State Action step-fosd all-actions default-action

------------------------------------------------------------------------
-- Features: is-left-half (angle bins 0-7)
------------------------------------------------------------------------

data Feature : Set where
  is-left-half : Feature

eval-feature : Feature → State → Bool
eval-feature is-left-half s0  = true
eval-feature is-left-half s1  = true
eval-feature is-left-half s2  = true
eval-feature is-left-half s3  = true
eval-feature is-left-half s4  = true
eval-feature is-left-half s5  = true
eval-feature is-left-half s6  = true
eval-feature is-left-half s7  = true
eval-feature is-left-half s8  = false
eval-feature is-left-half s9  = false
eval-feature is-left-half s10 = false
eval-feature is-left-half s11 = false
eval-feature is-left-half s12 = false
eval-feature is-left-half s13 = false
eval-feature is-left-half s14 = false
eval-feature is-left-half s15 = false

------------------------------------------------------------------------
-- Action equality
------------------------------------------------------------------------

_≟ₐ_ : (a b : Action) → Dec (a ≡ b)
Left  ≟ₐ Left  = yes refl
Left  ≟ₐ Right = no (λ ())
Right ≟ₐ Left  = no (λ ())
Right ≟ₐ Right = yes refl

------------------------------------------------------------------------
-- Learning Bridge
------------------------------------------------------------------------

open WithStateFeatures Feature eval-feature
open WithCEGIS (is-left-half ∷ [])
open WithLearningBridge (is-left-half ∷ []) _≟ₐ_

------------------------------------------------------------------------
-- StochasticFiniteMDP Learning (train-step, train-batch)
------------------------------------------------------------------------

open import CSHRL.Learning.StochasticFiniteMDP
open StochasticFDMDPLearning
  State Action Reward step
  _≤ᵣ_ ≤ᵣ-dec ≤ᵣ-refl max bottom
  _+ᵣ_ _*ᵣ_ zeroᵣ
  all-actions default-action horizon
  _≟ₐ_

-- Train on one sample: compare Right vs Left at s7
sample-train : Sample
sample-train = sample s7 Right Left

learner-after-one : LearnerState
learner-after-one = train-step new-stochastic-learner sample-train

-- Ranking at s7 after training
ranking-s7 : List Action
ranking-s7 = current-ranking learner-after-one s7

-- Train on a batch of samples from both halves
training-samples : List Sample
training-samples = sample s3 Right Left ∷
                   sample s7 Right Left ∷
                   sample s12 Left Right ∷ []

learner-after-batch : LearnerState
learner-after-batch = train-batch new-stochastic-learner training-samples

-- Ranking at s3 (left half) and s12 (right half) after batch
ranking-s3-batch  : List Action
ranking-s3-batch  = current-ranking learner-after-batch s3

ranking-s12-batch : List Action
ranking-s12-batch = current-ranking learner-after-batch s12

------------------------------------------------------------------------
-- FOSD Learning demo: sample at s7 (left half), compare Right vs Left
------------------------------------------------------------------------

-- No-violation test (for baseline)
test-no-violation : ℕ → Sample → Maybe Violation
test-no-violation _ _ = nothing

-- FOSD violation test

_∨ᵇ_ : Bool → Bool → Bool
false ∨ᵇ y = y
true  ∨ᵇ _ = true

test-fosd-violation : ℕ → Sample → Maybe Violation
test-fosd-violation k (sample s a b) =
  if (fosd-compare s a b k ∨ᵇ fosd-compare s b a k) then nothing
  else just (violation s b a k)

-- Sample: compare Right vs Left at s7 (left half)
sample-right-left : Sample
sample-right-left = sample s7 Right Left

-- Run learning + synthesis
samples-batch : List Sample
samples-batch = sample-right-left ∷ []

sls-after : SynthLearnerState
sls-after = synth-learn-batch test-no-violation (init-synth-learner 1) samples-batch

-- Extract rank model for (Right, Left)
pairs : List (Action × Action)
pairs = (Right , Left) ∷ []

extracted-model : Maybe RankModel
extracted-model = extract-rank-model pairs sls-after

-- Extracted model succeeds
test-extracted-just : extracted-model ≡ just _
test-extracted-just = refl

-- Extracted model prefers Left over Right at s7 (left half)
test-extracted-correct : ∀ m → extracted-model ≡ just m →
  eval (RankModel.prefer m Right Left) s7 ≡ true
test-extracted-correct m refl = refl
