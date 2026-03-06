{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Synthesis.FOSDStochasticFiniteMDP
--
-- FOSD-based synthesis for Stochastic Finite MDPs.
--
-- Same structure as Synthesis.StochasticFiniteMDP, but observations
-- are generated from FOSD comparison (fosd?) instead of expected
-- trace comparison. The PredicateDSL and CEGIS are UNCHANGED.
--
-- Provides:
--   - fosd-compare: State → Action → Action → ℕ → Bool
--   - WithStateFeatures, WithCEGIS (same interface)
--   - synth-rank-pred from FOSD observations
--
-- Use: open this module with your MDP parameters, define features,
-- generate observations via fosd-compare, run CEGIS.
------------------------------------------------------------------------

module CSHRL.Synthesis.FOSDStochasticFiniteMDP where

open import Data.List using (List; []; _∷_; map; length)
open import Data.Nat using (ℕ; zero; suc; _⊔_; _≤_; z≤n; s≤s; _+_; _*_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
open import Relation.Nullary using (Dec; yes; no)

open import CSHRL.Probability.Finite using (Dist; _>>=_; fmap)
open import CSHRL.Probability.FOSD using (fosd?)

import CSHRL.Synthesis.Core as SynthCore

------------------------------------------------------------------------
-- FOSD Stochastic Synthesis Module
------------------------------------------------------------------------

module SFDMDPSynthesisFOSD
  (State Action : Set)
  (step : State → Action → Dist (State × ℕ))
  (all-actions : List Action)
  (default-action : Action)
  where

  --------------------------------------------------------------------
  -- Import FOSDCore for marginal-reward
  --------------------------------------------------------------------

  open import CSHRL.Core.FOSD
  open FOSDCore State Action step all-actions default-action
    using (marginal-reward; immediate-reward-dist; PointwiseFOSD; FOSDCoindHomo)

  --------------------------------------------------------------------
  -- FOSD observation layer
  --
  -- fosd-compare s a b n = true iff a FOSD≤ b at depth n
  -- (i.e. b dominates a, so "a ≤ b" in the ranking)
  --------------------------------------------------------------------

  fosd-compare : State → Action → Action → ℕ → Bool
  fosd-compare s a b n = fosd? (marginal-reward s a n) (marginal-reward s b n)

  --------------------------------------------------------------------
  -- State predicates via PredicateDSL (same as StochasticFiniteMDP)
  --------------------------------------------------------------------

  module WithStateFeatures
    (Feature : Set)
    (eval-feature : Feature → State → Bool)
    where

    open SynthCore.PredicateDSL State Feature eval-feature public

    ------------------------------------------------------------------
    -- RankModel (same structure)
    ------------------------------------------------------------------

    record RankModel : Set where
      field
        prefer : Action → Action → PredProg

    rank-eval : RankModel → State → Action → Action → Bool
    rank-eval m s a b = eval (RankModel.prefer m a b) s

    RankHolds : RankModel → State → Action → Action → Set
    RankHolds m s a b = rank-eval m s a b ≡ true

    rank-propagates : ∀ (m : RankModel) (s₁ s₂ : State) (a b : Action) →
      FeatureEquiv (RankModel.prefer m a b) s₁ s₂ →
      rank-eval m s₁ a b ≡ rank-eval m s₂ a b
    rank-propagates m s₁ s₂ a b = propagation (RankModel.prefer m a b) s₁ s₂

    ------------------------------------------------------------------
    -- Integration with FOSD EC
    --
    -- A correct RankModel produces a valid FOSDCoindHomo.
    -- RankHolds m s a b means "a ≤ b" (b preferred). Preservation:
    -- when a ≤ b, the preferred action b must dominate a, i.e. PointwiseFOSD s b a.
    ------------------------------------------------------------------

    ModelPreservesFOSD : RankModel → Set
    ModelPreservesFOSD m = ∀ a b s →
      RankHolds m s a b → PointwiseFOSD s b a

    module WithCorrectModel
      (m : RankModel)
      (preserves : ModelPreservesFOSD m)
      where

      instance
        SynthesizedFOSDHomo : FOSDCoindHomo
        SynthesizedFOSDHomo = record
          { _≤ₐ_ = RankHolds m
          ; preserves-fosd = preserves
          }

    ------------------------------------------------------------------
    -- CEGIS for ranking predicates (FOSD observations)
    ------------------------------------------------------------------

    module WithCEGIS
      (all-features : List Feature)
      where

      open CEGIS all-features public

      synth-rank-pred : ℕ → List PredObs → Maybe PredProg
      synth-rank-pred depth obs with cegis-loop (initial-vs depth) obs
      ... | []      = nothing
      ... | (p ∷ _) = just p

      rank-vs-size : ℕ → List PredObs → ℕ
      rank-vs-size depth obs = length (cegis-loop (initial-vs depth) obs)

    ------------------------------------------------------------------
    -- Learning Bridge for FOSD
    --
    -- Connects the learning loop with FOSD synthesis. Samples are
    -- converted to ranking observations via fosd-compare (instead of
    -- expected-trace-compare). Same structure as StochasticFiniteMDP.
    ------------------------------------------------------------------

    module WithLearningBridge
      (all-features : List Feature)
      (_≟ₐ_ : (a b : Action) → Dec (a ≡ b))
      where

      open WithCEGIS all-features

      import CSHRL.Learning.Base as LB
      open LB.UniversalLearning State Action _≟ₐ_

      -- Convert a sample to a ranking observation using FOSD
      sample-to-obs : ℕ → Sample → Action × Action × PredObs
      sample-to-obs k (sample s a b) =
        a , b , (s , fosd-compare s a b k)

      violation-to-obs : Violation → Action × Action × PredObs
      violation-to-obs v =
        Violation.viol-worse v , Violation.viol-better v ,
        (Violation.viol-state v , false)

      -- Combined learner state (mirrors StochasticFiniteMDP bridge)
      record SynthLearnerState : Set where
        constructor synth-learner-state
        field
          learn-state  : LearnerState
          rank-vs-ab   : Action → Action → VersionSpace

      init-synth-learner : ℕ → SynthLearnerState
      init-synth-learner depth = synth-learner-state
        init-learner
        (λ _ _ → initial-vs depth)

      update-rank-vs : (Action → Action → VersionSpace) →
        Action → Action → PredObs →
        Action → Action → VersionSpace
      update-rank-vs old-vs a b ob a' b' with a' ≟ₐ a | b' ≟ₐ b
      ... | yes _ | yes _ = refine (old-vs a' b') ob
      ... | yes _ | no  _ = old-vs a' b'
      ... | no  _ | _     = old-vs a' b'

      synth-learn-step :
        (ℕ → Sample → Maybe Violation) →
        SynthLearnerState → Sample → SynthLearnerState
      synth-learn-step test sls s = synth-learner-state new-learn new-vs
        where
          k = LearnerState.current-depth
                (SynthLearnerState.learn-state sls)
          new-learn = make-learner test
                        (SynthLearnerState.learn-state sls) s
          sample-result = sample-to-obs k s
          a = proj₁ sample-result
          b = proj₁ (proj₂ sample-result)
          ob = proj₂ (proj₂ sample-result)
          new-vs = update-rank-vs
                     (SynthLearnerState.rank-vs-ab sls) a b ob

      synth-learn-batch :
        (ℕ → Sample → Maybe Violation) →
        SynthLearnerState → List Sample → SynthLearnerState
      synth-learn-batch test sls []       = sls
      synth-learn-batch test sls (s ∷ ss) =
        synth-learn-batch test (synth-learn-step test sls s) ss

      extract-rank-model :
        List (Action × Action) →
        SynthLearnerState → Maybe RankModel
      extract-rank-model pairs sls = build-model pairs
        where
          build-model : List (Action × Action) → Maybe RankModel
          build-model [] = just (record { prefer = λ _ _ → truep })
          build-model ((a , b) ∷ rest) with
            SynthLearnerState.rank-vs-ab sls a b
          ... | []      = nothing
          ... | (p ∷ _) with build-model rest
          ...   | nothing = nothing
          ...   | just m  = just (record
            { prefer = λ a' b' →
                case (a' ≟ₐ a , b' ≟ₐ b) of λ where
                  (yes _ , yes _) → p
                  _               → RankModel.prefer m a' b' })
            where
              case_of_ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} →
                A → (A → B) → B
              case x of f = f x

      pair-vs-size : SynthLearnerState → Action → Action → ℕ
      pair-vs-size sls a b =
        length (SynthLearnerState.rank-vs-ab sls a b)

      total-vs-size : List (Action × Action) →
        SynthLearnerState → ℕ
      total-vs-size [] _ = 0
      total-vs-size ((a , b) ∷ rest) sls =
        pair-vs-size sls a b + total-vs-size rest sls

      ------------------------------------------------------------------
      -- Convergence Properties
      ------------------------------------------------------------------

      update-vs-mono : ∀ old-vs a b ob a' b' →
        length (update-rank-vs old-vs a b ob a' b') ≤
        length (old-vs a' b')
      update-vs-mono old-vs a b ob a' b' with a' ≟ₐ a | b' ≟ₐ b
      ... | yes _ | yes _ = vs-shrinks (old-vs a' b') ob
      ... | yes _ | no  _ = ≤-refl
      ... | no  _ | _     = ≤-refl

      SynthVSMono : Set
      SynthVSMono = ∀ (old-vs : Action → Action → VersionSpace)
                      (a b : Action) (ob : PredObs)
                      (a' b' : Action) →
        length (update-rank-vs old-vs a b ob a' b') ≤
        length (old-vs a' b')

      synth-vs-mono : SynthVSMono
      synth-vs-mono = update-vs-mono

      CombinedConvergence : Set
      CombinedConvergence = ∀ test sls (batch : List Sample) →
        ∀ a b →
          length (SynthLearnerState.rank-vs-ab
                   (synth-learn-batch test sls batch) a b) ≤
          length (SynthLearnerState.rank-vs-ab sls a b)

      combined-convergence : CombinedConvergence
      combined-convergence test sls []       a b = ≤-refl
      combined-convergence test sls (s ∷ ss) a b =
        ≤-trans
          (combined-convergence test (synth-learn-step test sls s) ss a b)
          (update-vs-mono (SynthLearnerState.rank-vs-ab sls)
            sa sb ob a b)
        where
          k  = LearnerState.current-depth
                 (SynthLearnerState.learn-state sls)
          so = sample-to-obs k s
          sa = proj₁ so
          sb = proj₁ (proj₂ so)
          ob = proj₂ (proj₂ so)
          ≤-trans : ∀ {a b c : ℕ} → a ≤ b → b ≤ c → a ≤ c
          ≤-trans z≤n     _       = z≤n
          ≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)
