{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Synthesis.StochasticFiniteMDP
--
-- EC-specific synthesis for Stochastic Finite MDPs.
--
-- Instantiates the generic PredicateDSL from Synthesis.Core with
-- State as the carrier type, connecting to stochastic transitions.
--
-- Key insight: the PredicateDSL and CEGIS infrastructure is GENERIC
-- over the carrier type. All propagation, dissolution, sufficiency,
-- online synthesis, and tight-bound theorems apply UNCHANGED.
-- Only the observation layer differs: expected trace comparison
-- replaces deterministic trace comparison.
--
-- Provides:
--   - State observations (recording stochastic transitions)
--   - RankModel: rankings as per-pair PredProg predicates on states
--   - Ranking propagation via FeatureEquiv (inherited from generic DSL)
--   - StochasticCoindHomo construction from verified ranking models
--   - Expected trace-based CEGIS observations
--   - Learning-synthesis bridge for stochastic feedback
------------------------------------------------------------------------

module CSHRL.Synthesis.StochasticFiniteMDP where

open import Data.List using (List; []; _∷_; map; length)
open import Data.Nat using (ℕ; zero; suc; _⊔_; _≤_; z≤n; s≤s; _+_; _*_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
open import Relation.Nullary using (Dec; yes; no)

open import CSHRL.Probability.Finite using (Dist; pure; _>>=_; fmap)

import CSHRL.Synthesis.Core as SynthCore

------------------------------------------------------------------------
-- The Stochastic FDMDP Synthesis Module
------------------------------------------------------------------------

module SFDMDPSynthesis
  (State : Set)
  (Action : Set)
  (Reward : Set)

  -- Stochastic step: returns distribution over (State × Reward)
  (step : State → Action → Dist (State × Reward))

  -- Reward ordering
  (_≤ᵣ_ : Reward → Reward → Set)
  (_≤?_ : (r s : Reward) → Dec (r ≤ᵣ s))
  (≤ᵣ-refl : ∀ {r} → r ≤ᵣ r)

  -- Reward arithmetic (for expected values)
  (_+ᵣ_ : Reward → Reward → Reward)
  (_*ᵣ_ : ℕ → Reward → Reward)
  (zeroᵣ : Reward)

  -- Supremum
  (max : Reward → Reward → Reward)
  (bottom : Reward)

  -- Finiteness
  (all-actions : List Action)
  (default-action : Action)
  (horizon : ℕ)
  where

  --------------------------------------------------------------------
  -- Import Stochastic EC (expected traces, ranking, CoindHomo)
  --------------------------------------------------------------------

  open import CSHRL.EnvironmentClass.StochasticFiniteMDP
  open StochasticFiniteMDP
    State Action Reward step
    _≤ᵣ_ _≤?_ ≤ᵣ-refl max bottom
    _+ᵣ_ _*ᵣ_ zeroᵣ
    all-actions default-action horizon
    public

  --------------------------------------------------------------------
  -- SECTION 1: STATE OBSERVATIONS
  --
  -- Records of stochastic transitions. The key difference from the
  -- deterministic case: next state and reward are drawn from a
  -- distribution. Observations record specific realizations.
  --------------------------------------------------------------------

  record StateObs : Set where
    constructor sobs
    field
      state  : State
      action : Action

  -- An observation is valid if it refers to a valid state-action pair
  -- (For stochastic MDPs, we don't record the outcome — the expected
  -- trace is computed from the step distribution.)

  --------------------------------------------------------------------
  -- SECTION 2: STATE PREDICATES VIA PredicateDSL
  --
  -- Opens the generic PredicateDSL with State as the carrier.
  -- ALL generic theorems (propagation, dissolution, sufficiency,
  -- online synthesis, tight bound) apply immediately.
  --
  -- This is the key modularity result: the synthesis theory is
  -- INDEPENDENT of whether transitions are deterministic or
  -- stochastic. The PredicateDSL operates on states, not on
  -- transitions.
  --------------------------------------------------------------------

  module WithStateFeatures
    (Feature : Set)
    (eval-feature : Feature → State → Bool)
    where

    open SynthCore.PredicateDSL State Feature eval-feature public

    ------------------------------------------------------------------
    -- SECTION 3: RANKING MODELS
    --
    -- A RankModel assigns a PredProg per action pair.
    -- "eval (prefer m a b) s = true" means action a is ranked ≤ b
    -- at state s (b is at least as good as a).
    --
    -- The ranking is synthesized from expected trace comparisons,
    -- but the model itself is a pure predicate on states.
    ------------------------------------------------------------------

    record RankModel : Set where
      field
        prefer : Action → Action → PredProg

    rank-eval : RankModel → State → Action → Action → Bool
    rank-eval m s a b = eval (RankModel.prefer m a b) s

    RankHolds : RankModel → State → Action → Action → Set
    RankHolds m s a b = rank-eval m s a b ≡ true

    ------------------------------------------------------------------
    -- RANKING PROPAGATION
    --
    -- Feature-equivalent states get the same ranking for every
    -- action pair. This inherits directly from the generic
    -- Propagation Theorem — stochastic transitions are irrelevant.
    ------------------------------------------------------------------

    rank-propagates : ∀ (m : RankModel) (s₁ s₂ : State)
      (a b : Action) →
      FeatureEquiv (RankModel.prefer m a b) s₁ s₂ →
      rank-eval m s₁ a b ≡ rank-eval m s₂ a b
    rank-propagates m s₁ s₂ a b =
      propagation (RankModel.prefer m a b) s₁ s₂

    rank-transfer : ∀ (m : RankModel) (s₁ s₂ : State)
      (a b : Action) →
      FeatureEquiv (RankModel.prefer m a b) s₁ s₂ →
      RankHolds m s₁ a b →
      RankHolds m s₂ a b
    rank-transfer m s₁ s₂ a b equiv holds =
      trans (sym (rank-propagates m s₁ s₂ a b equiv)) holds

    ------------------------------------------------------------------
    -- SECTION 4: INTEGRATION WITH STOCHASTIC EC
    --
    -- A correct RankModel produces a valid StochasticCoindHomo.
    -- The preservation condition uses lexicographic stream dominance
    -- on expected action-values.
    ------------------------------------------------------------------

    ModelPreservesLex : RankModel → Set
    ModelPreservesLex m = ∀ a b s →
      RankHolds m s a b →
      expected-action-value s a ≤ₛ-lex expected-action-value s b

    module WithCorrectModel
      (m : RankModel)
      (preserves : ModelPreservesLex m)
      where

      instance
        SynthesizedStochasticHomo : StochasticCoindHomo
        SynthesizedStochasticHomo = record
          { _≤ₐ_ = RankHolds m
          ; preserves = preserves
          }

    ------------------------------------------------------------------
    -- SECTION 5: VERSION SPACE FOR RANKINGS
    --
    -- The set of RankModels consistent with observed trace orderings.
    ------------------------------------------------------------------

    PreservesAtState : RankModel → State → Set
    PreservesAtState m s = ∀ a b →
      RankHolds m s a b →
      expected-action-value s a ≤ₛ-lex expected-action-value s b

    InRankVS : RankModel → List State → Set
    InRankVS m []       = ⊤
    InRankVS m (s ∷ ss) = PreservesAtState m s × InRankVS m ss

    ExpectedValueCoherent : State → State → Set
    ExpectedValueCoherent s₁ s₂ = ∀ a b →
      expected-action-value s₁ a ≤ₛ-lex expected-action-value s₁ b →
      expected-action-value s₂ a ≤ₛ-lex expected-action-value s₂ b

    vs-propagates : ∀ (m : RankModel) (s₁ s₂ : State) →
      ExpectedValueCoherent s₁ s₂ →
      (∀ a b → FeatureEquiv (RankModel.prefer m a b) s₁ s₂) →
      PreservesAtState m s₁ →
      PreservesAtState m s₂
    vs-propagates m s₁ s₂ coherent all-equiv pres₁ a b rank-s₂ =
      let rank-s₁ = rank-transfer m s₂ s₁ a b
                       (feat-equiv-sym (RankModel.prefer m a b) s₁ s₂
                         (all-equiv a b))
                       rank-s₂
      in coherent a b (pres₁ a b rank-s₁)

    ------------------------------------------------------------------
    -- SECTION 6: CEGIS FOR RANKING PREDICATES
    --
    -- Uses the generic CEGIS from Core to synthesize ranking
    -- predicates from expected trace-comparison observations.
    --
    -- The observations come from comparing expected traces:
    --   expected-trace-action s a k ≤ₜᵇ expected-trace-action s b k
    --
    -- All generic CEGIS properties transfer immediately:
    --   - Monotonic convergence
    --   - Propagation acceleration
    --   - Dissolution
    --   - Feature sufficiency
    --   - Online synthesis (order independence)
    --   - Tight sample complexity bound
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
      rank-vs-size depth obs =
        length (cegis-loop (initial-vs depth) obs)

      bfilter-preserves : ∀ {A : Set} (f : A → Bool) (xs : List A)
        (x : A) → x ∈ₗ xs → f x ≡ true → x ∈ₗ bfilter f xs
      bfilter-preserves f (x ∷ xs) .x here fx with f x
      ... | true  = here
      bfilter-preserves f (x ∷ xs) y (there mem) fy with f x
      ... | true  = there (bfilter-preserves f xs y mem fy)
      ... | false = bfilter-preserves f xs y mem fy

      rank-synth-sound : ∀ (p : PredProg) (vs : VersionSpace)
        (obs : List PredObs) →
        p ∈ₗ vs →
        (∀ ob → ob ∈ₗ obs → eval p (proj₁ ob) ≡ proj₂ ob) →
        p ∈ₗ cegis-loop vs obs
      rank-synth-sound p vs [] p-in _ = p-in
      rank-synth-sound p vs (ob ∷ obs) p-in all-ok =
        rank-synth-sound p (refine vs ob) obs
          (bfilter-preserves (λ q → consistent q ob) vs p p-in
            (consistent-correct p (proj₁ ob) (proj₂ ob) (all-ok ob here)))
          (λ ob' mem → all-ok ob' (there mem))

    ------------------------------------------------------------------
    -- SECTION 7: LEARNING-SYNTHESIS BRIDGE
    --
    -- Connects the stochastic learning loop with the synthesis loop.
    --
    -- Key bridge: each Sample at a given depth produces a ranking
    -- observation by comparing EXPECTED traces. This observation
    -- refines the version space for the relevant action pair.
    --
    -- The combined system inherits all generic bridge properties:
    --   - bridge-is-cegis: bridge ≡ standard CEGIS
    --   - bridge-mono: VS shrinks monotonically
    --   - bridge-sufficient: learning convergence → synthesis correctness
    --   - bridge-commutes: feedback order doesn't matter
    --   - bridge-replay: repeated feedback is no-op
    ------------------------------------------------------------------

    module WithLearningBridge
      (all-features : List Feature)
      (_≟ₐ_ : (a b : Action) → Dec (a ≡ b))
      where

      open WithCEGIS all-features

      import CSHRL.Learning.Base as LB
      open LB.UniversalLearning State Action _≟ₐ_

      -- Convert a sample to a ranking observation using EXPECTED traces
      expected-trace-compare : State → Action → Action → ℕ → Bool
      expected-trace-compare s a b k =
        expected-trace-action s a k ≤ₜᵇ expected-trace-action s b k

      sample-to-obs : ℕ → Sample → Action × Action × PredObs
      sample-to-obs k (sample s a b) =
        a , b , (s , expected-trace-compare s a b k)

      violation-to-obs : Violation → Action × Action × PredObs
      violation-to-obs v =
        Violation.viol-worse v , Violation.viol-better v ,
        (Violation.viol-state v , false)

      -- Combined learner state (mirrors deterministic bridge)
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
