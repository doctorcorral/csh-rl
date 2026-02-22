{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Synthesis.FiniteDeterministicMDP
--
-- EC-specific synthesis for Finite Deterministic MDPs.
--
-- Instantiates the generic PredicateDSL from Synthesis.Core with
-- State as the carrier type. Provides:
--
--   - State observations (recording step transitions)
--   - RankModel: rankings as per-pair PredProg predicates on states
--   - Ranking propagation: feature-equivalent states get same ranking
--   - CoindHomo construction from verified ranking models
--   - Successor propagation: state predicates on successors
------------------------------------------------------------------------

module CSHRL.Synthesis.FiniteDeterministicMDP where

open import Data.List using (List; []; _∷_; map; length)
open import Data.Nat using (ℕ; zero; suc; _⊔_; _≤_; z≤n; s≤s)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)
open import Data.Unit using (⊤; tt)
open import Codata.Guarded.Stream using (Stream; head; tail; tabulate)
open import Function using (_∘_)
open import Relation.Nullary using (Dec; yes; no)

import CSHRL.Synthesis.Core as SynthCore

------------------------------------------------------------------------
-- The FDMDP Synthesis Module
------------------------------------------------------------------------

module FDMDPSynthesis
  (State : Set)
  (Action : Set)
  (step : State → Action → State × ℕ)
  (all-actions : List Action)
  where

  --------------------------------------------------------------------
  -- Import Core for solve, value, action-value, CoindHomo
  --------------------------------------------------------------------

  open import CSHRL.Core
  open Core State Action ℕ step _≤_ _⊔_ 0 all-actions public

  --------------------------------------------------------------------
  -- SECTION 1: STATE OBSERVATIONS
  --
  -- Records of step transitions. Richer than generic observations:
  -- the next state and reward are separated for constraint analysis.
  --------------------------------------------------------------------

  record StateObs : Set where
    constructor sobs
    field
      state  : State
      action : Action
      next   : State
      rew    : ℕ

  ObsValid : StateObs → Set
  ObsValid o = step (StateObs.state o) (StateObs.action o)
               ≡ (StateObs.next o , StateObs.rew o)

  AllObsValid : List StateObs → Set
  AllObsValid []       = ⊤
  AllObsValid (o ∷ os) = ObsValid o × AllObsValid os

  --------------------------------------------------------------------
  -- SECTION 2: STATE PREDICATES VIA PredicateDSL
  --
  -- Opens the generic PredicateDSL with State as the carrier.
  -- Features are state-component predicates:
  --   - "is-at s₀" — is the state equal to s₀?
  --   - "is-terminal" — does the state loop to itself?
  --   - "is-rewarding" — does some action give positive reward?
  --
  -- Each FDMDP instance provides its own Feature type.
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
    -- at state s (i.e., b is at least as good as a).
    --
    -- Using PredProg instead of raw functions gives us propagation:
    -- feature-equivalent states get the same ranking, automatically.
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
    -- action pair. This is the FDMDP version of the propagation
    -- theorem: one observation about ranking at state s₁ tells us
    -- the ranking at ALL feature-equivalent states s₂.
    ------------------------------------------------------------------

    rank-propagates : ∀ (m : RankModel) (s₁ s₂ : State) (a b : Action) →
      FeatureEquiv (RankModel.prefer m a b) s₁ s₂ →
      rank-eval m s₁ a b ≡ rank-eval m s₂ a b
    rank-propagates m s₁ s₂ a b =
      propagation (RankModel.prefer m a b) s₁ s₂

    rank-transfer : ∀ (m : RankModel) (s₁ s₂ : State) (a b : Action) →
      FeatureEquiv (RankModel.prefer m a b) s₁ s₂ →
      RankHolds m s₁ a b →
      RankHolds m s₂ a b
    rank-transfer m s₁ s₂ a b equiv holds =
      trans (sym (rank-propagates m s₁ s₂ a b equiv)) holds

    ------------------------------------------------------------------
    -- SECTION 4: SUCCESSOR PREDICATES
    --
    -- "Does action a from state s lead to a state satisfying p?"
    -- This connects state predicates to transition structure.
    ------------------------------------------------------------------

    leads-to : PredProg → State → Action → Bool
    leads-to p s a = eval p (proj₁ (step s a))

    gives-reward : PredProg → State → Action → Bool
    gives-reward p s a = eval p s

    -- Successor propagation: if s₁ and s₂ have feature-equivalent
    -- successors under action a, then the same successor predicates hold.
    successor-propagation : ∀ (p : PredProg) (s₁ s₂ : State) (a : Action) →
      FeatureEquiv p (proj₁ (step s₁ a)) (proj₁ (step s₂ a)) →
      leads-to p s₁ a ≡ leads-to p s₂ a
    successor-propagation p s₁ s₂ a =
      propagation p (proj₁ (step s₁ a)) (proj₁ (step s₂ a))

    ------------------------------------------------------------------
    -- SECTION 5: INTEGRATION WITH EC
    --
    -- A correct RankModel produces a valid CoindHomo.
    ------------------------------------------------------------------

    ModelPreserves : RankModel → Set
    ModelPreserves m = ∀ a b s →
      RankHolds m s a b →
      action-value s a ≤ₛ action-value s b

    module WithCorrectModel
      (m : RankModel)
      (preserves : ModelPreserves m)
      where

      instance
        SynthesizedHomo : CoindHomo
        SynthesizedHomo = record
          { _≤ₐ_ = RankHolds m
          ; preserves = preserves
          }

    ------------------------------------------------------------------
    -- SECTION 6: VERSION SPACE FOR RANKINGS
    --
    -- The set of RankModels consistent with observed preservations.
    -- Each observation constrains which ranking predicates are valid.
    ------------------------------------------------------------------

    PreservesAtState : RankModel → State → Set
    PreservesAtState m s = ∀ a b →
      RankHolds m s a b →
      action-value s a ≤ₛ action-value s b

    InRankVS : RankModel → List State → Set
    InRankVS m []       = ⊤
    InRankVS m (s ∷ ss) = PreservesAtState m s × InRankVS m ss

    -- Value coherence: feature-equiv states have same action-value ordering.
    -- This bridges ranking propagation to preservation propagation.
    ValueCoherent : State → State → Set
    ValueCoherent s₁ s₂ = ∀ a b →
      action-value s₁ a ≤ₛ action-value s₁ b →
      action-value s₂ a ≤ₛ action-value s₂ b

    -- Ranking propagation at version-space level:
    -- Preservation at s₁ + feature equivalence + value coherence
    -- → preservation at s₂
    vs-propagates : ∀ (m : RankModel) (s₁ s₂ : State) →
      ValueCoherent s₁ s₂ →
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
    -- SECTION 7: CEGIS FOR RANKING PREDICATES
    --
    -- Uses the generic CEGIS from Core to synthesize ranking
    -- predicates from trace-comparison observations.
    --
    -- For each action pair (a, b), the predicate `prefer a b`
    -- is synthesized independently: each sample (s, a, b) provides
    -- a PredObs (s, trace(a) ≤ₜ trace(b)) that refines the VS.
    --
    -- Propagation acceleration applies: feature-equivalent states
    -- eliminate the same candidates automatically.
    ------------------------------------------------------------------

    module WithCEGIS
      (all-features : List Feature)
      where

      open CEGIS all-features public

      -- Synthesize a single ranking predicate from observations
      -- Each observation (s, val) says: at state s, this predicate
      -- should evaluate to val
      synth-rank-pred : ℕ → List PredObs → Maybe PredProg
      synth-rank-pred depth obs with cegis-loop (initial-vs depth) obs
      ... | []      = nothing
      ... | (p ∷ _) = just p

      -- Remaining version space size for a ranking predicate
      rank-vs-size : ℕ → List PredObs → ℕ
      rank-vs-size depth obs = length (cegis-loop (initial-vs depth) obs)

      -- bfilter preserves membership for elements that pass the filter
      bfilter-preserves : ∀ {A : Set} (f : A → Bool) (xs : List A)
        (x : A) → x ∈ₗ xs → f x ≡ true → x ∈ₗ bfilter f xs
      bfilter-preserves f (x ∷ xs) .x here fx with f x
      ... | true  = here
      bfilter-preserves f (x ∷ xs) y (there mem) fy with f x
      ... | true  = there (bfilter-preserves f xs y mem fy)
      ... | false = bfilter-preserves f xs y mem fy

      -- Correctness: if p is in the VS and consistent with all
      -- observations, p survives the CEGIS loop
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
    -- SECTION 8: LEARNING-SYNTHESIS BRIDGE
    --
    -- Connects the learning loop (violations, samples, depth) with
    -- the synthesis loop (version spaces, observations, predicates).
    --
    -- Key bridge: each Sample at a given depth produces a ranking
    -- observation by comparing traces. This observation refines the
    -- version space for the relevant action pair.
    --
    -- The combined system converges because:
    --   1. Learning side: depth increases monotonically
    --   2. Synthesis side: VS shrinks monotonically
    --   3. Propagation: equivalent states are free (dissolution)
    ------------------------------------------------------------------

    module WithLearningBridge
      (all-features : List Feature)
      (_≟ₐ_ : (a b : Action) → Dec (a ≡ b))
      (trace-compare : State → Action → Action → ℕ → Bool)
      where

      open WithCEGIS all-features

      import CSHRL.Learning.Base as LB
      open LB.UniversalLearning State Action _≟ₐ_

      -- Convert a sample at a depth to a ranking observation
      -- trace-compare s a b k = true means a ≤ b at depth k
      sample-to-obs : ℕ → Sample → Action × Action × PredObs
      sample-to-obs k (sample s a b) =
        a , b , (s , trace-compare s a b k)

      -- Convert a violation to a negative observation
      -- Violation says: ranking said worse ≤ better but it was wrong
      -- So prefer(worse, better) should be false at the violated state
      violation-to-obs : Violation → Action × Action × PredObs
      violation-to-obs v =
        Violation.viol-worse v , Violation.viol-better v ,
        (Violation.viol-state v , false)

      -- Combined learner state
      record SynthLearnerState : Set where
        constructor synth-learner-state
        field
          learn-state  : LearnerState
          rank-vs-ab   : Action → Action → VersionSpace

      -- Initialize combined state
      init-synth-learner : ℕ → SynthLearnerState
      init-synth-learner depth = synth-learner-state
        init-learner
        (λ _ _ → initial-vs depth)

      -- Helper: update one pair's VS while leaving others unchanged
      update-rank-vs : (Action → Action → VersionSpace) →
        Action → Action → PredObs → Action → Action → VersionSpace
      update-rank-vs old-vs a b ob a' b' with a' ≟ₐ a | b' ≟ₐ b
      ... | yes _ | yes _ = refine (old-vs a' b') ob
      ... | yes _ | no  _ = old-vs a' b'
      ... | no  _ | _     = old-vs a' b'

      -- Process one sample: update both learning and synthesis state
      synth-learn-step :
        (ℕ → Sample → Maybe Violation) →
        SynthLearnerState → Sample → SynthLearnerState
      synth-learn-step test sls s = synth-learner-state new-learn new-vs
        where
          k = LearnerState.current-depth (SynthLearnerState.learn-state sls)
          new-learn = make-learner test (SynthLearnerState.learn-state sls) s
          sample-result = sample-to-obs k s
          a = proj₁ sample-result
          b = proj₁ (proj₂ sample-result)
          ob = proj₂ (proj₂ sample-result)
          new-vs = update-rank-vs (SynthLearnerState.rank-vs-ab sls) a b ob

      -- Process a batch of samples
      synth-learn-batch :
        (ℕ → Sample → Maybe Violation) →
        SynthLearnerState → List Sample → SynthLearnerState
      synth-learn-batch test sls []       = sls
      synth-learn-batch test sls (s ∷ ss) =
        synth-learn-batch test (synth-learn-step test sls s) ss

      -- Extract synthesized ranking model (if all pairs have candidates)
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

      -- VS size for a specific pair (for monitoring convergence)
      pair-vs-size : SynthLearnerState → Action → Action → ℕ
      pair-vs-size sls a b =
        length (SynthLearnerState.rank-vs-ab sls a b)

      -- Total VS size across all pairs (convergence metric)
      total-vs-size : List (Action × Action) → SynthLearnerState → ℕ
      total-vs-size [] _ = 0
      total-vs-size ((a , b) ∷ rest) sls =
        pair-vs-size sls a b + total-vs-size rest sls
        where open import Data.Nat using (_+_)

      ------------------------------------------------------------------
      -- Convergence Properties
      ------------------------------------------------------------------

      -- update-rank-vs monotonically decreases each pair's VS
      update-vs-mono : ∀ old-vs a b ob a' b' →
        length (update-rank-vs old-vs a b ob a' b') ≤
        length (old-vs a' b')
      update-vs-mono old-vs a b ob a' b' with a' ≟ₐ a | b' ≟ₐ b
      ... | yes _ | yes _ = vs-shrinks (old-vs a' b') ob
      ... | yes _ | no  _ = ≤-refl
        where open import Data.Nat.Properties using (≤-refl)
      ... | no  _ | _     = ≤-refl
        where open import Data.Nat.Properties using (≤-refl)

      -- The synthesis side monotonically shrinks: the update-rank-vs
      -- used in synth-learn-step only refines the targeted pair and
      -- leaves all others unchanged.
      SynthVSMono : Set
      SynthVSMono = ∀ (old-vs : Action → Action → VersionSpace)
                      (a b : Action) (ob : PredObs) (a' b' : Action) →
        length (update-rank-vs old-vs a b ob a' b') ≤
        length (old-vs a' b')

      synth-vs-mono : SynthVSMono
      synth-vs-mono = update-vs-mono

      -- The learning side increases depth monotonically. This follows
      -- from the structure of make-learner (curried-step), which
      -- either keeps depth the same (no violation) or increments it.
      LearnDepthMono : Set
      LearnDepthMono = ∀ test (ls : LearnerState) (s : Sample) →
        LearnerState.current-depth ls ≤
        LearnerState.current-depth (make-learner test ls s)

      -- Combined convergence guarantee (type):
      -- The combined system converges because:
      --   1. Learning depth is bounded (from Learning.Base convergence)
      --   2. Each pair's VS shrinks monotonically (synth-vs-mono)
      --   3. Both are bounded below by 0
      -- So the system reaches a fixpoint in finite steps.
      CombinedConvergence : Set
      CombinedConvergence = ∀ test sls (batch : List Sample) →
        ∀ a b →
          length (SynthLearnerState.rank-vs-ab
                   (synth-learn-batch test sls batch) a b) ≤
          length (SynthLearnerState.rank-vs-ab sls a b)
