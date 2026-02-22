{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Synthesis.CombinatorialPlacementMDP
--
-- EC-specific synthesis for Combinatorial Placement MDPs.
--
-- Instantiates the generic PredicateDSL from Synthesis.Core with
-- Config as the carrier type. Adds placement-specific structure:
--
--   - PlacementObs with Outcome classification (dead/solved/ongoing)
--   - SynthModel: synthesized is-dead and is-solved predicates
--   - Outcome constraint propagation for placement dynamics
--   - Step classification propagation
--   - Integration with the EC via WithTruePredicates
--   - Version space for placement models
------------------------------------------------------------------------

module CSHRL.Synthesis.CombinatorialPlacementMDP where

open import Data.List using (List; []; _∷_; map; foldr; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _⊔_; _≤_; z≤n; s≤s)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_; not)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Codata.Guarded.Stream using (Stream; head; tail; tabulate)
open import Function using (_∘_)

import CSHRL.Synthesis.Core as SynthCore

------------------------------------------------------------------------
-- The Placement Synthesis Module
------------------------------------------------------------------------

module PlacementSynthesis
  (Config : Set)
  (Action : Set)
  (place : Config → Action → Config)
  (solved-reward : ℕ)
  (all-actions : List Action)
  (default-action : Action)
  (horizon : ℕ)
  where

  --------------------------------------------------------------------
  -- State (structural, independent of predicates)
  --------------------------------------------------------------------

  data State : Set where
    Ongoing : Config → State
    Dead    : State
    Solved  : Config → State

  make-step : (Config → Bool) → (Config → Bool) →
    State → Action → State × ℕ
  make-step _       _          Dead       _ = (Dead , 0)
  make-step _       _          (Solved c) _ = (Solved c , solved-reward)
  make-step is-dead is-solved  (Ongoing c) a =
    let c' = place c a
    in if is-dead c' then (Dead , 0)
       else if is-solved c' then (Solved c' , solved-reward)
       else (Ongoing c' , 0)

  --------------------------------------------------------------------
  -- SECTION 1: PLACEMENT OBSERVATIONS
  --------------------------------------------------------------------

  data Outcome : Set where
    dead    : Outcome
    solved  : Outcome
    ongoing : Outcome

  record PlacementObs : Set where
    constructor pobs
    field
      config  : Config
      action  : Action
      result  : Config
      outcome : Outcome

  OutcomeConstraint : (Config → Bool) → (Config → Bool) →
    Config → Outcome → Set
  OutcomeConstraint is-dead is-solved c dead    = is-dead c ≡ true
  OutcomeConstraint is-dead is-solved c solved  =
    is-dead c ≡ false × is-solved c ≡ true
  OutcomeConstraint is-dead is-solved c ongoing =
    is-dead c ≡ false × is-solved c ≡ false

  ObsConsistent : (Config → Bool) → (Config → Bool) →
    PlacementObs → Set
  ObsConsistent is-dead is-solved o =
    place (PlacementObs.config o) (PlacementObs.action o)
      ≡ PlacementObs.result o
    × OutcomeConstraint is-dead is-solved
        (PlacementObs.result o) (PlacementObs.outcome o)

  AllObsConsistent : (Config → Bool) → (Config → Bool) →
    List PlacementObs → Set
  AllObsConsistent d s []       = ⊤
  AllObsConsistent d s (o ∷ os) =
    ObsConsistent d s o × AllObsConsistent d s os

  --------------------------------------------------------------------
  -- SECTION 2: EC-SPECIFIC DSL INSTANTIATION
  --
  -- Opens the generic PredicateDSL from Synthesis.Core with
  -- Config as the carrier type. The Feature type and eval-feature
  -- are provided by the caller (e.g., QFeature for Queens).
  --------------------------------------------------------------------

  module WithDSL
    (Feature : Set)
    (eval-feature : Feature → Config → Bool)
    where

    open SynthCore.PredicateDSL Config Feature eval-feature public

    ------------------------------------------------------------------
    -- SECTION 3: SYNTHESIZED MODELS
    ------------------------------------------------------------------

    record SynthModel : Set where
      field
        dead-pred   : PredProg
        solved-pred : PredProg

    synth-is-dead : SynthModel → Config → Bool
    synth-is-dead m = eval (SynthModel.dead-pred m)

    synth-is-solved : SynthModel → Config → Bool
    synth-is-solved m = eval (SynthModel.solved-pred m)

    synth-step : SynthModel → State → Action → State × ℕ
    synth-step m = make-step (synth-is-dead m) (synth-is-solved m)

    ------------------------------------------------------------------
    -- SECTION 4: OBSERVATION-DRIVEN CONSTRAINT PROPAGATION
    ------------------------------------------------------------------

    dead-propagates : ∀ (m : SynthModel) (c₁ c₂ : Config) →
      FeatureEquiv (SynthModel.dead-pred m) c₁ c₂ →
      synth-is-dead m c₁ ≡ true →
      synth-is-dead m c₂ ≡ true
    dead-propagates m c₁ c₂ equiv obs =
      trans (sym (propagation (SynthModel.dead-pred m) c₁ c₂ equiv)) obs

    solved-propagates : ∀ (m : SynthModel) (c₁ c₂ : Config) →
      FeatureEquiv (SynthModel.solved-pred m) c₁ c₂ →
      synth-is-solved m c₁ ≡ true →
      synth-is-solved m c₂ ≡ true
    solved-propagates m c₁ c₂ equiv obs =
      trans (sym (propagation (SynthModel.solved-pred m) c₁ c₂ equiv)) obs

    ongoing-propagates : ∀ (m : SynthModel) (c₁ c₂ : Config) →
      FeatureEquiv (SynthModel.dead-pred m) c₁ c₂ →
      FeatureEquiv (SynthModel.solved-pred m) c₁ c₂ →
      synth-is-dead m c₁ ≡ false →
      synth-is-solved m c₁ ≡ false →
      synth-is-dead m c₂ ≡ false × synth-is-solved m c₂ ≡ false
    ongoing-propagates m c₁ c₂ d-eq s-eq d-f s-f =
      trans (sym (propagation (SynthModel.dead-pred m) c₁ c₂ d-eq)) d-f ,
      trans (sym (propagation (SynthModel.solved-pred m) c₁ c₂ s-eq)) s-f

    classify : State × ℕ → Outcome
    classify (Dead , _)      = dead
    classify (Solved _ , _)  = solved
    classify (Ongoing _ , _) = ongoing

    reward : State × ℕ → ℕ
    reward (_ , r) = r

    step-classification-propagates :
      ∀ (m : SynthModel) (c₁ c₂ : Config) (a : Action) →
      FeatureEquiv (SynthModel.dead-pred m) (place c₁ a) (place c₂ a) →
      FeatureEquiv (SynthModel.solved-pred m) (place c₁ a) (place c₂ a) →
      classify (synth-step m (Ongoing c₁) a)
        ≡ classify (synth-step m (Ongoing c₂) a)
      × reward (synth-step m (Ongoing c₁) a)
        ≡ reward (synth-step m (Ongoing c₂) a)
    step-classification-propagates m c₁ c₂ a d-eq s-eq
      with eval (SynthModel.dead-pred m) (place c₁ a)
         | propagation (SynthModel.dead-pred m)
             (place c₁ a) (place c₂ a) d-eq
    ... | true  | d-prop rewrite sym d-prop = refl , refl
    ... | false | d-prop rewrite sym d-prop
      with eval (SynthModel.solved-pred m) (place c₁ a)
         | propagation (SynthModel.solved-pred m)
             (place c₁ a) (place c₂ a) s-eq
    ...   | true  | s-prop rewrite sym s-prop = refl , refl
    ...   | false | s-prop rewrite sym s-prop = refl , refl

    ------------------------------------------------------------------
    -- Model consistency with observations
    ------------------------------------------------------------------

    ModelConsistent : SynthModel → PlacementObs → Set
    ModelConsistent m = ObsConsistent (synth-is-dead m) (synth-is-solved m)

    AllModelConsistent : SynthModel → List PlacementObs → Set
    AllModelConsistent m = AllObsConsistent (synth-is-dead m) (synth-is-solved m)

    ------------------------------------------------------------------
    -- OBSERVATION CONSTRAINT PROPAGATION
    ------------------------------------------------------------------

    obs-constraint-propagates : ∀ (m : SynthModel) (c₁ c₂ : Config) (outcome : Outcome) →
      FeatureEquiv (SynthModel.dead-pred m) c₁ c₂ →
      FeatureEquiv (SynthModel.solved-pred m) c₁ c₂ →
      OutcomeConstraint (synth-is-dead m) (synth-is-solved m) c₁ outcome →
      OutcomeConstraint (synth-is-dead m) (synth-is-solved m) c₂ outcome
    obs-constraint-propagates m c₁ c₂ dead d-eq s-eq dead-c₁ =
      dead-propagates m c₁ c₂ d-eq dead-c₁
    obs-constraint-propagates m c₁ c₂ solved d-eq s-eq (d-false , s-true) =
      trans (sym (propagation (SynthModel.dead-pred m) c₁ c₂ d-eq)) d-false ,
      solved-propagates m c₁ c₂ s-eq s-true
    obs-constraint-propagates m c₁ c₂ ongoing d-eq s-eq (d-false , s-false) =
      ongoing-propagates m c₁ c₂ d-eq s-eq d-false s-false

    ------------------------------------------------------------------
    -- SECTION 5: INTEGRATION WITH EC
    ------------------------------------------------------------------

    module WithTruePredicates
      (is-dead-true   : Config → Bool)
      (is-solved-true : Config → Bool)
      where

      ModelCorrect : SynthModel → Set
      ModelCorrect m =
        (∀ c → synth-is-dead m c ≡ is-dead-true c) ×
        (∀ c → synth-is-solved m c ≡ is-solved-true c)

      step-correct : ∀ (m : SynthModel) →
        ModelCorrect m →
        ∀ s a → synth-step m s a ≡ make-step is-dead-true is-solved-true s a
      step-correct m (d-ok , s-ok) Dead       _ = refl
      step-correct m (d-ok , s-ok) (Solved c) _ = refl
      step-correct m (d-ok , s-ok) (Ongoing c) a
        rewrite d-ok (place c a) | s-ok (place c a) = refl

    ------------------------------------------------------------------
    -- SECTION 6: VERSION SPACE ANALYSIS
    ------------------------------------------------------------------

    InVersionSpace : SynthModel → List PlacementObs → Set
    InVersionSpace m os = AllModelConsistent m os

    true-model-survives : ∀ m os o →
      InVersionSpace m os →
      ModelConsistent m o →
      InVersionSpace m (o ∷ os)
    true-model-survives m os o vs mc = mc , vs

    vs-shrinks : ∀ m o os →
      InVersionSpace m (o ∷ os) →
      InVersionSpace m os
    vs-shrinks _ _ _ (_ , rest) = rest

    ------------------------------------------------------------------
    -- SECTION 7: CEGIS FOR PLACEMENT MODELS
    --
    -- Uses the generic CEGIS from Core to synthesize is-dead and
    -- is-solved predicates from placement observations.
    --
    -- The pipeline:
    --   1. Convert PlacementObs → PredObs (one stream for dead,
    --      one for solved)
    --   2. Run CEGIS for each predicate independently
    --   3. Combine surviving candidates into SynthModel
    --
    -- Propagation acceleration is inherited: feature-equivalent
    -- configs eliminate the same candidates automatically.
    ------------------------------------------------------------------

    module WithCEGIS
      (all-features : List Feature)
      where

      open CEGIS all-features public

      -- Map Outcome to expected is-dead value
      outcome-dead : Outcome → Bool
      outcome-dead dead    = true
      outcome-dead solved  = false
      outcome-dead ongoing = false

      -- Map Outcome to expected is-solved value
      outcome-solved : Outcome → Bool
      outcome-solved dead    = false
      outcome-solved solved  = true
      outcome-solved ongoing = false

      -- Convert placement observation → predicate observation
      dead-obs : PlacementObs → PredObs
      dead-obs o =
        PlacementObs.result o , outcome-dead (PlacementObs.outcome o)

      solved-obs : PlacementObs → PredObs
      solved-obs o =
        PlacementObs.result o , outcome-solved (PlacementObs.outcome o)

      dead-obs-list : List PlacementObs → List PredObs
      dead-obs-list = map dead-obs

      solved-obs-list : List PlacementObs → List PredObs
      solved-obs-list = map solved-obs

      -- Synthesize is-dead predicate from observations
      synth-dead : ℕ → List PlacementObs → VersionSpace
      synth-dead depth obs =
        cegis-loop (initial-vs depth) (dead-obs-list obs)

      -- Synthesize is-solved predicate from observations
      synth-solved : ℕ → List PlacementObs → VersionSpace
      synth-solved depth obs =
        cegis-loop (initial-vs depth) (solved-obs-list obs)

      -- Pick first surviving candidate from each version space
      pick-model : VersionSpace → VersionSpace → Maybe SynthModel
      pick-model (d ∷ _) (s ∷ _) = just (record
        { dead-pred = d ; solved-pred = s })
      pick-model _ _ = nothing

      -- Full CEGIS pipeline: enumerate, observe, refine, pick
      cegis-synth : ℕ → List PlacementObs → Maybe SynthModel
      cegis-synth depth obs =
        pick-model (synth-dead depth obs)
                   (synth-solved depth obs)

      -- Version space sizes after refinement
      dead-vs-size : ℕ → List PlacementObs → ℕ
      dead-vs-size depth obs = length (synth-dead depth obs)

      solved-vs-size : ℕ → List PlacementObs → ℕ
      solved-vs-size depth obs = length (synth-solved depth obs)
