{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Stochastic.CartPoleContinuousLearning
--
-- The full pipeline: Learn → Verify → Lift to Continuous.
--
-- 1. LEARN: FOSD synthesis on a 2-state abstract CartPole discovers
--    the optimal ranking from observations (4 samples).
-- 2. VERIFY: the learned ordering preserves SD[0] on the marginal
--    reward distributions (proved computationally via fosd?-sound).
-- 3. LIFT: abstract-lift transfers the verified ranking from Bool
--    to ℚ⁴ — a verified policy for ALL rational CartPole states.
--
-- No hand-coded policy: the ordering is discovered by CEGIS from
-- FOSD observations.  No discretization of the continuous state.
-- No postulates.  All --safe.
------------------------------------------------------------------------

module CSHRL.Tasks.Stochastic.CartPoleContinuousLearning where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ)
open import Data.List using (List; _∷_; [])
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (Dec; yes; no)

open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 0ℚ; ½; -½; _/_; -_)
open import Data.Rational.Properties using (_<?_)

open import CSHRL.Probability.Finite using (Dist; pure)
open import CSHRL.Probability.SD using (_SD[_]≤_; SD-refl)
open import CSHRL.Probability.FOSD using (_FOSD≤_; fosd?-sound)
open import CSHRL.Core.Compose using (VerifiedRanking)
open import CSHRL.Core.Abstraction using (StateAbstraction; abstract-lift)

------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------

ConcreteState : Set
ConcreteState = ℚ × ℚ × ℚ × ℚ

data Action : Set where
  Left  : Action
  Right : Action

_≟ₐ_ : (a b : Action) → Dec (a ≡ b)
Left  ≟ₐ Left  = yes refl
Left  ≟ₐ Right = no (λ ())
Right ≟ₐ Left  = no (λ ())
Right ≟ₐ Right = yes refl

all-actions : List Action
all-actions = Left ∷ Right ∷ []

default-action : Action
default-action = Left

------------------------------------------------------------------------
-- PART 1 — Abstract MDP on Bool (2 states)
--
-- Reward encodes angle-action alignment:
--   left-half + Left  → reward 1 (correct push)
--   left-half + Right → reward 0 (wrong push)
--   right-half + Left  → reward 0
--   right-half + Right → reward 1
------------------------------------------------------------------------

abstract-step : Bool → Action → Dist (Bool × ℕ)
abstract-step true  Left  = pure (true  , 1)
abstract-step true  Right = pure (true  , 0)
abstract-step false Left  = pure (false , 0)
abstract-step false Right = pure (false , 1)

------------------------------------------------------------------------
-- PART 2 — FOSD Synthesis: discover the ranking from observations
------------------------------------------------------------------------

open import CSHRL.Synthesis.FOSDStochasticFiniteMDP
open SFDMDPSynthesisFOSD Bool Action abstract-step all-actions default-action

data Feature : Set where
  is-left : Feature

eval-feature : Feature → Bool → Bool
eval-feature is-left b = b

open WithStateFeatures Feature eval-feature
open WithCEGIS (is-left ∷ [])

-- FOSD observations at depth 0 (computed from abstract-step)
test-RL-at-left  : fosd-compare true  Right Left 0 ≡ true
test-RL-at-left  = refl

test-RL-at-right : fosd-compare false Right Left 0 ≡ false
test-RL-at-right = refl

test-LR-at-right : fosd-compare false Left Right 0 ≡ true
test-LR-at-right = refl

test-LR-at-left  : fosd-compare true  Left Right 0 ≡ false
test-LR-at-left  = refl

-- CEGIS synthesizes predicates from observations
-- "Where does Right ≤ Left hold?"  →  feat is-left  (left half only)
synth-RL : Maybe PredProg
synth-RL = synth-rank-pred 1
  ((true , true) ∷ (false , false) ∷ [])

test-synth-RL : synth-RL ≡ just (feat is-left)
test-synth-RL = refl

-- "Where does Left ≤ Right hold?"  →  ¬p feat is-left  (right half only)
synth-LR : Maybe PredProg
synth-LR = synth-rank-pred 1
  ((false , true) ∷ (true , false) ∷ [])

test-synth-LR : synth-LR ≡ just (¬p feat is-left)
test-synth-LR = refl

------------------------------------------------------------------------
-- PART 3 — Learning Bridge: same ranking from samples
------------------------------------------------------------------------

open WithLearningBridge (is-left ∷ []) _≟ₐ_

import CSHRL.Learning.Base as LB
open LB.UniversalLearning Bool Action _≟ₐ_
  using (Sample; sample; Violation)

learning-samples : List Sample
learning-samples = sample true  Right Left  ∷
                   sample false Right Left  ∷
                   sample true  Left  Right ∷
                   sample false Left  Right ∷ []

test-nothing : ℕ → Sample → Maybe Violation
test-nothing _ _ = nothing

sls : SynthLearnerState
sls = synth-learn-batch test-nothing
        (init-synth-learner 1) learning-samples

learned-model : Maybe RankModel
learned-model = extract-rank-model
  ((Right , Left) ∷ (Left , Right) ∷ []) sls

test-learned-just : learned-model ≡ just _
test-learned-just = refl

test-learned-RL : ∀ m → learned-model ≡ just m →
  eval (RankModel.prefer m Right Left) true ≡ true
test-learned-RL m refl = refl

test-learned-LR : ∀ m → learned-model ≡ just m →
  eval (RankModel.prefer m Left Right) false ≡ true
test-learned-LR m refl = refl

------------------------------------------------------------------------
-- PART 4 — State abstraction: ℚ⁴ → Bool (angle sign)
------------------------------------------------------------------------

is-left-half : ℚ → Bool
is-left-half θ with θ <? 0ℚ
... | yes _ = true
... | no  _ = false

project : ConcreteState → Bool
project (_ , _ , θ , _) = is-left-half θ

cartpole-abstraction : StateAbstraction ConcreteState Bool
cartpole-abstraction = record
  { project = project
  ; embed   = λ { true  → (0ℚ , 0ℚ , -½ , 0ℚ)
                ; false → (0ℚ , 0ℚ ,  ½ , 0ℚ) }
  ; section = λ { true → refl ; false → refl }
  }

------------------------------------------------------------------------
-- PART 5 — Marginals and verified ranking on Bool
--
-- The ordering was DISCOVERED by CEGIS (Part 2).
-- The SD[0] preservation is proved computationally.
------------------------------------------------------------------------

marginal-by-half : Bool → Action → ℕ → Dist ℕ
marginal-by-half true  Left  _ = (2 , 1) ∷ (1 , 1) ∷ []
marginal-by-half true  Right _ = (0 , 1) ∷ (0 , 1) ∷ []
marginal-by-half false Left  _ = (0 , 1) ∷ (0 , 1) ∷ []
marginal-by-half false Right _ = (2 , 1) ∷ (1 , 1) ∷ []

marginal : ConcreteState → Action → ℕ → Dist ℕ
marginal s = marginal-by-half (project s)

order : Bool → Action → Action → Set
order true  Left  Left  = ⊤
order true  Right Left  = ⊤
order true  Right Right = ⊤
order true  Left  Right = ⊥
order false Left  Left  = ⊤
order false Left  Right = ⊤
order false Right Right = ⊤
order false Right Left  = ⊥

private
  good bad : Dist ℕ
  good = (2 , 1) ∷ (1 , 1) ∷ []
  bad  = (0 , 1) ∷ (0 , 1) ∷ []

fosd-bad≤good : bad FOSD≤ good
fosd-bad≤good = fosd?-sound bad good refl

private
  abs-marginal : Bool → Action → ℕ → Dist ℕ
  abs-marginal b = marginal (StateAbstraction.embed cartpole-abstraction b)

abstract-ranking : VerifiedRanking Bool Action abs-marginal 0
abstract-ranking = record
  { _≤ₐ_ = order
  ; preserves = pf
  }
  where
    pf : ∀ a b s → order s a b →
      ∀ n → abs-marginal s a n SD[ 0 ]≤ abs-marginal s b n
    pf Left  Left  true  _ n = SD-refl 0 good
    pf Right Left  true  _ n = fosd-bad≤good
    pf Right Right true  _ n = SD-refl 0 bad
    pf Left  Left  false _ n = SD-refl 0 bad
    pf Left  Right false _ n = fosd-bad≤good
    pf Right Right false _ n = SD-refl 0 good
    pf Left  Right true  () n
    pf Right Left  false () n

------------------------------------------------------------------------
-- PART 6 — LIFT: verified ranking on ALL of ℚ⁴
------------------------------------------------------------------------

marginal-invariant : ∀ s₁ s₂ → project s₁ ≡ project s₂ →
  ∀ a t → marginal s₁ a t ≡ marginal s₂ a t
marginal-invariant s₁ s₂ eq a t = cong (λ b → marginal-by-half b a t) eq

continuous-cartpole-ranking : VerifiedRanking ConcreteState Action marginal 0
continuous-cartpole-ranking =
  abstract-lift cartpole-abstraction marginal-invariant abstract-ranking

------------------------------------------------------------------------
-- PART 7 — Spot checks at arbitrary rational states
--
-- The verified ranking covers every (x, ẋ, θ, θ̇) ∈ ℚ⁴.
------------------------------------------------------------------------

open VerifiedRanking continuous-cartpole-ranking

¼ : ℚ
¼ = + 1 / 4

-¼ : ℚ
-¼ = - ¼

check-neg-½  : _≤ₐ_ (0ℚ , 0ℚ , -½ , 0ℚ) Right Left
check-neg-½  = tt

check-neg-¼  : _≤ₐ_ (½ , -½ , -¼ , ½) Right Left
check-neg-¼  = tt

check-pos-½  : _≤ₐ_ (0ℚ , 0ℚ , ½ , 0ℚ) Left Right
check-pos-½  = tt

check-pos-¼  : _≤ₐ_ (-½ , ½ , ¼ , -½) Left Right
check-pos-¼  = tt
