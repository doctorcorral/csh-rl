{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Stochastic.CartPolePhysicsLearning
--
-- CartPole with physics-motivated dynamics, 4 abstract states, and
-- the full Learn → Verify → Lift pipeline.
--
-- Abstract state = Phase = (angle sign × angular velocity sign):
--   LL  θ < 0, θ̇ < 0  (falling left  — critical)
--   LR  θ < 0, θ̇ ≥ 0  (recovering left  — safe)
--   RL  θ ≥ 0, θ̇ < 0  (recovering right — safe)
--   RR  θ ≥ 0, θ̇ ≥ 0  (falling right — critical)
--
-- Step function encodes linearised CartPole dynamics:
--   Left push  ⟹  θ̈ > 0 (pole tilts right)
--   Right push ⟹  θ̈ < 0 (pole tilts left)
--
-- CEGIS discovers TWO features (angle sign AND angular velocity sign)
-- are needed to express the ranking — a genuinely richer policy than
-- the 2-state version.  The learned policy distinguishes critical
-- states (one action mandatory) from safe states (either action OK).
--
-- Lifted to ℚ⁴ via abstract-lift.  All --safe, no postulates.
------------------------------------------------------------------------

module CSHRL.Tasks.Stochastic.CartPolePhysicsLearning where

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

-- Phase-space quadrant (angle sign × angular velocity sign)
data Phase : Set where
  LL : Phase    -- θ < 0, θ̇ < 0  (falling left)
  LR : Phase    -- θ < 0, θ̇ ≥ 0  (recovering from left)
  RL : Phase    -- θ ≥ 0, θ̇ < 0  (recovering from right)
  RR : Phase    -- θ ≥ 0, θ̇ ≥ 0  (falling right)

------------------------------------------------------------------------
-- PART 1 — Physics-motivated step function
--
-- Linearised CartPole (small-angle approx, standard parameters):
--   θ̈ ≈ (g·θ − F/m_total) / (l·(4/3 − m_p/m_total))
--
--   Left push  (F < 0): θ̈ > 0 → angular velocity increases
--   Right push (F > 0): θ̈ < 0 → angular velocity decreases
--
-- At critical states (angle and velocity same sign, diverging):
--   correct push → velocity recovers (reward 1)
--   wrong push   → stays critical    (reward 0)
--
-- At safe states (angle and velocity opposite sign, recovering):
--   correct push → stay safe      (reward 1)
--   wrong push   → back to critical (reward 1, but worse position)
------------------------------------------------------------------------

abstract-step : Phase → Action → Dist (Phase × ℕ)
abstract-step LL Left  = pure (LR , 1)    -- θ̈ > 0: vel recovers
abstract-step LL Right = pure (LL , 0)    -- θ̈ < 0: stays critical
abstract-step LR Left  = pure (LR , 1)    -- θ̈ > 0: continue safe
abstract-step LR Right = pure (LL , 1)    -- θ̈ < 0: vel reverses
abstract-step RL Left  = pure (RR , 1)    -- θ̈ > 0: vel reverses
abstract-step RL Right = pure (RL , 1)    -- θ̈ < 0: continue safe
abstract-step RR Left  = pure (RR , 0)    -- θ̈ > 0: stays critical
abstract-step RR Right = pure (RL , 1)    -- θ̈ < 0: vel recovers

------------------------------------------------------------------------
-- PART 2 — FOSD Synthesis: discover ranking from dynamics
------------------------------------------------------------------------

open import CSHRL.Synthesis.FOSDStochasticFiniteMDP
open SFDMDPSynthesisFOSD Phase Action abstract-step all-actions default-action

data Feature : Set where
  angle-neg : Feature    -- θ < 0
  vel-neg   : Feature    -- θ̇ < 0
  right-ok  : Feature    -- ¬(θ < 0 ∧ θ̇ < 0): Right is a viable action

eval-feature : Feature → Phase → Bool
eval-feature angle-neg LL = true
eval-feature angle-neg LR = true
eval-feature angle-neg RL = false
eval-feature angle-neg RR = false
eval-feature vel-neg   LL = true
eval-feature vel-neg   LR = false
eval-feature vel-neg   RL = true
eval-feature vel-neg   RR = false
eval-feature right-ok  LL = false
eval-feature right-ok  LR = true
eval-feature right-ok  RL = true
eval-feature right-ok  RR = true

open WithStateFeatures Feature eval-feature
open WithCEGIS (angle-neg ∷ vel-neg ∷ right-ok ∷ [])

-- Depth-0 FOSD observations from abstract-step
test-RL-LL : fosd-compare LL Right Left 0 ≡ true
test-RL-LL = refl

test-RL-RR : fosd-compare RR Right Left 0 ≡ false
test-RL-RR = refl

test-LR-RR : fosd-compare RR Left Right 0 ≡ true
test-LR-RR = refl

test-LR-LL : fosd-compare LL Left Right 0 ≡ false
test-LR-LL = refl

-- CEGIS synthesizes ranking predicates from all 4 phases
obs-RL : List PredObs
obs-RL = (LL , true) ∷ (LR , true) ∷ (RL , true) ∷ (RR , false) ∷ []

synth-RL : Maybe PredProg
synth-RL = synth-rank-pred 1 obs-RL

-- Discovered: angle-neg ∨ vel-neg  (true at {LL, LR, RL}, false at {RR})
test-synth-RL : synth-RL ≡ just (feat angle-neg ∨p feat vel-neg)
test-synth-RL = refl

obs-LR : List PredObs
obs-LR = (LL , false) ∷ (LR , true) ∷ (RL , true) ∷ (RR , true) ∷ []

synth-LR : Maybe PredProg
synth-LR = synth-rank-pred 1 obs-LR

-- Discovered: right-ok  (false at {LL}, true at {LR, RL, RR})
test-synth-LR : synth-LR ≡ just (feat right-ok)
test-synth-LR = refl

------------------------------------------------------------------------
-- PART 3 — Learning Bridge: ranking from samples
------------------------------------------------------------------------

open WithLearningBridge (angle-neg ∷ vel-neg ∷ right-ok ∷ []) _≟ₐ_

import CSHRL.Learning.Base as LB
open LB.UniversalLearning Phase Action _≟ₐ_
  using (Sample; sample; Violation)

-- 8 samples: all 4 phases × both action pairs
learning-samples : List Sample
learning-samples =
  sample LL Right Left  ∷ sample LR Right Left  ∷
  sample RL Right Left  ∷ sample RR Right Left  ∷
  sample LL Left  Right ∷ sample LR Left  Right ∷
  sample RL Left  Right ∷ sample RR Left  Right ∷ []

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

-- At LL (falling left): Left is critical
test-learned-LL-RL : ∀ m → learned-model ≡ just m →
  eval (RankModel.prefer m Right Left) LL ≡ true
test-learned-LL-RL m refl = refl

-- At RR (falling right): Right is critical
test-learned-RR-LR : ∀ m → learned-model ≡ just m →
  eval (RankModel.prefer m Left Right) RR ≡ true
test-learned-RR-LR m refl = refl

------------------------------------------------------------------------
-- PART 4 — State abstraction: ℚ⁴ → Phase (angle × velocity signs)
------------------------------------------------------------------------

project : ConcreteState → Phase
project (_ , _ , θ , θ̇) with θ <? 0ℚ | θ̇ <? 0ℚ
... | yes _ | yes _ = LL
... | yes _ | no  _ = LR
... | no  _ | yes _ = RL
... | no  _ | no  _ = RR

cartpole-abstraction : StateAbstraction ConcreteState Phase
cartpole-abstraction = record
  { project = project
  ; embed   = λ { LL → (0ℚ , 0ℚ , -½ , -½)
                ; LR → (0ℚ , 0ℚ , -½ ,  ½)
                ; RL → (0ℚ , 0ℚ ,  ½ , -½)
                ; RR → (0ℚ , 0ℚ ,  ½ ,  ½) }
  ; section = λ { LL → refl ; LR → refl ; RL → refl ; RR → refl }
  }

------------------------------------------------------------------------
-- PART 5 — Marginals and verified abstract ranking
--
-- The ordering was DISCOVERED by CEGIS from dynamics (Part 2).
-- Marginals are constant in n so SD[0] preservation is trivial.
------------------------------------------------------------------------

marginal-by-quad : Phase → Action → ℕ → Dist ℕ
marginal-by-quad LL Left  _ = (2 , 1) ∷ (1 , 1) ∷ []
marginal-by-quad LL Right _ = (0 , 1) ∷ (0 , 1) ∷ []
marginal-by-quad LR Left  _ = (1 , 1) ∷ (1 , 1) ∷ []
marginal-by-quad LR Right _ = (1 , 1) ∷ (1 , 1) ∷ []
marginal-by-quad RL Left  _ = (1 , 1) ∷ (1 , 1) ∷ []
marginal-by-quad RL Right _ = (1 , 1) ∷ (1 , 1) ∷ []
marginal-by-quad RR Left  _ = (0 , 1) ∷ (0 , 1) ∷ []
marginal-by-quad RR Right _ = (2 , 1) ∷ (1 , 1) ∷ []

marginal : ConcreteState → Action → ℕ → Dist ℕ
marginal s = marginal-by-quad (project s)

-- Ordering discovered by CEGIS:
--   LL: Left only (critical)    LR: indifferent (safe)
--   RL: indifferent (safe)      RR: Right only (critical)
order : Phase → Action → Action → Set
order LL Left  Left  = ⊤
order LL Right Left  = ⊤
order LL Right Right = ⊤
order LL Left  Right = ⊥
order LR Left  Left  = ⊤
order LR Right Left  = ⊤
order LR Left  Right = ⊤
order LR Right Right = ⊤
order RL Left  Left  = ⊤
order RL Right Left  = ⊤
order RL Left  Right = ⊤
order RL Right Right = ⊤
order RR Left  Left  = ⊤
order RR Left  Right = ⊤
order RR Right Right = ⊤
order RR Right Left  = ⊥

private
  good neutral bad : Dist ℕ
  good    = (2 , 1) ∷ (1 , 1) ∷ []
  neutral = (1 , 1) ∷ (1 , 1) ∷ []
  bad     = (0 , 1) ∷ (0 , 1) ∷ []

fosd-bad≤good : bad FOSD≤ good
fosd-bad≤good = fosd?-sound bad good refl

private
  abs-marginal : Phase → Action → ℕ → Dist ℕ
  abs-marginal p = marginal (StateAbstraction.embed cartpole-abstraction p)

abstract-ranking : VerifiedRanking Phase Action abs-marginal 0
abstract-ranking = record
  { _≤ₐ_ = order
  ; preserves = pf
  }
  where
    pf : ∀ a b s → order s a b →
      ∀ n → abs-marginal s a n SD[ 0 ]≤ abs-marginal s b n
    -- LL: Left only
    pf Left  Left  LL _ n = SD-refl 0 good
    pf Right Left  LL _ n = fosd-bad≤good
    pf Right Right LL _ n = SD-refl 0 bad
    pf Left  Right LL () n
    -- LR: indifferent
    pf Left  Left  LR _ n = SD-refl 0 neutral
    pf Right Left  LR _ n = SD-refl 0 neutral
    pf Left  Right LR _ n = SD-refl 0 neutral
    pf Right Right LR _ n = SD-refl 0 neutral
    -- RL: indifferent
    pf Left  Left  RL _ n = SD-refl 0 neutral
    pf Right Left  RL _ n = SD-refl 0 neutral
    pf Left  Right RL _ n = SD-refl 0 neutral
    pf Right Right RL _ n = SD-refl 0 neutral
    -- RR: Right only
    pf Left  Left  RR _ n = SD-refl 0 bad
    pf Left  Right RR _ n = fosd-bad≤good
    pf Right Right RR _ n = SD-refl 0 good
    pf Right Left  RR () n

------------------------------------------------------------------------
-- PART 6 — Lift to ℚ⁴
------------------------------------------------------------------------

marginal-invariant : ∀ s₁ s₂ → project s₁ ≡ project s₂ →
  ∀ a t → marginal s₁ a t ≡ marginal s₂ a t
marginal-invariant s₁ s₂ eq a t = cong (λ p → marginal-by-quad p a t) eq

continuous-ranking : VerifiedRanking ConcreteState Action marginal 0
continuous-ranking =
  abstract-lift cartpole-abstraction marginal-invariant abstract-ranking

------------------------------------------------------------------------
-- PART 7 — Spot checks: 4-region policy on ℚ⁴
--
-- The policy uses BOTH angle AND angular velocity:
--   LL (falling left):  Left mandatory
--   LR (recovering):    either action OK
--   RL (recovering):    either action OK
--   RR (falling right): Right mandatory
------------------------------------------------------------------------

open VerifiedRanking continuous-ranking

¼ : ℚ
¼ = + 1 / 4

-¼ : ℚ
-¼ = - ¼

-- LL region (θ < 0, θ̇ < 0): Left is critical
check-LL : _≤ₐ_ (0ℚ , 0ℚ , -½ , -½) Right Left
check-LL = tt

-- LR region (θ < 0, θ̇ ≥ 0): both actions OK
check-LR-a : _≤ₐ_ (0ℚ , 0ℚ , -¼ , ¼) Right Left
check-LR-a = tt

check-LR-b : _≤ₐ_ (0ℚ , 0ℚ , -¼ , ¼) Left Right
check-LR-b = tt

-- RL region (θ ≥ 0, θ̇ < 0): both actions OK
check-RL-a : _≤ₐ_ (0ℚ , 0ℚ , ¼ , -¼) Left Right
check-RL-a = tt

check-RL-b : _≤ₐ_ (0ℚ , 0ℚ , ¼ , -¼) Right Left
check-RL-b = tt

-- RR region (θ ≥ 0, θ̇ ≥ 0): Right is critical
check-RR : _≤ₐ_ (½ , -½ , ¼ , ½) Left Right
check-RR = tt

------------------------------------------------------------------------
-- PART 8 — Extractable Controller
--
-- The verified ranking yields a concrete decision procedure on ℚ⁴.
-- At critical states the action is mandatory; at safe states we
-- tie-break by angle sign (push toward centre).
--
-- Equivalent Python / gym controller:
--
--   def decide(obs):
--       theta, theta_dot = obs[2], obs[3]
--       if theta < 0 and theta_dot < 0: return 0   # Left
--       if theta >= 0 and theta_dot >= 0: return 1  # Right
--       return 0 if theta < 0 else 1                # safe: lean
------------------------------------------------------------------------

decide : ConcreteState → Action
decide s with project s
... | LL = Left
... | LR = Left
... | RL = Right
... | RR = Right

private
  ll-rep rr-rep lr-rep rl-rep : ConcreteState
  ll-rep = (0ℚ , 0ℚ , -½ , -½)
  rr-rep = (0ℚ , 0ℚ ,  ½ ,  ½)
  lr-rep = (0ℚ , 0ℚ , -½ ,  ½)
  rl-rep = (0ℚ , 0ℚ ,  ½ , -½)

decide-critical-left : decide ll-rep ≡ Left
decide-critical-left = refl

decide-critical-right : decide rr-rep ≡ Right
decide-critical-right = refl

decide-left-optimal : _≤ₐ_ ll-rep Right Left
decide-left-optimal = tt

decide-right-optimal : _≤ₐ_ rr-rep Left Right
decide-right-optimal = tt

decide-safe-lr : _≤ₐ_ lr-rep Left Right × _≤ₐ_ lr-rep Right Left
decide-safe-lr = tt , tt

decide-safe-rl : _≤ₐ_ rl-rep Left Right × _≤ₐ_ rl-rep Right Left
decide-safe-rl = tt , tt
