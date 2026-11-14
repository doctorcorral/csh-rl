{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Stochastic.GamblersRuinFOSDSynth
--
-- FOSD-based synthesis in GamblersRuin (richer than BiasedBandit).
--
-- GamblersRuin: 3 states (Ruin, Middle, Goal), 2 actions (Bet, Quit).
-- - Bet from Middle: 50% Goal (r=1), 50% Ruin (r=0)
-- - Quit from Middle: 100% Middle (r=0)
--
-- FOSD requires equal total weights for comparison. GamblersRuin's
-- step gives Bet weight 2, Quit weight 1. We use step-fosd that scales
-- Quit to weight 2 (same semantics: 100% (Middle,0)) so fosd? can compare.
--
-- At depth 0 with step-fosd: Bet has (1,1)∷(0,1)∷[], Quit has (0,2)∷[].
-- Quit FOSD≤ Bet (Bet dominates). Optimal: Bet at Middle.
------------------------------------------------------------------------

module CSHRL.Tasks.Stochastic.GamblersRuinFOSDSynth where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.List using (List; _∷_; []; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; cong₂; sym; subst)
open import Data.Nat.Properties using (≤-refl)
open import Relation.Nullary using (Dec; yes; no)

open import CSHRL.Tasks.Stochastic.GamblersRuin
  using (State; Action; all-actions; default-action;
         Ruin; Middle; Goal; Bet; Quit)

open import CSHRL.Probability.Finite using (Dist; pure; bernoulli; scale; _>>=_; >>=-singleton)
open import CSHRL.Probability.FOSD using (_FOSD≤_; FOSD-refl; fosd?; fosd?-sound; fosd?-scale)

-- Step with equal total weights at Middle (required for fosd?)
step-fosd : State → Action → Dist (State × ℕ)
step-fosd Middle Bet  = bernoulli (Goal , 1) 1 (Ruin , 0) 1
step-fosd Middle Quit = ((Middle , 0) , 2) ∷ []   -- weight 2 to match Bet
step-fosd Ruin   _    = pure (Ruin , 0)
step-fosd Goal   _    = pure (Goal , 0)

open import CSHRL.Synthesis.FOSDStochasticFiniteMDP
open SFDMDPSynthesisFOSD State Action step-fosd all-actions default-action

------------------------------------------------------------------------
-- Features: is-middle (true only at Middle)
------------------------------------------------------------------------

data Feature : Set where
  is-middle : Feature

eval-feature : Feature → State → Bool
eval-feature is-middle Ruin   = false
eval-feature is-middle Middle = true
eval-feature is-middle Goal   = false

------------------------------------------------------------------------
-- FOSD observations at Middle
------------------------------------------------------------------------

open WithStateFeatures Feature eval-feature
open WithCEGIS (is-middle ∷ [])

-- Quit ≤ Bet at Middle: Quit is dominated by Bet
obs-quit≤bet : PredObs
obs-quit≤bet = Middle , fosd-compare Middle Quit Bet 0

-- Bet ≤ Quit at Middle: false (Bet dominates, not the other way)
obs-bet≤quit : PredObs
obs-bet≤quit = Middle , fosd-compare Middle Bet Quit 0

-- Observation list for prefer(Quit, Bet): we want true at Middle
obs-prefer-quit-bet : List PredObs
obs-prefer-quit-bet = obs-quit≤bet ∷ []

------------------------------------------------------------------------
-- Synthesis
------------------------------------------------------------------------

synth-quit≤bet : Maybe PredProg
synth-quit≤bet = synth-rank-pred 1 obs-prefer-quit-bet

------------------------------------------------------------------------
-- Verification
------------------------------------------------------------------------

-- FOSD at depth 0: Quit FOSD≤ Bet (Bet dominates Quit)
test-fosd-quit≤bet : fosd-compare Middle Quit Bet 0 ≡ true
test-fosd-quit≤bet = refl

-- Bet does not FOSD≤ Quit
test-fosd-bet≤quit : fosd-compare Middle Bet Quit 0 ≡ false
test-fosd-bet≤quit = refl

-- Synthesis succeeds (CEGIS returns first survivor: truep or feat is-middle)
test-synth-succeeds : synth-quit≤bet ≡ just truep
test-synth-succeeds = refl

-- Synthesized predicate holds at Middle (Quit ≤ Bet) → Bet is preferred
test-pred-at-middle : eval truep Middle ≡ true
test-pred-at-middle = refl

------------------------------------------------------------------------
-- Policy check: at Middle, prefer Bet over Quit
--
-- The synthesized predicate for prefer(Quit, Bet) is true at Middle,
-- meaning Quit ≤ Bet, so Bet is preferred. At Ruin/Goal (terminal),
-- both actions are equivalent.
------------------------------------------------------------------------

policy-at-middle : Action
policy-at-middle = Bet

test-policy : eval truep Middle ≡ true
test-policy = refl

------------------------------------------------------------------------
-- Learning Bridge Demo
--
-- Demonstrates the full learning + synthesis pipeline: samples are
-- converted to FOSD observations, synth-learn-batch updates both
-- learner state and per-pair version spaces, extract-rank-model
-- builds the RankModel.
------------------------------------------------------------------------

_≟ₐ_ : (a b : Action) → Dec (a ≡ b)
Bet  ≟ₐ Bet  = yes refl
Bet  ≟ₐ Quit = no (λ ())
Quit ≟ₐ Bet  = no (λ ())
Quit ≟ₐ Quit = yes refl

import CSHRL.Learning.Base as LB
open LB.UniversalLearning State Action _≟ₐ_ using (Sample; Violation; sample)

open WithLearningBridge (is-middle ∷ []) _≟ₐ_

-- No-violation test (depth 0 suffices for GamblersRuin)
test-no-violation : ℕ → Sample → Maybe Violation
test-no-violation _ _ = nothing

-- FOSD-based violation test: returns violation when actions are FOSD-incomparable
-- at the current depth (neither a FOSD≤ b nor b FOSD≤ a). Signals that we need
-- an observation to resolve the ranking.
open LB.UniversalLearning State Action _≟ₐ_ using (violation)

_∨ᵇ_ : Bool → Bool → Bool
false ∨ᵇ y = y
true  ∨ᵇ _ = true

test-fosd-violation : ℕ → Sample → Maybe Violation
test-fosd-violation k (sample s a b) =
  if (fosd-compare s a b k ∨ᵇ fosd-compare s b a k) then nothing
  else just (violation s b a k)

-- Sample: compare Quit vs Bet at Middle
sample-quit-bet : Sample
sample-quit-bet = sample Middle Quit Bet

-- Quit vs Bet at Middle: FOSD-comparable (Quit ≤ Bet), so no violation
test-fosd-no-violation : test-fosd-violation 0 sample-quit-bet ≡ nothing
test-fosd-no-violation = refl

samples-batch : List Sample
samples-batch = sample-quit-bet ∷ []

-- Run learning + synthesis
sls-after : SynthLearnerState
sls-after = synth-learn-batch test-no-violation (init-synth-learner 1) samples-batch

-- Extract rank model for (Quit, Bet)
pairs : List (Action × Action)
pairs = (Quit , Bet) ∷ []

extracted-model : Maybe RankModel
extracted-model = extract-rank-model pairs sls-after

-- Extracted model succeeds and prefers Bet over Quit at Middle
test-extracted-just : extracted-model ≡ just _
test-extracted-just = refl

test-extracted-correct : ∀ m → extracted-model ≡ just m →
  eval (RankModel.prefer m Quit Bet) Middle ≡ true
test-extracted-correct m refl = refl

------------------------------------------------------------------------
-- ModelPreservesFOSD for GamblersRuin
--
-- Concrete RankModel: prefer Quit Bet = truep (Quit ≤ Bet, Bet preferred),
-- prefer Bet Quit = falsep, prefer a a = truep. Proves that when the model
-- says a ≤ b, the preferred action b FOSD-dominates a.
------------------------------------------------------------------------

-- prefer Quit Bet = feat is-middle (true only at Middle, where Bet dominates)
-- prefer Bet Quit = falsep; prefer a a = truep
gambler-prefer : Action → Action → PredProg
gambler-prefer Quit Bet = feat is-middle
gambler-prefer Bet  Quit = falsep
gambler-prefer Quit Quit = truep
gambler-prefer Bet  Bet  = truep

gambler-rank : RankModel
gambler-rank = record { prefer = gambler-prefer }

-- RankHolds gambler-rank s Quit Bet only at Middle (feat is-middle = true)
-- RankHolds gambler-rank s Bet Quit never; RankHolds s a a always
open import CSHRL.Core.FOSD
open FOSDCore State Action step-fosd all-actions default-action
  using (marginal-reward; PointwiseFOSD; pw-fosd-refl)

-- Middle: Quit FOSD≤ Bet at depth 0 (via fosd?-sound)
middle-quit≤bet-0 : marginal-reward Middle Quit 0 FOSD≤ marginal-reward Middle Bet 0
middle-quit≤bet-0 = fosd?-sound (marginal-reward Middle Quit 0) (marginal-reward Middle Bet 0)
  test-fosd-quit≤bet

-- marginal-reward Middle Quit (suc n) ≡ scale 2 (marginal-reward Middle Quit n)
marginal-quit-scale : ∀ n →
  marginal-reward Middle Quit (suc n) ≡ scale 2 (marginal-reward Middle Quit n)
marginal-quit-scale n = >>=-singleton (Middle , 0) 2 f
  where f : (State × ℕ) → Dist ℕ
        f (s' , _) = marginal-reward s' default-action n

-- Terminal states: Goal and Ruin always yield (0,1)∷[]
marginal-goal-quit : ∀ n → marginal-reward Goal Quit n ≡ (0 , 1) ∷ []
marginal-goal-quit zero = refl
marginal-goal-quit (suc n) =
  trans (>>=-singleton (Goal , 0) 1 f)
        (cong (scale 1) (marginal-goal-quit n))
  where f : (State × ℕ) → Dist ℕ
        f (s' , _) = marginal-reward s' default-action n

marginal-ruin-quit : ∀ n → marginal-reward Ruin Quit n ≡ (0 , 1) ∷ []
marginal-ruin-quit zero = refl
marginal-ruin-quit (suc n) =
  trans (>>=-singleton (Ruin , 0) 1 f)
        (cong (scale 1) (marginal-ruin-quit n))
  where f : (State × ℕ) → Dist ℕ
        f (s' , _) = marginal-reward s' default-action n

-- Bet from Middle (suc n): 50% Goal, 50% Ruin → both give (0,1), so (0,1)∷(0,1)∷[]
marginal-bet-suc : ∀ n → marginal-reward Middle Bet (suc n) ≡ (0 , 1) ∷ (0 , 1) ∷ []
marginal-bet-suc n = cong₂ (λ g r → scale 1 g ++ scale 1 r ++ [])
  (marginal-goal-quit n) (marginal-ruin-quit n)

-- fosd? (marginal-reward Middle Quit n) (marginal-reward Middle Bet (suc n)) ≡ true
fosd-quit-bet-suc : ∀ n →
  fosd? (marginal-reward Middle Quit n) (marginal-reward Middle Bet (suc n)) ≡ true
fosd-quit-bet-suc zero = refl
fosd-quit-bet-suc (suc n) rewrite marginal-quit-scale n =
  fosd?-scale (marginal-reward Middle Quit n) (marginal-reward Middle Bet (suc (suc n))) 2
    (subst (λ ν → fosd? (marginal-reward Middle Quit n) ν ≡ true)
           (trans (marginal-bet-suc n) (sym (marginal-bet-suc (suc n))))
           (fosd-quit-bet-suc n))
    (s≤s z≤n)

-- Quit (suc n) FOSD≤ Bet (suc n) for all n
middle-quit≤bet-suc : ∀ n →
  marginal-reward Middle Quit (suc n) FOSD≤ marginal-reward Middle Bet (suc n)
middle-quit≤bet-suc n rewrite marginal-quit-scale n =
  fosd?-sound (scale 2 (marginal-reward Middle Quit n)) (marginal-reward Middle Bet (suc n))
    (fosd?-scale (marginal-reward Middle Quit n) (marginal-reward Middle Bet (suc n)) 2
      (fosd-quit-bet-suc n) (s≤s z≤n))

PointwiseFOSD-Depth0 : State → Action → Action → Set
PointwiseFOSD-Depth0 s a b =
  marginal-reward s b 0 FOSD≤ marginal-reward s a 0

ModelPreservesFOSD-Depth0 : RankModel → Set
ModelPreservesFOSD-Depth0 m = ∀ a b s →
  RankHolds m s a b → PointwiseFOSD-Depth0 s b a

middle-quit≤bet-0-only : PointwiseFOSD-Depth0 Middle Bet Quit
middle-quit≤bet-0-only = middle-quit≤bet-0

gambler-preserves-depth0 : ModelPreservesFOSD-Depth0 gambler-rank
gambler-preserves-depth0 Quit Bet Middle _ = middle-quit≤bet-0-only
gambler-preserves-depth0 Quit Bet Ruin   ()
gambler-preserves-depth0 Quit Bet Goal   ()
gambler-preserves-depth0 Bet  Quit s ()
gambler-preserves-depth0 Quit Quit s _ = FOSD-refl (marginal-reward s Quit 0)
gambler-preserves-depth0 Bet  Bet  s _ = FOSD-refl (marginal-reward s Bet 0)

------------------------------------------------------------------------
-- Full ModelPreservesFOSD
------------------------------------------------------------------------

middle-pointwise-fosd : PointwiseFOSD Middle Bet Quit
middle-pointwise-fosd zero    = middle-quit≤bet-0
middle-pointwise-fosd (suc n) = middle-quit≤bet-suc n

gambler-preserves : ModelPreservesFOSD gambler-rank
gambler-preserves Quit Bet Middle _ = middle-pointwise-fosd
gambler-preserves Quit Bet Ruin   ()
gambler-preserves Quit Bet Goal   ()
gambler-preserves Bet  Quit s ()
gambler-preserves Quit Quit s _ = pw-fosd-refl s Quit
gambler-preserves Bet  Bet  s _ = pw-fosd-refl s Bet
