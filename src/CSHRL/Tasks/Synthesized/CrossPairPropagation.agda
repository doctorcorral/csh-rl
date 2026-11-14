{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- Cross-Pair Propagation: Learn A > B by observing only C vs D
--
-- Demonstrates the deepest consequence of the Propagation Theorem:
-- CEGIS observations are pair-agnostic. When two ranking pairs are
-- governed by the same feature structure, observing one pair
-- determines the other — without ever directly comparing the
-- actions of interest.
--
-- Setup:
--   • 4 actions (A, B, C, D) — A,B are "top tier", C,D are "bottom"
--   • 2 features (f₁, f₂) — f₁ determines all rankings
--   • 6 states in 3 equivalence classes (2 states each)
--
-- Result:
--   • 2 observations about C vs D → pinpoints feat f₁
--   • feat f₁ correctly ranks A vs B at ALL 6 states
--   • Dissolution: equivalent states add zero information
--   • ALL 6 action pairs determined from 2 sub-optimal observations
------------------------------------------------------------------------

module CSHRL.Tasks.Synthesized.CrossPairPropagation where

open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Unit using (⊤; tt)

open import CSHRL.Synthesis.Core

------------------------------------------------------------------------
-- Domain: 6 states, 4 actions, 2 features
------------------------------------------------------------------------

data State : Set where
  s₁ s₂ s₃ s₄ s₅ s₆ : State

data Action : Set where
  A B C D : Action

data Feature : Set where
  f₁ f₂ : Feature

-- Feature evaluation: 3 equivalence classes of 2 states each
--   Class α (s₁, s₂): f₁ = T, f₂ = T
--   Class β (s₃, s₄): f₁ = F, f₂ = T
--   Class γ (s₅, s₆): f₁ = T, f₂ = F
eval-feat : Feature → State → Bool
eval-feat f₁ s₁ = true
eval-feat f₁ s₂ = true
eval-feat f₁ s₃ = false
eval-feat f₁ s₄ = false
eval-feat f₁ s₅ = true
eval-feat f₁ s₆ = true
eval-feat f₂ s₁ = true
eval-feat f₂ s₂ = true
eval-feat f₂ s₃ = true
eval-feat f₂ s₄ = true
eval-feat f₂ s₅ = false
eval-feat f₂ s₆ = false

open PredicateDSL State Feature eval-feat
open CEGIS (f₁ ∷ f₂ ∷ [])

------------------------------------------------------------------------
-- THE RANKING STRUCTURE
--
-- Feature f₁ determines the total ordering of all 4 actions:
--   f₁ = true  → A > B > C > D  (all 6 pairs: "first > second")
--   f₁ = false → D > C > B > A  (all 6 pairs: "second > first")
--
-- So prefer(A,B) = prefer(A,C) = prefer(A,D) = prefer(B,C)
--    = prefer(B,D) = prefer(C,D) = feat f₁
--
-- The crucial consequence: from CEGIS's perspective, a C-vs-D
-- observation at state s produces PredObs (s, eval (feat f₁) s),
-- which is IDENTICAL to what an A-vs-B observation would produce.
-- CEGIS cannot tell which pair was observed.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- SECTION 1: CEGIS WITH C-vs-D OBSERVATIONS ONLY
------------------------------------------------------------------------

-- Initial version space (depth 0): truep, falsep, feat f₁, feat f₂
vs₀ : VersionSpace
vs₀ = initial-vs 0

check-vs₀ : length vs₀ ≡ 4
check-vs₀ = refl

-- Observation 1: C > D at s₁ (class α, f₁=T)
-- Generates PredObs (s₁, true)
obs₁ : PredObs
obs₁ = s₁ , true

vs₁ : VersionSpace
vs₁ = refine vs₀ obs₁

-- falsep eliminated (evaluates to false at s₁)
check-vs₁ : length vs₁ ≡ 3
check-vs₁ = refl

-- Observation 2: D > C at s₃ (class β, f₁=F)
-- Generates PredObs (s₃, false)
obs₂ : PredObs
obs₂ = s₃ , false

vs₂ : VersionSpace
vs₂ = refine vs₁ obs₂

-- truep and feat f₂ eliminated → only feat f₁ survives
check-vs₂ : length vs₂ ≡ 1
check-vs₂ = refl

-- The sole survivor IS feat f₁
pinpointed : cegis-loop vs₀ (obs₁ ∷ obs₂ ∷ []) ≡ feat f₁ ∷ []
pinpointed = refl

------------------------------------------------------------------------
-- SECTION 2: THE PAYOFF — A > B FROM C > D
--
-- We never observed A vs B. We never observed A vs C, B vs C,
-- A vs D, or B vs D. We only observed C vs D.
--
-- Yet the surviving program feat f₁ correctly determines the
-- A-vs-B ranking at ALL 6 states:
------------------------------------------------------------------------

-- A > B at class α (f₁ = true)
ab-s₁ : eval (feat f₁) s₁ ≡ true
ab-s₁ = refl

ab-s₂ : eval (feat f₁) s₂ ≡ true
ab-s₂ = refl

-- B > A at class β (f₁ = false)
ab-s₃ : eval (feat f₁) s₃ ≡ false
ab-s₃ = refl

ab-s₄ : eval (feat f₁) s₄ ≡ false
ab-s₄ = refl

-- A > B at class γ (f₁ = true)
ab-s₅ : eval (feat f₁) s₅ ≡ true
ab-s₅ = refl

ab-s₆ : eval (feat f₁) s₆ ≡ true
ab-s₆ = refl

------------------------------------------------------------------------
-- In fact, ALL 6 ranking pairs are determined:
--
--   prefer(A,B) = prefer(A,C) = prefer(A,D) =
--   prefer(B,C) = prefer(B,D) = prefer(C,D) = feat f₁
--
-- Two sub-optimal observations → all 6 rankings at all 6 states.
-- Without propagation: 6 pairs × 6 states = 36 observations.
-- With propagation:    2 observations.
-- Savings factor: 18×.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- SECTION 3: DISSOLUTION — EQUIVALENT STATES ADD NOTHING
------------------------------------------------------------------------

-- s₁ and s₂ are feature-equivalent (both class α)
s₁≈s₂ : AllFeatAgree s₁ s₂
s₁≈s₂ f₁ = refl
s₁≈s₂ f₂ = refl

-- C > D at s₂ after C > D at s₁: provably no change
dissolution-α : refine (refine vs₀ (s₁ , true)) (s₂ , true)
              ≡ refine vs₀ (s₁ , true)
dissolution-α = refine-absorb vs₀ s₁ s₂ true s₁≈s₂

-- s₃ and s₄ are feature-equivalent (both class β)
s₃≈s₄ : AllFeatAgree s₃ s₄
s₃≈s₄ f₁ = refl
s₃≈s₄ f₂ = refl

-- D > C at s₄ after D > C at s₃: provably no change
dissolution-β : refine (refine vs₁ (s₃ , false)) (s₄ , false)
              ≡ refine vs₁ (s₃ , false)
dissolution-β = refine-absorb vs₁ s₃ s₄ false s₃≈s₄

-- s₅ and s₆ are feature-equivalent (both class γ)
s₅≈s₆ : AllFeatAgree s₅ s₆
s₅≈s₆ f₁ = refl
s₅≈s₆ f₂ = refl

------------------------------------------------------------------------
-- SECTION 4: EARLY CONVERGENCE
--
-- The tight bound says we MIGHT need |C/~| = 3 observations
-- (one per class). But the VS converged in just 2: classes α
-- and β were enough to eliminate all wrong programs.
--
-- Class γ (f₁=T, f₂=F) adds nothing because the VS already
-- contains only feat f₁, which is consistent at class γ.
------------------------------------------------------------------------

-- Observation at class γ is non-informative: VS already converged
class-γ-redundant : refine vs₂ (s₅ , true) ≡ vs₂
class-γ-redundant = refl

------------------------------------------------------------------------
-- SECTION 5: WHY THIS WORKS — THE CROSS-PAIR PRINCIPLE
--
-- Any PredProg evaluation is automatically feature-respecting
-- (this follows immediately from the Propagation Theorem).
-- When two rankings are determined by the same PredProg, their
-- observations are indistinguishable. CEGIS operates on PredObs
-- (carrier × bool) — it has no notion of "which pair" generated
-- the observation. So C-vs-D observations ARE A-vs-B observations
-- whenever both pairs share the same underlying predicate.
------------------------------------------------------------------------

-- Generic: any PredProg evaluation respects features
eval-respects : ∀ (p : PredProg) → FeatureRespects (λ s → eval p s)
eval-respects p c₁ c₂ afa =
  propagation p c₁ c₂ (all-agree→feat-equiv c₁ c₂ afa p)

------------------------------------------------------------------------
-- SECTION 6: SCALING PERSPECTIVE
--
-- With k actions, there are k(k-1)/2 ranking pairs.
-- If all pairs are governed by the same feature structure,
-- observing ANY pair gives information about ALL pairs.
--
--   k=2: 1 pair,  no cross-pair effect
--   k=3: 3 pairs, 1 observation covers 3 pairs
--   k=4: 6 pairs, 1 observation covers 6 pairs  ← this demo
--   k=n: n(n-1)/2 pairs, multiplicative savings
--
-- Combined with dissolution (m states per class → 1 observation
-- per class), the savings are:
--
--   Without propagation:  k(k-1)/2 × |States| observations
--   With propagation:     as few as |C/~| observations total
--
-- For this demo: 6 × 6 = 36 → 2. A factor of 18×.
------------------------------------------------------------------------
