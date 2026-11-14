{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- Propagation Curves: Verified Data for Cross-Pair Learning Plots
--
-- 4 actions, 3 features, 8 states (one per equivalence class).
-- Tracks version-space size and ranking accuracy at each observation
-- step, with every data point verified by refl.
--
-- Key result: the A>B accuracy curve from C-vs-D observations is
-- IDENTICAL to the curve from A-vs-B observations, because both
-- ranking pairs are governed by the same predicate (feat f₁).
------------------------------------------------------------------------

module CSHRL.Tasks.Synthesized.PropagationCurves where

open import Data.List using (List; []; _∷_; length; map)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import CSHRL.Synthesis.Core

------------------------------------------------------------------------
-- Domain: 8 states × 3 features = 8 equivalence classes
------------------------------------------------------------------------

data State : Set where
  s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ : State

data Action : Set where
  A B C D : Action

data Feature : Set where
  f₁ f₂ f₃ : Feature

-- Each state is a unique feature vector:
--   s₁ = (T,T,T)  s₂ = (T,T,F)  s₃ = (T,F,T)  s₄ = (T,F,F)
--   s₅ = (F,T,T)  s₆ = (F,T,F)  s₇ = (F,F,T)  s₈ = (F,F,F)
eval-feat : Feature → State → Bool
eval-feat f₁ s₁ = true
eval-feat f₁ s₂ = true
eval-feat f₁ s₃ = true
eval-feat f₁ s₄ = true
eval-feat f₁ s₅ = false
eval-feat f₁ s₆ = false
eval-feat f₁ s₇ = false
eval-feat f₁ s₈ = false
eval-feat f₂ s₁ = true
eval-feat f₂ s₂ = true
eval-feat f₂ s₃ = false
eval-feat f₂ s₄ = false
eval-feat f₂ s₅ = true
eval-feat f₂ s₆ = true
eval-feat f₂ s₇ = false
eval-feat f₂ s₈ = false
eval-feat f₃ s₁ = true
eval-feat f₃ s₂ = false
eval-feat f₃ s₃ = true
eval-feat f₃ s₄ = false
eval-feat f₃ s₅ = true
eval-feat f₃ s₆ = false
eval-feat f₃ s₇ = true
eval-feat f₃ s₈ = false

open PredicateDSL State Feature eval-feat
open CEGIS (f₁ ∷ f₂ ∷ f₃ ∷ [])

------------------------------------------------------------------------
-- Ranking structure:
--   prefer(A,B) = feat f₁    prefer(C,D) = feat f₁  (correlated!)
--   prefer(A,C) = feat f₂    prefer(B,D) = feat f₂  (correlated!)
--   prefer(B,C) = feat f₃
--   prefer(A,D) = feat f₁ ∧p feat f₂
--
-- The A>B and C>D rankings are governed by the SAME predicate.
-- CEGIS cannot distinguish which pair generated an observation.
------------------------------------------------------------------------

-- Target function for the A>B ranking
target : State → Bool
target = eval-feat f₁

all-states : List State
all-states = s₁ ∷ s₂ ∷ s₃ ∷ s₄ ∷ s₅ ∷ s₆ ∷ s₇ ∷ s₈ ∷ []

------------------------------------------------------------------------
-- Accuracy metric: count states where all VS survivors agree with
-- the target. When |VS| = 1, this is "the synthesized program is
-- correct at this state." When |VS| > 1, agreement means all
-- candidates give the same (correct) answer.
------------------------------------------------------------------------

private
  beq : Bool → Bool → Bool
  beq true  true  = true
  beq false false = true
  beq _     _     = false

unanimous : VersionSpace → State → Bool
unanimous []       s = true
unanimous (p ∷ ps) s = beq (eval p s) (target s) ∧ unanimous ps s

count : (State → Bool) → List State → ℕ
count _ []       = zero
count f (s ∷ ss) with f s
... | true  = suc (count f ss)
... | false = count f ss

accuracy : VersionSpace → ℕ
accuracy vs = count (unanimous vs) all-states

------------------------------------------------------------------------
-- SECTION 1: C-vs-D OBSERVATION SEQUENCE
--
-- We observe C vs D at each state. Since prefer(C,D) = feat f₁:
--   f₁ = T → C > D → PredObs (s, true)
--   f₁ = F → D > C → PredObs (s, false)
------------------------------------------------------------------------

vs₀ : VersionSpace
vs₀ = initial-vs 0

-- Initial: 5 programs, 0 states correctly determined
size₀ : length vs₀ ≡ 5
size₀ = refl
acc₀ : accuracy vs₀ ≡ 0
acc₀ = refl

-- Step 1: C > D at s₁ (T,T,T) → eliminates falsep
vs₁ : VersionSpace
vs₁ = refine vs₀ (s₁ , true)

size₁ : length vs₁ ≡ 4
size₁ = refl
acc₁ : accuracy vs₁ ≡ 1
acc₁ = refl

-- Step 2: C > D at s₂ (T,T,F) → eliminates feat f₃
vs₂ : VersionSpace
vs₂ = refine vs₁ (s₂ , true)

size₂ : length vs₂ ≡ 3
size₂ = refl
acc₂ : accuracy vs₂ ≡ 2
acc₂ = refl

-- Step 3: C > D at s₃ (T,F,T) → eliminates feat f₂
vs₃ : VersionSpace
vs₃ = refine vs₂ (s₃ , true)

size₃ : length vs₃ ≡ 2
size₃ = refl
acc₃ : accuracy vs₃ ≡ 4
acc₃ = refl

-- Step 4: C > D at s₄ (T,F,F) → NON-INFORMATIVE
-- Both truep and feat f₁ evaluate to true at s₄. No elimination.
vs₄ : VersionSpace
vs₄ = refine vs₃ (s₄ , true)

size₄ : length vs₄ ≡ 2
size₄ = refl
acc₄ : accuracy vs₄ ≡ 4
acc₄ = refl

-- Step 5: D > C at s₅ (F,T,T) → eliminates truep. CONVERGED!
vs₅ : VersionSpace
vs₅ = refine vs₄ (s₅ , false)

size₅ : length vs₅ ≡ 1
size₅ = refl
acc₅ : accuracy vs₅ ≡ 8
acc₅ = refl

-- Steps 6-8: all redundant after convergence
vs₆ : VersionSpace
vs₆ = refine vs₅ (s₆ , false)

size₆ : length vs₆ ≡ 1
size₆ = refl

vs₇ : VersionSpace
vs₇ = refine vs₆ (s₇ , false)

size₇ : length vs₇ ≡ 1
size₇ = refl

vs₈ : VersionSpace
vs₈ = refine vs₇ (s₈ , false)

size₈ : length vs₈ ≡ 1
size₈ = refl

-- The sole survivor is feat f₁
converged : vs₅ ≡ feat f₁ ∷ []
converged = refl

------------------------------------------------------------------------
-- SECTION 2: CROSS-PAIR IDENTITY
--
-- A-vs-B observations produce the EXACT SAME PredObs as C-vs-D,
-- because prefer(A,B) = prefer(C,D) = feat f₁.
-- At each state: eval(feat f₁, s) is the same regardless of
-- whether we're asking about A>B or C>D.
--
-- So the observation sequence is IDENTICAL:
--   C>D at s₁ → (s₁, true)  = A>B at s₁ → (s₁, true)
--   C>D at s₂ → (s₂, true)  = A>B at s₂ → (s₂, true)
--   D>C at s₅ → (s₅, false) = B>A at s₅ → (s₅, false)
--   etc.
--
-- The VS evolution, accuracy, and convergence are all identical.
------------------------------------------------------------------------

-- The C-vs-D and A-vs-B observation lists are the same value
cd-obs : List PredObs
cd-obs = (s₁ , true) ∷ (s₂ , true) ∷ (s₃ , true) ∷ (s₄ , true)
       ∷ (s₅ , false) ∷ (s₆ , false) ∷ (s₇ , false) ∷ (s₈ , false) ∷ []

ab-obs : List PredObs
ab-obs = map (λ s → s , eval-feat f₁ s) all-states

cross-pair-identity : cd-obs ≡ ab-obs
cross-pair-identity = refl

-- Therefore the full CEGIS runs are identical
cross-pair-vs : cegis-loop vs₀ cd-obs ≡ cegis-loop vs₀ ab-obs
cross-pair-vs = refl

------------------------------------------------------------------------
-- SECTION 3: VERIFIED PLOT DATA
--
-- Every row in this table is a theorem (verified by refl above).
--
-- Step | Obs source  | State | Bool  | |VS| | Accuracy | Note
-- -----|-------------|-------|-------|------|----------|--------
--  0   | —           | —     | —     |  5   |  0/8     | initial
--  1   | C>D (= A>B) | s₁    | true  |  4   |  1/8     | −falsep
--  2   | C>D (= A>B) | s₂    | true  |  3   |  2/8     | −feat f₃
--  3   | C>D (= A>B) | s₃    | true  |  2   |  4/8     | −feat f₂
--  4   | C>D (= A>B) | s₄    | true  |  2   |  4/8     | non-inform.
--  5   | D>C (= B>A) | s₅    | false |  1   |  8/8     | −truep ✓
--  6   | D>C (= B>A) | s₆    | false |  1   |  8/8     | redundant
--  7   | D>C (= B>A) | s₇    | false |  1   |  8/8     | redundant
--  8   | D>C (= B>A) | s₈    | false |  1   |  8/8     | redundant
------------------------------------------------------------------------
