{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Learning.Base: Universal Learning Infrastructure
--
-- This module provides EC-independent definitions for the learning
-- process. It defines:
--   - Ranking type and totality
--   - Action availability
--   - Violation detection structure
--   - Learning loop skeleton
--
-- EC-specific modules instantiate these with concrete trace computations.
------------------------------------------------------------------------

module CSHRL.Learning.Base where

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)

------------------------------------------------------------------------
-- Universal Learning Module
--
-- Parameterized only by State, Action, and decidable action equality.
-- No reward structure or step function—those are EC-specific.
------------------------------------------------------------------------

module UniversalLearning
  (State Action : Set)
  (_≟ₐ_ : (a b : Action) → Dec (a ≡ b))
  where

  ------------------------------------------------------------------------
  -- Ranking Type
  --
  -- A ranking assigns a total order to actions in each state.
  -- Convention: rank s a b = true means "a is ranked ≤ b" (b is preferred or equal)
  ------------------------------------------------------------------------

  Ranking : Set
  Ranking = State → Action → Action → Bool

  ------------------------------------------------------------------------
  -- Action Availability
  --
  -- Models which actions are currently executable.
  ------------------------------------------------------------------------

  Available : Set
  Available = Action → Bool

  -- All actions available
  all-available : Available
  all-available = λ _ → true

  -- Make a specific action unavailable
  make-unavailable : Action → Available → Available
  make-unavailable unavail current = λ a → 
    current a ∧ (case a ≟ₐ unavail of λ { (yes _) → false ; (no _) → true })
    where
      case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
      case x of f = f x

  -- Filter list by availability
  filter-available : Available → List Action → List Action
  filter-available _ []       = []
  filter-available p (x ∷ xs) = 
    if p x then x ∷ filter-available p xs else filter-available p xs

  ------------------------------------------------------------------------
  -- List-to-Ranking Conversion
  --
  -- Convert a sorted list of actions (best first) to a ranking function.
  -- Convention: rank a b = true means "a ≤ b" (a is dominated by or equal to b)
  --
  -- If the list is [best, ..., worst], then:
  --   - rank worst best = true  (worst ≤ best)
  --   - rank best worst = false (best is NOT ≤ worst, it's better)
  ------------------------------------------------------------------------

  -- b appears before a in the list (b is ranked higher/better than a)
  -- Returns true if a ≤ b (a is dominated by b or equal)
  is-dominated-by : List Action → Action → Action → Bool
  is-dominated-by [] _ _ = true   -- Not in list, assume equal
  is-dominated-by (x ∷ xs) a b with a ≟ₐ x | b ≟ₐ x
  ... | yes _ | yes _ = true   -- a = b = x, so a ≤ b (equal)
  ... | yes _ | no  _ = false  -- a found first (a is better), so a ≤ b is FALSE
  ... | no  _ | yes _ = true   -- b found first (b is better), so a ≤ b is TRUE
  ... | no  _ | no  _ = is-dominated-by xs a b

  -- Convert ranking list to comparison function
  -- rank a b = true means a ≤ b (a is less than or equal to b in value)
  list-to-ranking : List Action → Action → Action → Bool
  list-to-ranking ranking a b = is-dominated-by ranking a b

  ------------------------------------------------------------------------
  -- Totality
  --
  -- A ranking is total if for all a, b: a ≤ b or b ≤ a
  ------------------------------------------------------------------------

  IsTotal : Ranking → State → Set
  IsTotal rank s = ∀ a b → rank s a b ≡ true ⊎ rank s b a ≡ true

  -- Helper: is-dominated-by is always total (either a ≤ b or b ≤ a)
  dominated-total : ∀ ranking a b → 
    is-dominated-by ranking a b ≡ true ⊎ 
    is-dominated-by ranking b a ≡ true
  dominated-total [] a b = inj₁ refl
  dominated-total (x ∷ xs) a b with a ≟ₐ x | b ≟ₐ x
  ... | yes _ | yes _ = inj₁ refl  -- a = b = x
  ... | yes _ | no  _ = inj₂ refl  -- a first, so b ≤ a
  ... | no  _ | yes _ = inj₁ refl  -- b first, so a ≤ b
  ... | no  _ | no  _ = dominated-total xs a b

  -- List-based rankings are always total
  list-ranking-total : ∀ ranking s → IsTotal (λ _ → list-to-ranking ranking) s
  list-ranking-total ranking s a b = dominated-total ranking a b

  ------------------------------------------------------------------------
  -- Violation Structure
  --
  -- A violation records where ranking disagrees with value ordering.
  -- The actual test is EC-specific (depends on trace/value computation).
  ------------------------------------------------------------------------

  record Violation : Set where
    constructor violation
    field
      viol-state  : State
      viol-better : Action  -- Should be ranked higher
      viol-worse  : Action  -- Should be ranked lower
      viol-depth  : ℕ       -- Depth at which violation detected

  ------------------------------------------------------------------------
  -- Sample Structure
  --
  -- A sample is a state and pair of actions to test.
  ------------------------------------------------------------------------

  record Sample : Set where
    constructor sample
    field
      sample-state : State
      sample-a     : Action
      sample-b     : Action

  ------------------------------------------------------------------------
  -- Abstract Learning Loop
  --
  -- The loop structure is universal; the violation test is EC-specific.
  ------------------------------------------------------------------------

  -- Learning step type: given test function, depth, sample → new depth
  LearnStep : Set
  LearnStep = (ℕ → Sample → Maybe Violation) → ℕ → Sample → ℕ

  -- Default implementation: increase depth on violation
  default-learn-step : LearnStep
  default-learn-step test depth s with test depth s
  ... | nothing = depth
  ... | just _  = suc depth

  -- Learning loop type
  LearnLoop : Set
  LearnLoop = (ℕ → Sample → Maybe Violation) → ℕ → List Sample → ℕ

  -- Default implementation: fold learn-step over samples
  default-learn-loop : LearnLoop
  default-learn-loop test depth []             = depth
  default-learn-loop test depth (s ∷ samples) = 
    default-learn-loop test (default-learn-step test depth s) samples

  ------------------------------------------------------------------------
  -- Convergence Structure
  --
  -- States that rankings stabilize at some depth.
  -- The proof is EC-specific.
  ------------------------------------------------------------------------

  ConvergesAt : (ℕ → Ranking) → Set
  ConvergesAt ranking-at = ∃[ k ] (∀ s a b → 
    ranking-at k s a b ≡ ranking-at (suc k) s a b)


