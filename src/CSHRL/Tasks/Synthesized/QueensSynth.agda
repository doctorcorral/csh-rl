{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Synthesized.QueensSynth
--
-- Instantiates the CombinatorialPlacementMDP synthesis framework
-- on the N-Queens problem. Demonstrates:
--
--   1. Queen-specific features (pairwise attack checks)
--   2. is-dead expressed as PredProg (disjunction of attack features)
--   3. Computational correctness: synth-is-dead ≡ is-dead-config
--   4. THE PROPAGATION IN ACTION:
--      "Observing that board [0, 1] is Dead (diagonal attack)
--       automatically tells us that board [3, 4] is also Dead,
--       because they share the same attack feature."
--   5. EC integration via WithTruePredicates
------------------------------------------------------------------------

module CSHRL.Tasks.Synthesized.QueensSynth where

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≡ᵇ_; _⊔_; _≤_; z≤n; s≤s)
open import Data.List using (List; []; _∷_; length; map; _++_; foldr)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)
open import Data.Unit using (⊤; tt)

------------------------------------------------------------------------
-- Domain (matching Queens8)
------------------------------------------------------------------------

N : ℕ
N = 8

Config : Set
Config = List ℕ

data Action : Set where
  C0 C1 C2 C3 C4 C5 C6 C7 : Action

action-to-ℕ : Action → ℕ
action-to-ℕ C0 = 0
action-to-ℕ C1 = 1
action-to-ℕ C2 = 2
action-to-ℕ C3 = 3
action-to-ℕ C4 = 4
action-to-ℕ C5 = 5
action-to-ℕ C6 = 6
action-to-ℕ C7 = 7

all-actions : List Action
all-actions = C0 ∷ C1 ∷ C2 ∷ C3 ∷ C4 ∷ C5 ∷ C6 ∷ C7 ∷ []

default-action : Action
default-action = C0

place : Config → Action → Config
place xs a = xs ++ (action-to-ℕ a ∷ [])

solved-reward : ℕ
solved-reward = 100

horizon : ℕ
horizon = N

------------------------------------------------------------------------
-- True predicates (from Queens8, for correctness comparison)
------------------------------------------------------------------------

abs-diff : ℕ → ℕ → ℕ
abs-diff x y = (x ∸ y) + (y ∸ x)

all-safe : Config → Bool
all-safe = go 0
  where
    check-one : ℕ → ℕ → ℕ → Config → Bool
    check-one _ _ _ [] = true
    check-one r1 c1 r2 (c2 ∷ rest) =
      not ((c1 ≡ᵇ c2) ∨ (abs-diff r1 r2 ≡ᵇ abs-diff c1 c2))
      ∧ check-one r1 c1 (suc r2) rest

    go : ℕ → Config → Bool
    go _ [] = true
    go row (c ∷ rest) = check-one row c (suc row) rest ∧ go (suc row) rest

is-dead-config : Config → Bool
is-dead-config xs = not (all-safe xs)

is-solved-config : Config → Bool
is-solved-config xs = length xs ≡ᵇ N

------------------------------------------------------------------------
-- Open the Synthesis Framework
------------------------------------------------------------------------

open import CSHRL.Synthesis.CombinatorialPlacementMDP

open PlacementSynthesis
  Config Action place solved-reward all-actions default-action horizon

------------------------------------------------------------------------
-- QUEEN-SPECIFIC FEATURES
--
-- The atomic observable properties of a board configuration.
-- For queens, the key features are:
--   attacks i j  — do queens at rows i and j attack each other?
--   length-is n  — does the board have exactly n queens?
------------------------------------------------------------------------

private
  lookup-safe : List ℕ → ℕ → ℕ → ℕ
  lookup-safe []       _ d = d
  lookup-safe (x ∷ _)  zero    _ = x
  lookup-safe (_ ∷ xs) (suc n) d = lookup-safe xs n d

  has-index : List ℕ → ℕ → Bool
  has-index []       _       = false
  has-index (_ ∷ _)  zero    = true
  has-index (_ ∷ xs) (suc n) = has-index xs n

  check-attack : ℕ → ℕ → Config → Bool
  check-attack i j xs =
    let ci = lookup-safe xs i 0
        cj = lookup-safe xs j 0
    in (ci ≡ᵇ cj) ∨ (abs-diff i j ≡ᵇ abs-diff ci cj)

data QFeature : Set where
  attacks   : ℕ → ℕ → QFeature
  length-is : ℕ → QFeature

eval-qfeature : QFeature → Config → Bool
eval-qfeature (attacks i j) xs =
  has-index xs i ∧ has-index xs j ∧ check-attack i j xs
eval-qfeature (length-is n) xs = length xs ≡ᵇ n

------------------------------------------------------------------------
-- Open the Predicate DSL with Queen Features
------------------------------------------------------------------------

open WithDSL QFeature eval-qfeature

------------------------------------------------------------------------
-- BUILDING THE PREDICATES AS PredProg
------------------------------------------------------------------------

-- Fold a list of features into a disjunction
any-feat : List QFeature → PredProg
any-feat []           = falsep
any-feat (f ∷ [])     = feat f
any-feat (f ∷ f₂ ∷ fs) = feat f ∨p any-feat (f₂ ∷ fs)

-- All pairs (i, j) with i < j for indices 0..n-1
private
  pair-inner : ℕ → ℕ → ℕ → List (ℕ × ℕ)
  pair-inner _ _ zero    = []
  pair-inner i j (suc k) = (i , j) ∷ pair-inner i (suc j) k

  pair-outer : ℕ → ℕ → List (ℕ × ℕ)
  pair-outer _ zero          = []
  pair-outer _ (suc zero)    = []
  pair-outer i (suc (suc k)) =
    pair-inner i (suc i) (suc k) ++ pair-outer (suc i) (suc k)

all-pairs : ℕ → List (ℕ × ℕ)
all-pairs n = pair-outer 0 n

-- is-dead: any pair of queens attacks each other
is-dead-prog : PredProg
is-dead-prog = any-feat (map (λ { (i , j) → attacks i j }) (all-pairs N))

-- is-solved: exactly N queens placed
is-solved-prog : PredProg
is-solved-prog = feat (length-is N)

-- The synthesized model
queens-model : SynthModel
queens-model = record
  { dead-pred   = is-dead-prog
  ; solved-pred = is-solved-prog
  }

------------------------------------------------------------------------
-- COMPUTATIONAL CORRECTNESS
--
-- The synthesized predicates agree with the hand-written ones
-- on concrete boards. These are all proved by refl (computation).
------------------------------------------------------------------------

-- Safe boards: synth agrees with is-dead-config
test-safe-empty : synth-is-dead queens-model [] ≡ is-dead-config []
test-safe-empty = refl

test-safe-02 : synth-is-dead queens-model (0 ∷ 2 ∷ []) ≡ is-dead-config (0 ∷ 2 ∷ [])
test-safe-02 = refl

test-safe-047 : synth-is-dead queens-model (0 ∷ 4 ∷ 7 ∷ [])
              ≡ is-dead-config (0 ∷ 4 ∷ 7 ∷ [])
test-safe-047 = refl

-- Dead boards: synth agrees with is-dead-config
test-dead-01 : synth-is-dead queens-model (0 ∷ 1 ∷ []) ≡ is-dead-config (0 ∷ 1 ∷ [])
test-dead-01 = refl

test-dead-00 : synth-is-dead queens-model (0 ∷ 0 ∷ []) ≡ is-dead-config (0 ∷ 0 ∷ [])
test-dead-00 = refl

-- The known 8-Queens solution: synth correctly says NOT dead
test-solution-not-dead :
  synth-is-dead queens-model (0 ∷ 4 ∷ 7 ∷ 5 ∷ 2 ∷ 6 ∷ 1 ∷ 3 ∷ [])
  ≡ false
test-solution-not-dead = refl

-- The known 8-Queens solution: synth correctly says solved
test-solution-solved :
  synth-is-solved queens-model (0 ∷ 4 ∷ 7 ∷ 5 ∷ 2 ∷ 6 ∷ 1 ∷ 3 ∷ [])
  ≡ true
test-solution-solved = refl

------------------------------------------------------------------------
-- PROPAGATION DEMO 1: Single Feature
--
-- Two boards with the same diagonal attack pattern.
-- Board [0, 1]: queen at (0,0) and (1,1) — diagonal attack.
-- Board [3, 4]: queen at (0,3) and (1,4) — diagonal attack.
--
-- The feature "attacks 0 1" evaluates to true on BOTH boards.
-- By the propagation theorem, ANY predicate built from this
-- feature evaluates identically on both. One Dead observation
-- tells us about ALL boards with the same attack pattern.
------------------------------------------------------------------------

board-dead₁ : Config
board-dead₁ = 0 ∷ 1 ∷ []

board-dead₂ : Config
board-dead₂ = 3 ∷ 4 ∷ []

-- Both boards have the same attack on pair (0, 1)
attacks-01-equiv : eval-qfeature (attacks 0 1) board-dead₁
                 ≡ eval-qfeature (attacks 0 1) board-dead₂
attacks-01-equiv = refl

-- Feature equivalence for a single-feature predicate
demo-pred : PredProg
demo-pred = feat (attacks 0 1)

demo-feat-equiv : FeatureEquiv demo-pred board-dead₁ board-dead₂
demo-feat-equiv = refl

-- PROPAGATION: dead at [0, 1] implies dead at [3, 4]
demo-dead-propagates :
  eval demo-pred board-dead₁ ≡ true →
  eval demo-pred board-dead₂ ≡ true
demo-dead-propagates obs =
  trans (sym (propagation demo-pred board-dead₁ board-dead₂ demo-feat-equiv)) obs

-- Verification: both boards ARE dead by computation
verify-dead₁ : eval demo-pred board-dead₁ ≡ true
verify-dead₁ = refl

verify-dead₂ : eval demo-pred board-dead₂ ≡ true
verify-dead₂ = refl

------------------------------------------------------------------------
-- PROPAGATION DEMO 2: Multi-Feature Program
--
-- A two-feature predicate: attacks on pairs (0,1) and (1,2).
-- Two 3-queen boards with the SAME attack pattern on both pairs.
--
-- Board [0, 3, 1]: no attacks on (0,1) or (1,2)
-- Board [4, 7, 5]: no attacks on (0,1) or (1,2)
--
-- Even though the actual column values differ entirely,
-- the predicate evaluates identically on both.
------------------------------------------------------------------------

board-safe₁ : Config
board-safe₁ = 0 ∷ 3 ∷ 1 ∷ []

board-safe₂ : Config
board-safe₂ = 4 ∷ 7 ∷ 5 ∷ []

two-feat-pred : PredProg
two-feat-pred = feat (attacks 0 1) ∨p feat (attacks 1 2)

-- Feature equivalence: both features agree on both boards
two-feat-equiv : FeatureEquiv two-feat-pred board-safe₁ board-safe₂
two-feat-equiv = refl , refl

-- Propagation: same classification for both boards
two-feat-prop : eval two-feat-pred board-safe₁ ≡ eval two-feat-pred board-safe₂
two-feat-prop = propagation two-feat-pred board-safe₁ board-safe₂ two-feat-equiv

-- Both are safe (false) — verified by computation
two-feat-safe₁ : eval two-feat-pred board-safe₁ ≡ false
two-feat-safe₁ = refl

two-feat-safe₂ : eval two-feat-pred board-safe₂ ≡ false
two-feat-safe₂ = refl

------------------------------------------------------------------------
-- PROPAGATION DEMO 3: Mixed Attack Pattern
--
-- Board [0, 2, 1]: attacks on pair (0,2) — diagonal!
--   queen (0,0) vs (2,1): |0-1|=1, |0-2|=2. No.
--   BUT queen (1,2) vs (2,1): |2-1|=1, |1-2|=1. YES — diagonal attack!
-- Board [5, 7, 6]: same pattern on pair (1,2)
--   queen (1,7) vs (2,6): |7-6|=1, |1-2|=1. YES — diagonal attack!
--
-- Attack pair (1,2) is true on BOTH boards.
-- Propagation: if one board is dead, so is the other.
------------------------------------------------------------------------

board-mixed₁ : Config
board-mixed₁ = 0 ∷ 2 ∷ 1 ∷ []

board-mixed₂ : Config
board-mixed₂ = 5 ∷ 7 ∷ 6 ∷ []

mixed-pred : PredProg
mixed-pred = feat (attacks 1 2)

mixed-feat-equiv : FeatureEquiv mixed-pred board-mixed₁ board-mixed₂
mixed-feat-equiv = refl

-- Both boards are dead (attack on pair 1,2)
mixed-dead₁ : eval mixed-pred board-mixed₁ ≡ true
mixed-dead₁ = refl

mixed-dead₂ : eval mixed-pred board-mixed₂ ≡ true
mixed-dead₂ = refl

-- Propagation: dead observation transfers between boards
mixed-propagation :
  eval mixed-pred board-mixed₁ ≡ true →
  eval mixed-pred board-mixed₂ ≡ true
mixed-propagation obs =
  trans (sym (propagation mixed-pred board-mixed₁ board-mixed₂ mixed-feat-equiv))
        obs

------------------------------------------------------------------------
-- OBSERVATION CONSTRAINT PROPAGATION
--
-- The full framework theorem applied concretely:
-- A model consistent with a Dead observation at config c₁
-- is automatically consistent at ALL feature-equivalent configs.
------------------------------------------------------------------------

-- Build a model from the single-feature dead predicate
demo-model : SynthModel
demo-model = record
  { dead-pred   = demo-pred
  ; solved-pred = is-solved-prog
  }

-- Observation: board [0, 1] is dead
demo-obs-dead₁ : OutcomeConstraint
  (synth-is-dead demo-model) (synth-is-solved demo-model)
  board-dead₁ dead
demo-obs-dead₁ = refl

-- Feature equiv for the model's predicates
demo-model-dead-equiv :
  FeatureEquiv (SynthModel.dead-pred demo-model) board-dead₁ board-dead₂
demo-model-dead-equiv = refl

demo-model-solved-equiv :
  FeatureEquiv (SynthModel.solved-pred demo-model) board-dead₁ board-dead₂
demo-model-solved-equiv = refl

-- CONSTRAINT PROPAGATION: Dead at [0,1] → Dead at [3,4]
demo-obs-propagates : OutcomeConstraint
  (synth-is-dead demo-model) (synth-is-solved demo-model)
  board-dead₂ dead
demo-obs-propagates =
  obs-constraint-propagates demo-model
    board-dead₁ board-dead₂ dead
    demo-model-dead-equiv demo-model-solved-equiv
    demo-obs-dead₁

------------------------------------------------------------------------
-- EC INTEGRATION
--
-- When the synthesized predicates match the true predicates,
-- the synthesized step function equals the true step function.
-- This connects synthesis to the verified EC (Queens8).
------------------------------------------------------------------------

open WithTruePredicates is-dead-config is-solved-config

-- Pointwise correctness on specific boards (by computation)
step-correct-dead-board : ∀ a →
  synth-step queens-model (Ongoing (0 ∷ 0 ∷ [])) a
  ≡ make-step is-dead-config is-solved-config (Ongoing (0 ∷ 0 ∷ [])) a
step-correct-dead-board C0 = refl
step-correct-dead-board C1 = refl
step-correct-dead-board C2 = refl
step-correct-dead-board C3 = refl
step-correct-dead-board C4 = refl
step-correct-dead-board C5 = refl
step-correct-dead-board C6 = refl
step-correct-dead-board C7 = refl

step-correct-safe-board : ∀ a →
  synth-step queens-model (Ongoing (0 ∷ 2 ∷ [])) a
  ≡ make-step is-dead-config is-solved-config (Ongoing (0 ∷ 2 ∷ [])) a
step-correct-safe-board C0 = refl
step-correct-safe-board C1 = refl
step-correct-safe-board C2 = refl
step-correct-safe-board C3 = refl
step-correct-safe-board C4 = refl
step-correct-safe-board C5 = refl
step-correct-safe-board C6 = refl
step-correct-safe-board C7 = refl

------------------------------------------------------------------------
-- CEGIS DEMO
--
-- Uses the CEGIS loop to synthesize is-dead from observations.
--
-- Feature set: {attacks 0 1, length-is 8}
-- Initial VS at depth 0: {truep, falsep, feat(attacks 0 1), feat(length-is 8)}
--
-- Observations:
--   1. Board [0, 1]: dead (diagonal attack)
--      → dead obs: (board, true)  → eliminates falsep, feat(length-is 8)
--   2. Board [0, 2]: ongoing (no attack)
--      → dead obs: (board, false) → eliminates truep
--   After 2 obs: only feat(attacks 0 1) survives — correct!
------------------------------------------------------------------------

open import Data.Maybe using (Maybe; just; nothing)

small-features : List QFeature
small-features = attacks 0 1 ∷ length-is 8 ∷ []

open WithCEGIS small-features

-- Observations as PlacementObs
obs-dead-01 : PlacementObs
obs-dead-01 = pobs [] C0 (0 ∷ []) ongoing

obs-dead-board : PlacementObs
obs-dead-board = pobs (0 ∷ []) C1 (0 ∷ 1 ∷ []) dead

obs-safe-board : PlacementObs
obs-safe-board = pobs (0 ∷ []) C2 (0 ∷ 2 ∷ []) ongoing

-- Initial version space size at depth 0: 4 atoms
test-initial-vs : length (initial-vs 0) ≡ 4
test-initial-vs = refl

-- After one dead observation: VS shrinks
test-dead-vs-1 : dead-vs-size 0 (obs-dead-board ∷ []) ≡ 2
test-dead-vs-1 = refl

-- After two dead observations: VS shrinks further
test-dead-vs-2 :
  dead-vs-size 0 (obs-dead-board ∷ obs-safe-board ∷ []) ≡ 1
test-dead-vs-2 = refl

-- Without a solved observation, the solved predicate defaults to falsep
-- (first consistent candidate). Adding a solved observation disambiguates.
test-cegis-partial :
  cegis-synth 0 (obs-dead-board ∷ obs-safe-board ∷ [])
  ≡ just (record { dead-pred = feat (attacks 0 1)
                  ; solved-pred = falsep })
test-cegis-partial = refl

-- Add a "solved" observation to refine the solved predicate.
-- We use an 8-queen solution board as the solved config.
obs-solved-board : PlacementObs
obs-solved-board = pobs
  (0 ∷ 4 ∷ 7 ∷ 5 ∷ 2 ∷ 6 ∷ 1 ∷ [])   -- 7-queen prefix
  C3                                      -- place queen at col 3
  (0 ∷ 4 ∷ 7 ∷ 5 ∷ 2 ∷ 6 ∷ 1 ∷ 3 ∷ []) -- 8-queen solution
  solved

-- Full pipeline: 3 observations pin both predicates exactly
test-cegis-full :
  cegis-synth 0 (obs-dead-board ∷ obs-safe-board ∷ obs-solved-board ∷ [])
  ≡ just (record { dead-pred = feat (attacks 0 1)
                  ; solved-pred = feat (length-is 8) })
test-cegis-full = refl

------------------------------------------------------------------------
-- PROPAGATION QUANTIFICATION DEMO
--
-- Boards [0, 1] and [3, 4] share the same attack feature on pair (0,1).
-- We prove:
--   1. They are AllFeatAgree on our small feature set
--   2. Refining the dead VS at [0,1] produces the same result as [3,4]
--   3. After observing [0,1], observing [3,4] is a proven no-op
--   4. An entire class of equivalent boards is dissolved by one obs
------------------------------------------------------------------------

-- The two boards with the same diagonal attack pattern
board₁ : Config
board₁ = 0 ∷ 1 ∷ []

board₂ : Config
board₂ = 3 ∷ 4 ∷ []

-- All features agree: both boards have the same attack pattern
-- and the same length
boards-agree : AllFeatAgree board₁ board₂
boards-agree (attacks zero zero)              = refl
boards-agree (attacks zero (suc zero))        = refl
boards-agree (attacks zero (suc (suc _)))     = refl
boards-agree (attacks (suc zero) zero)        = refl
boards-agree (attacks (suc zero) (suc zero))  = refl
boards-agree (attacks (suc zero) (suc (suc _))) = refl
boards-agree (attacks (suc (suc _)) _)        = refl
boards-agree (length-is zero)                 = refl
boards-agree (length-is (suc zero))           = refl
boards-agree (length-is (suc (suc zero)))     = refl
boards-agree (length-is (suc (suc (suc _))))  = refl

-- THEOREM 1 INSTANTIATED: Same refinement at equivalent boards
-- The dead version space after observing board₁ equals the
-- dead version space after observing board₂.
demo-refine-equiv :
  refine (initial-vs 0) (board₁ , true)
  ≡ refine (initial-vs 0) (board₂ , true)
demo-refine-equiv =
  refine-equiv (initial-vs 0) board₁ board₂ true boards-agree

-- Computational verification: both produce the same 2-element VS
demo-refine-board₁ :
  length (refine (initial-vs 0) (board₁ , true)) ≡ 2
demo-refine-board₁ = refl

demo-refine-board₂ :
  length (refine (initial-vs 0) (board₂ , true)) ≡ 2
demo-refine-board₂ = refl

-- THEOREM 2 INSTANTIATED: Second observation is a no-op
-- After observing board₁ is dead, observing board₂ is dead
-- adds NO information — the version space is unchanged.
demo-subsumption :
  refine (refine (initial-vs 0) (board₁ , true)) (board₂ , true)
  ≡ refine (initial-vs 0) (board₁ , true)
demo-subsumption =
  refine-absorb (initial-vs 0) board₁ board₂ true boards-agree

-- Computational verification: still 2 candidates after redundant obs
demo-subsumption-size :
  length (refine (refine (initial-vs 0) (board₁ , true)) (board₂ , true))
  ≡ 2
demo-subsumption-size = refl

-- THEOREM 3 INSTANTIATED: Entire equivalence class dissolved
-- Board [6, 7] also has the same diagonal attack pattern.
-- After observing board₁, ALL equivalent boards are handled for free.
board₃ : Config
board₃ = 6 ∷ 7 ∷ []

boards₁₃-agree : AllFeatAgree board₁ board₃
boards₁₃-agree (attacks zero zero)              = refl
boards₁₃-agree (attacks zero (suc zero))        = refl
boards₁₃-agree (attacks zero (suc (suc _)))     = refl
boards₁₃-agree (attacks (suc zero) zero)        = refl
boards₁₃-agree (attacks (suc zero) (suc zero))  = refl
boards₁₃-agree (attacks (suc zero) (suc (suc _))) = refl
boards₁₃-agree (attacks (suc (suc _)) _)        = refl
boards₁₃-agree (length-is zero)                 = refl
boards₁₃-agree (length-is (suc zero))           = refl
boards₁₃-agree (length-is (suc (suc zero)))     = refl
boards₁₃-agree (length-is (suc (suc (suc _))))  = refl

-- Dissolution: observing at board₂ and board₃ after board₁
-- leaves the version space unchanged — both are free.
demo-dissolution :
  cegis-loop
    (refine (initial-vs 0) (board₁ , true))
    ((board₂ , true) ∷ (board₃ , true) ∷ [])
  ≡ refine (initial-vs 0) (board₁ , true)
demo-dissolution =
  exploration-dissolution (initial-vs 0) board₁ true
    (board₂ ∷ board₃ ∷ [])
    (boards-agree , boards₁₃-agree , tt)

-- Computational verification: 2 redundant observations, still 2 candidates
demo-dissolution-size :
  length (cegis-loop
    (refine (initial-vs 0) (board₁ , true))
    ((board₂ , true) ∷ (board₃ , true) ∷ []))
  ≡ 2
demo-dissolution-size = refl
