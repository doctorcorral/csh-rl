{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Synthesized.QueensAutoE2E
--
-- N-QUEENS WITHOUT HAND-CRAFTED FEATURES
--
-- Complete feature discovery pipeline:
--
--   1. ENUMERATE: 23 candidate features (18 pairwise + 5 length)
--   2. FILTER:    Keep conflict indicators → 18 pairwise survive
--   3. REDUCE:    Eliminate atomics subsumed by composites → 6 pair-any
--   4. DISCOVER:  is-solved from solved/non-solved samples → len-is 4
--   5. SOLVE:     CPMDP EC produces [1,3,0,2] — same as hand-crafted
--
-- The concept of "attacks" EMERGES as pair-any (same-column OR
-- same-diagonal), without the human naming or defining it.
--
-- All --safe, no postulates.
------------------------------------------------------------------------

module CSHRL.Tasks.Synthesized.QueensAutoE2E where

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_; not)
open import Data.Nat  using (ℕ; zero; suc; _+_; _∸_; _≡ᵇ_; _⊔_; _≤_; z≤n; s≤s)
open import Data.List using (List; []; _∷_; length; map; _++_; concatMap)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import CSHRL.Synthesis.FeatureTemplate

------------------------------------------------------------------------
-- Domain: 4-Queens
------------------------------------------------------------------------

N : ℕ
N = 4

Config : Set
Config = List ℕ

data Action : Set where
  C0 C1 C2 C3 : Action

action-to-ℕ : Action → ℕ
action-to-ℕ C0 = 0
action-to-ℕ C1 = 1
action-to-ℕ C2 = 2
action-to-ℕ C3 = 3

all-actions : List Action
all-actions = C0 ∷ C1 ∷ C2 ∷ C3 ∷ []

place : Config → Action → Config
place xs a = xs ++ (action-to-ℕ a ∷ [])

solved-reward : ℕ
solved-reward = 100

------------------------------------------------------------------------
-- ═══════════════════════════════════════════════════════════════════
-- STAGE 1: ENUMERATE
-- ═══════════════════════════════════════════════════════════════════
------------------------------------------------------------------------

candidates : List ListNatFeature
candidates = enumerate-all N

-- 18 pairwise (vals-eq + spread-eq + pair-any for 6 pairs) + 5 length
test-candidates : length candidates ≡ 23
test-candidates = refl

------------------------------------------------------------------------
-- ═══════════════════════════════════════════════════════════════════
-- STAGE 2: FILTER against alive samples
-- ═══════════════════════════════════════════════════════════════════
------------------------------------------------------------------------

alive-samples : List Config
alive-samples =
  [] ∷
  (0 ∷ []) ∷
  (0 ∷ 2 ∷ []) ∷
  (1 ∷ 3 ∷ 0 ∷ []) ∷
  (1 ∷ 3 ∷ 0 ∷ 2 ∷ []) ∷
  []

discovered : List ListNatFeature
discovered = filter-by-alive alive-samples candidates

-- All 18 pairwise features survive; all 5 length features eliminated
test-discovered : length discovered ≡ 18
test-discovered = refl

------------------------------------------------------------------------
-- ═══════════════════════════════════════════════════════════════════
-- STAGE 3: ELIMINATE REDUNDANCY
-- ═══════════════════════════════════════════════════════════════════
--
-- vals-eq i j is subsumed by pair-any i j (same column ⟹ conflict)
-- spread-eq i j is subsumed by pair-any i j (same diagonal ⟹ conflict)
--
-- After elimination: 6 composite pair-any features survive.
-- Each pair-any i j IS the "attacks i j" concept — discovered, not
-- provided.
------------------------------------------------------------------------

reduced : List ListNatFeature
reduced = eliminate-redundant discovered

test-reduced : length reduced ≡ 6
test-reduced = refl

------------------------------------------------------------------------
-- ═══════════════════════════════════════════════════════════════════
-- STAGE 4: DISCOVER is-solved
-- ═══════════════════════════════════════════════════════════════════
------------------------------------------------------------------------

solved-samples : List Config
solved-samples =
  (1 ∷ 3 ∷ 0 ∷ 2 ∷ []) ∷
  (2 ∷ 0 ∷ 3 ∷ 1 ∷ []) ∷
  []

non-solved-samples : List Config
non-solved-samples =
  [] ∷
  (0 ∷ []) ∷
  (0 ∷ 2 ∷ []) ∷
  (1 ∷ 3 ∷ 0 ∷ []) ∷
  (0 ∷ 0 ∷ []) ∷
  []

solved-feats : List ListNatFeature
solved-feats = filter-solved solved-samples non-solved-samples candidates

-- Exactly one feature survives: len-is 4
test-solved : length solved-feats ≡ 1
test-solved = refl

------------------------------------------------------------------------
-- ═══════════════════════════════════════════════════════════════════
-- BUILD PREDICATES from discovered features
-- ═══════════════════════════════════════════════════════════════════
------------------------------------------------------------------------

import CSHRL.Synthesis.Core as SynthCore
open SynthCore.PredicateDSL Config ListNatFeature eval-list-feature

any-feat : List ListNatFeature → PredProg
any-feat []            = falsep
any-feat (f ∷ [])      = feat f
any-feat (f ∷ g ∷ fs)  = feat f ∨p any-feat (g ∷ fs)

-- is-dead from 6 reduced composite features (= "attacks" per pair)
is-dead-prog : PredProg
is-dead-prog = any-feat reduced

-- is-solved from discovered solved feature (= len-is 4)
is-solved-prog : PredProg
is-solved-prog = any-feat solved-feats

synth-is-dead : Config → Bool
synth-is-dead = eval is-dead-prog

synth-is-solved : Config → Bool
synth-is-solved = eval is-solved-prog

------------------------------------------------------------------------
-- Classification tests
------------------------------------------------------------------------

check-empty-dead   : synth-is-dead []  ≡ false
check-empty-dead   = refl

check-empty-solved : synth-is-solved [] ≡ false
check-empty-solved = refl

check-00-dead : synth-is-dead (0 ∷ 0 ∷ []) ≡ true
check-00-dead = refl

check-01-dead : synth-is-dead (0 ∷ 1 ∷ []) ≡ true
check-01-dead = refl

check-13-alive : synth-is-dead (1 ∷ 3 ∷ []) ≡ false
check-13-alive = refl

check-solution-dead : synth-is-dead (1 ∷ 3 ∷ 0 ∷ 2 ∷ []) ≡ false
check-solution-dead = refl

check-solution-solved : synth-is-solved (1 ∷ 3 ∷ 0 ∷ 2 ∷ []) ≡ true
check-solution-solved = refl

------------------------------------------------------------------------
-- ═══════════════════════════════════════════════════════════════════
-- FEATURE VECTORS AND EQUIVALENCE CLASSES
-- ═══════════════════════════════════════════════════════════════════
--
-- The feature vector maps a board to its Boolean fingerprint under
-- the discovered features.  |C/~| = number of distinct vectors.
------------------------------------------------------------------------

-- Boards with the same conflict pattern share feature vectors
test-fv-equiv : feature-vector reduced (0 ∷ 0 ∷ [])
              ≡ feature-vector reduced (1 ∷ 1 ∷ [])
test-fv-equiv = refl

-- Conflicting and non-conflicting boards have different vectors
test-fv-conflict : feature-vector reduced (0 ∷ 0 ∷ [])
  ≡ true ∷ false ∷ false ∷ false ∷ false ∷ false ∷ []
test-fv-conflict = refl

test-fv-alive : feature-vector reduced (0 ∷ 2 ∷ [])
  ≡ false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ []
test-fv-alive = refl

-- |C/~| on all 16 length-2 boards: exactly 2 equivalence classes
-- (conflicting vs non-conflicting)
boards-len2 : List Config
boards-len2 =
  concatMap (λ i → map (λ j → i ∷ j ∷ []) (range-from 0 N))
            (range-from 0 N)

test-boards-len2 : length boards-len2 ≡ 16
test-boards-len2 = refl

test-equiv-classes : equiv-classes reduced boards-len2 ≡ 2
test-equiv-classes = refl

------------------------------------------------------------------------
-- ═══════════════════════════════════════════════════════════════════
-- INSTANTIATE and SOLVE
-- ═══════════════════════════════════════════════════════════════════
------------------------------------------------------------------------

open import CSHRL.EnvironmentClass.CombinatorialPlacementMDP

open CombinatorialPlacementMDP
  Config Action
  synth-is-dead synth-is-solved
  place solved-reward
  all-actions C0 N

test-first-action : find-policy (Ongoing []) N ≡ C1
test-first-action = refl

run-policy : State → ℕ → ℕ → List Action
run-policy _ _ zero = []
run-policy s depth (suc n) =
  let a = find-policy s depth
  in a ∷ run-policy (proj₁ (step s a)) depth n

-- SAME SOLUTION as hand-crafted QueensE2E
test-solution : run-policy (Ongoing []) N N
  ≡ C1 ∷ C3 ∷ C0 ∷ C2 ∷ []
test-solution = refl

------------------------------------------------------------------------
-- ═══════════════════════════════════════════════════════════════════
-- PARTIAL COMPLETIONS — Resume from any partial optimal placement
-- ═══════════════════════════════════════════════════════════════════
--
-- The auto-discovered predicates (6 pair-any features + len-is 4)
-- generalize: they can complete ANY partial placement, not just
-- the one CEGIS was trained on.  These tests are identical to those
-- in the hand-crafted QueensE2E — confirming feature learning
-- reproduces the same generalization behavior.
------------------------------------------------------------------------

-- From 1-queen prefix [1]: complete to [3, 0, 2]
test-from-1 : run-policy (Ongoing (1 ∷ [])) N 3
  ≡ C3 ∷ C0 ∷ C2 ∷ []
test-from-1 = refl

-- From 2-queen prefix [1, 3]: complete to [0, 2]
test-from-2 : run-policy (Ongoing (1 ∷ 3 ∷ [])) N 2
  ≡ C0 ∷ C2 ∷ []
test-from-2 = refl

-- From 3-queen prefix [1, 3, 0]: complete to [2]
test-from-3 : run-policy (Ongoing (1 ∷ 3 ∷ 0 ∷ [])) N 1
  ≡ C2 ∷ []
test-from-3 = refl

-- The second 4-Queens solution: start with [2], complete to [0, 3, 1]
test-alt-solution : run-policy (Ongoing (2 ∷ [])) N 3
  ≡ C0 ∷ C3 ∷ C1 ∷ []
test-alt-solution = refl

-- Partial of the second solution: from [2, 0], complete to [3, 1]
test-alt-from-2 : run-policy (Ongoing (2 ∷ 0 ∷ [])) N 2
  ≡ C3 ∷ C1 ∷ []
test-alt-from-2 = refl

-- Partial of the second solution: from [2, 0, 3], complete to [1]
test-alt-from-3 : run-policy (Ongoing (2 ∷ 0 ∷ 3 ∷ [])) N 1
  ≡ C1 ∷ []
test-alt-from-3 = refl

-- Terminal state reached correctly
test-final-state :
  proj₁ (step (proj₁ (step (proj₁ (step (proj₁ (step (Ongoing []) C1)) C3)) C0)) C2)
  ≡ Solved (1 ∷ 3 ∷ 0 ∷ 2 ∷ [])
test-final-state = refl

test-alt-final-state :
  proj₁ (step (proj₁ (step (proj₁ (step (proj₁ (step (Ongoing []) C2)) C0)) C3)) C1)
  ≡ Solved (2 ∷ 0 ∷ 3 ∷ 1 ∷ [])
test-alt-final-state = refl

------------------------------------------------------------------------
-- ═══════════════════════════════════════════════════════════════════
-- INVALID PARTIALS — What happens from a doomed starting position?
-- ═══════════════════════════════════════════════════════════════════
--
-- The synthesized program handles invalid (conflicted) partial
-- placements gracefully.  All extensions of a dead board are
-- themselves dead, so the Finder sees uniform zero reward across
-- all actions and returns the default (C0).
------------------------------------------------------------------------

-- A richer rollout recording (action, resulting state)
run-trace : State → ℕ → ℕ → List (Action × State)
run-trace _ _ zero    = []
run-trace s depth (suc n) =
  let a  = find-policy s depth
      s' = proj₁ (step s a)
  in (a , s') ∷ run-trace s' depth n

-- Case 1: Start from [0,0] — column conflict already present.
-- Every extension inherits the conflict → immediate Dead.
-- The Finder returns C0 (default) since all actions are equivalent.
test-conflict-step : proj₁ (step (Ongoing (0 ∷ 0 ∷ [])) C0) ≡ Dead
test-conflict-step = refl

test-conflict-step2 : proj₁ (step (Ongoing (0 ∷ 0 ∷ [])) C3) ≡ Dead
test-conflict-step2 = refl

test-conflict-policy : run-policy (Ongoing (0 ∷ 0 ∷ [])) N 2
  ≡ C0 ∷ C0 ∷ []
test-conflict-policy = refl

test-conflict-trace : run-trace (Ongoing (0 ∷ 0 ∷ [])) N 2
  ≡ (C0 , Dead) ∷ (C0 , Dead) ∷ []
test-conflict-trace = refl

-- Case 2: Start from [0,1] — diagonal conflict.
-- Same behavior: immediate Dead for all extensions.
test-diag-conflict : synth-is-dead (0 ∷ 1 ∷ []) ≡ true
test-diag-conflict = refl

test-diag-trace : run-trace (Ongoing (0 ∷ 1 ∷ [])) N 2
  ≡ (C0 , Dead) ∷ (C0 , Dead) ∷ []
test-diag-trace = refl

-- Case 3: Start from [0] — valid but doomed.
-- No valid 4-Queens solution starts with queen at column 0.
-- The Finder places queens optimally given the constraint,
-- but all paths eventually reach Dead.
test-doomed-0 : run-policy (Ongoing (0 ∷ [])) N 3
  ≡ C0 ∷ C0 ∷ C0 ∷ []
test-doomed-0 = refl

test-doomed-0-trace : run-trace (Ongoing (0 ∷ [])) N 3
  ≡ (C0 , Dead) ∷
    (C0 , Dead) ∷
    (C0 , Dead) ∷ []
test-doomed-0-trace = refl

-- [0] → C0 → Dead immediately: column 0 is already taken
test-why-0-dead : synth-is-dead (0 ∷ 0 ∷ []) ≡ true
test-why-0-dead = refl

-- All actions from [0] lead to Dead (no valid 4-Queens solution from col 0)
test-0-C1 : proj₁ (step (Ongoing (0 ∷ [])) C1) ≡ Dead
test-0-C1 = refl

test-0-C2 : proj₁ (step (Ongoing (0 ∷ [])) C2)
  ≡ Ongoing (0 ∷ 2 ∷ [])
test-0-C2 = refl

test-0-C3 : proj₁ (step (Ongoing (0 ∷ [])) C3)
  ≡ Ongoing (0 ∷ 3 ∷ [])
test-0-C3 = refl

-- Case 4: Start from [3] — valid but no solution exists.
-- The Finder explores as far as it can.
test-doomed-3 : run-policy (Ongoing (3 ∷ [])) N 3
  ≡ C0 ∷ C0 ∷ C0 ∷ []
test-doomed-3 = refl

-- Check the states: from [3], the Finder explores but never finds Solved
test-doomed-3-trace : run-trace (Ongoing (3 ∷ [])) N 3
  ≡ (C0 , Ongoing (3 ∷ 0 ∷ [])) ∷
    (C0 , Dead) ∷
    (C0 , Dead) ∷ []
test-doomed-3-trace = refl

------------------------------------------------------------------------
-- ═══════════════════════════════════════════════════════════════════
-- VERIFY — Independent validation (not using synth predicates)
-- ═══════════════════════════════════════════════════════════════════
------------------------------------------------------------------------

private
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

test-valid : all-safe (1 ∷ 3 ∷ 0 ∷ 2 ∷ []) ≡ true
test-valid = refl

test-alt-valid : all-safe (2 ∷ 0 ∷ 3 ∷ 1 ∷ []) ≡ true
test-alt-valid = refl

------------------------------------------------------------------------
-- ═══════════════════════════════════════════════════════════════════
-- REWARD TRAJECTORIES — cumulative reward along the rollout
-- ═══════════════════════════════════════════════════════════════════
------------------------------------------------------------------------

collect-rewards : State → ℕ → ℕ → List ℕ
collect-rewards _ _ zero    = []
collect-rewards s depth (suc n) =
  let a       = find-policy s depth
      sr      = step s a
      s'      = proj₁ sr
      r       = proj₂ sr
  in r ∷ collect-rewards s' depth n

-- Valid starts: accumulate 0,0,0,solved-reward pattern
test-rewards-empty : collect-rewards (Ongoing []) N N
  ≡ 0 ∷ 0 ∷ 0 ∷ 100 ∷ []
test-rewards-empty = refl

test-rewards-from-1 : collect-rewards (Ongoing (1 ∷ [])) N 3
  ≡ 0 ∷ 0 ∷ 100 ∷ []
test-rewards-from-1 = refl

test-rewards-from-2 : collect-rewards (Ongoing (2 ∷ [])) N 3
  ≡ 0 ∷ 0 ∷ 100 ∷ []
test-rewards-from-2 = refl

test-rewards-from-13 : collect-rewards (Ongoing (1 ∷ 3 ∷ [])) N 2
  ≡ 0 ∷ 100 ∷ []
test-rewards-from-13 = refl

-- Doomed starts: all zeros (never reach Solved)
test-rewards-conflict : collect-rewards (Ongoing (0 ∷ 0 ∷ [])) N 2
  ≡ 0 ∷ 0 ∷ []
test-rewards-conflict = refl

test-rewards-doomed-0 : collect-rewards (Ongoing (0 ∷ [])) N 3
  ≡ 0 ∷ 0 ∷ 0 ∷ []
test-rewards-doomed-0 = refl

test-rewards-doomed-3 : collect-rewards (Ongoing (3 ∷ [])) N 3
  ≡ 0 ∷ 0 ∷ 0 ∷ []
test-rewards-doomed-3 = refl

-- Dead state: absorbing with zero reward
test-rewards-dead : collect-rewards Dead N 4
  ≡ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
test-rewards-dead = refl

-- Cumulative sums (for the plot)
private
  cumsum : List ℕ → List ℕ
  cumsum = go 0
    where
      go : ℕ → List ℕ → List ℕ
      go _ []       = []
      go acc (x ∷ xs) = (acc + x) ∷ go (acc + x) xs

test-cumsum-valid : cumsum (0 ∷ 0 ∷ 0 ∷ 100 ∷ [])
  ≡ 0 ∷ 0 ∷ 0 ∷ 100 ∷ []
test-cumsum-valid = refl

test-cumsum-doomed : cumsum (0 ∷ 0 ∷ 0 ∷ [])
  ≡ 0 ∷ 0 ∷ 0 ∷ []
test-cumsum-doomed = refl

------------------------------------------------------------------------
-- SUMMARY
--
-- The enhanced FTL pipeline:
--
--   23 candidates → 18 conflict indicators → 6 composite features
--                                          → 1 solved feature
--
-- Redundancy elimination discovers that "same-column" and
-- "same-diagonal" are both aspects of a single pairwise concept
-- (pair-any = the unnamed "attacks"), reducing the 18-way OR to
-- a 6-way OR that matches the hand-crafted version exactly.
--
-- is-solved is also discovered: len-is 4 is the only feature
-- true on all solved boards and false on all non-solved boards.
--
-- Feature vectors demonstrate |C/~|:
--   - On 16 length-2 boards, |C/~| = 2 (conflict vs no-conflict)
--   - Boards [0,0] and [1,1] share a vector (same equivalence class)
--   - Board [0,2] has a different vector (different class)
--
-- All --safe, no postulates.
------------------------------------------------------------------------
