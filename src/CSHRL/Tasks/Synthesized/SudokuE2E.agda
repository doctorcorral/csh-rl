{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Synthesized.SudokuE2E
--
-- END-TO-END VERIFIED PIPELINE: Observations → 4x4 Sudoku Solution
--
-- Complete CPMDP demo showing the synthesis-critical path on Sudoku:
--
--   STEP 1. SYNTHESIZE – Build is-dead, is-solved as PredProg terms
--           (what CEGIS produces from board observations)
--   STEP 2. INSTANTIATE – Open the EC with synthesized predicates
--           (PredProg defines the step function → no hand-crafted logic)
--   STEP 3. SOLVE – EC's find-policy completes the puzzle
--   STEP 4. VERIFY – The completed board satisfies every constraint
--   STEP 5. CAPABILITY – The EC *knows* solvability: solve = R from
--           the empty board (the puzzle is solvable), and every wrong
--           digit yields a 0-valued successor (doom detection)
--   STEP 6. CEGIS DEMO – Two observations pin the conflict predicate
--
-- Same shape as QueensE2E: is-dead is a disjunction of pairwise
-- conflict features over the `sees` relation (row / column / box).
-- Synthesis is on the CRITICAL PATH: without the PredProg predicates
-- there is no step function and no Finder.
--
-- The puzzle (uniquely solvable 4x4 Sudoku, 8 givens):
--
--     1 . | . 4          1 2 | 3 4
--     . 4 | 1 .          3 4 | 1 2
--     ----+----   ==>    ----+----
--     2 . | . 3          2 1 | 4 3
--     . 3 | 2 .          4 3 | 2 1
--
-- All --safe, no postulates.
------------------------------------------------------------------------

module CSHRL.Tasks.Synthesized.SudokuE2E where

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≡ᵇ_)
open import Data.List using (List; []; _∷_; length; map; _++_; concatMap)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans)

------------------------------------------------------------------------
-- DOMAIN: 4x4 Sudoku
--
-- Positions 0..15 in row-major order.  A configuration is the list of
-- digits written into the empty cells so far (row-major fill order).
------------------------------------------------------------------------

private
  div4 : ℕ → ℕ
  div4 (suc (suc (suc (suc n)))) = suc (div4 n)
  div4 _ = 0

  mod4 : ℕ → ℕ
  mod4 (suc (suc (suc (suc n)))) = mod4 n
  mod4 n = n

  div2 : ℕ → ℕ
  div2 (suc (suc n)) = suc (div2 n)
  div2 _ = 0

-- Two positions see each other: same row, column, or 2x2 box.
sees : ℕ → ℕ → Bool
sees p q =
  (div4 p ≡ᵇ div4 q) ∨
  (mod4 p ≡ᵇ mod4 q) ∨
  ((div2 (div4 p) ≡ᵇ div2 (div4 q)) ∧ (div2 (mod4 p) ≡ᵇ div2 (mod4 q)))

Cell : Set
Cell = Maybe ℕ

template : List Cell
template =
  just 1  ∷ nothing ∷ nothing ∷ just 4  ∷
  nothing ∷ just 4  ∷ just 1  ∷ nothing ∷
  just 2  ∷ nothing ∷ nothing ∷ just 3  ∷
  nothing ∷ just 3  ∷ just 2  ∷ nothing ∷ []

num-empty : ℕ
num-empty = 8

Config : Set
Config = List ℕ

merge : List Cell → Config → List Cell
merge [] _ = []
merge (just d  ∷ t) cfg = just d ∷ merge t cfg
merge (nothing ∷ t) [] = nothing ∷ merge t []
merge (nothing ∷ t) (d ∷ cfg) = just d ∷ merge t cfg

board-of : Config → List Cell
board-of = merge template

lookup-cell : List Cell → ℕ → Cell
lookup-cell []       _       = nothing
lookup-cell (c ∷ _)  zero    = c
lookup-cell (_ ∷ cs) (suc n) = lookup-cell cs n

data Action : Set where
  D1 D2 D3 D4 : Action

digit : Action → ℕ
digit D1 = 1
digit D2 = 2
digit D3 = 3
digit D4 = 4

all-actions : List Action
all-actions = D1 ∷ D2 ∷ D3 ∷ D4 ∷ []

place : Config → Action → Config
place cfg a = cfg ++ (digit a ∷ [])

solved-reward : ℕ
solved-reward = 100

------------------------------------------------------------------------
-- FEATURES: Observable properties of a board
--
-- conflict p q — do the (filled) cells at positions p and q hold the
--                same digit while seeing each other?
-- filled-is n  — have exactly n empty cells been filled?
------------------------------------------------------------------------

data SFeature : Set where
  conflict  : ℕ → ℕ → SFeature
  filled-is : ℕ → SFeature

eval-sfeature : SFeature → Config → Bool
eval-sfeature (conflict p q) cfg = check (lookup-cell b p) (lookup-cell b q)
  where
  b : List Cell
  b = board-of cfg
  check : Cell → Cell → Bool
  check (just d) (just e) = sees p q ∧ (d ≡ᵇ e)
  check _        _        = false
eval-sfeature (filled-is n) cfg = length cfg ≡ᵇ n

------------------------------------------------------------------------
-- ═══════════════════════════════════════════════════════════════════
-- STEP 1: SYNTHESIZE — Build predicates as PredProg terms
-- ═══════════════════════════════════════════════════════════════════
--
-- is-dead = ∨ of conflict features over all seeing pairs p < q
-- is-solved = all num-empty cells filled
------------------------------------------------------------------------

import CSHRL.Synthesis.Core as SynthCore
open SynthCore.PredicateDSL Config SFeature eval-sfeature

any-feat : List SFeature → PredProg
any-feat []            = falsep
any-feat (f ∷ [])      = feat f
any-feat (f ∷ f₂ ∷ fs) = feat f ∨p any-feat (f₂ ∷ fs)

private
  range : ℕ → ℕ → List ℕ          -- from, count
  range _ zero    = []
  range k (suc n) = k ∷ range (suc k) n

  filterᵇ : (ℕ → Bool) → List ℕ → List ℕ
  filterᵇ f [] = []
  filterᵇ f (x ∷ xs) =
    if f x then x ∷ filterᵇ f xs else filterᵇ f xs

-- The 56 seeing pairs of the 4x4 grid (each cell sees 7 others).
conflict-feats : List SFeature
conflict-feats =
  concatMap
    (λ p → map (conflict p) (filterᵇ (sees p) (range (suc p) (15 ∸ p))))
    (range 0 16)

check-feat-count : length conflict-feats ≡ 56
check-feat-count = refl

-- The synthesized predicates (PredProg terms)
is-dead-prog : PredProg
is-dead-prog = any-feat conflict-feats

is-solved-prog : PredProg
is-solved-prog = feat (filled-is num-empty)

-- The Boolean classifiers derived from PredProg
synth-is-dead : Config → Bool
synth-is-dead = eval is-dead-prog

synth-is-solved : Config → Bool
synth-is-solved = eval is-solved-prog

------------------------------------------------------------------------
-- ═══════════════════════════════════════════════════════════════════
-- STEP 2: INSTANTIATE — Open the EC with synthesized predicates
-- ═══════════════════════════════════════════════════════════════════
------------------------------------------------------------------------

open import CSHRL.EnvironmentClass.CombinatorialPlacementMDP

open CombinatorialPlacementMDP
  Config Action
  synth-is-dead synth-is-solved
  place solved-reward
  all-actions D1 num-empty

------------------------------------------------------------------------
-- Computational sanity checks: synthesized predicates classify correctly
------------------------------------------------------------------------

-- Empty board: not dead, not solved
check-empty-dead : synth-is-dead [] ≡ false
check-empty-dead = refl

check-empty-solved : synth-is-solved [] ≡ false
check-empty-solved = refl

-- First empty cell is position 1 (row 0, col 1).
-- Digit 1 collides with the given 1 at position 0 (same row) → dead.
check-d1-dead : synth-is-dead (1 ∷ []) ≡ true
check-d1-dead = refl

-- Digit 3 collides with the given 3 at position 13 (same column) → dead.
check-d3-dead : synth-is-dead (3 ∷ []) ≡ true
check-d3-dead = refl

-- Digit 2 conflicts with nothing → alive (it is the solution digit).
check-d2-alive : synth-is-dead (2 ∷ []) ≡ false
check-d2-alive = refl

------------------------------------------------------------------------
-- ═══════════════════════════════════════════════════════════════════
-- STEP 3: SOLVE — EC's find-policy completes the puzzle
-- ═══════════════════════════════════════════════════════════════════
------------------------------------------------------------------------

-- The optimal first move: digit 2 for the first empty cell
test-first-move : find-policy (Ongoing []) num-empty ≡ D2
test-first-move = refl

run-policy : State → ℕ → ℕ → List Action
run-policy _ _ zero = []
run-policy s depth (suc n) =
  let a = find-policy s depth
  in a ∷ run-policy (proj₁ (step s a)) depth n

-- The synthesized EC fills all 8 empty cells with the unique solution
test-solution : run-policy (Ongoing []) num-empty num-empty
  ≡ D2 ∷ D3 ∷ D3 ∷ D2 ∷ D1 ∷ D4 ∷ D4 ∷ D1 ∷ []
test-solution = refl

-- Partial completion: resume from any solvable prefix
test-from-2 : run-policy (Ongoing (2 ∷ 3 ∷ [])) num-empty 6
  ≡ D3 ∷ D2 ∷ D1 ∷ D4 ∷ D4 ∷ D1 ∷ []
test-from-2 = refl

test-from-6 : run-policy (Ongoing (2 ∷ 3 ∷ 3 ∷ 2 ∷ 1 ∷ 4 ∷ [])) num-empty 2
  ≡ D4 ∷ D1 ∷ []
test-from-6 = refl

------------------------------------------------------------------------
-- ═══════════════════════════════════════════════════════════════════
-- STEP 4: VERIFY — The completed board satisfies every constraint
-- ═══════════════════════════════════════════════════════════════════
------------------------------------------------------------------------

-- Hand-written full-board check (independent of synthesis)
check-one : ℕ → ℕ → ℕ → List Cell → Bool
check-one _ _ _ [] = true
check-one p d q (nothing ∷ rest) = check-one p d (suc q) rest
check-one p d q (just e ∷ rest) =
  not (sees p q ∧ (d ≡ᵇ e)) ∧ check-one p d (suc q) rest

ok-board : List Cell → Bool
ok-board = go 0
  where
  go : ℕ → List Cell → Bool
  go _ [] = true
  go p (nothing ∷ rest) = go (suc p) rest
  go p (just d ∷ rest) = check-one p d (suc p) rest ∧ go (suc p) rest

solution : Config
solution = 2 ∷ 3 ∷ 3 ∷ 2 ∷ 1 ∷ 4 ∷ 4 ∷ 1 ∷ []

test-valid : ok-board (board-of solution) ≡ true
test-valid = refl

test-complete : synth-is-solved solution ≡ true
test-complete = refl

-- The rollout ends in the Solved state of the synthesized EC
test-final-state :
  proj₁ (step (Ongoing (2 ∷ 3 ∷ 3 ∷ 2 ∷ 1 ∷ 4 ∷ 4 ∷ [])) D1)
  ≡ Solved solution
test-final-state = refl

------------------------------------------------------------------------
-- ═══════════════════════════════════════════════════════════════════
-- STEP 5: CAPABILITY — The EC knows solvability and doom
-- ═══════════════════════════════════════════════════════════════════
--
-- solve s k is the capability profile: the best reward reachable from
-- s within k more steps.  The EC's own value function certifies that
-- the puzzle is solvable (solve = R from the empty board), and that
-- every wrong digit leads to a worthless successor (solve = 0), which
-- is how the Finder avoids doomed branches.
------------------------------------------------------------------------

-- The puzzle IS solvable: full reward reachable from the empty board
test-solvable : solve (Ongoing []) num-empty ≡ solved-reward
test-solvable = refl

-- A wrong first digit is doomed: its capability profile is 0 forever
-- (here it dies immediately; at depth num-empty nothing is recoverable)
test-doomed : solve (proj₁ (step (Ongoing []) D3)) num-empty ≡ 0
test-doomed = refl

------------------------------------------------------------------------
-- ═══════════════════════════════════════════════════════════════════
-- STEP 6: CEGIS DEMO — Synthesize the conflict predicate
-- ═══════════════════════════════════════════════════════════════════
--
-- With a small feature vocabulary, CEGIS pins the correct conflict
-- predicate from just 2 board observations.  With the full 56-feature
-- vocabulary, the same algorithm produces is-dead-prog.
------------------------------------------------------------------------

small-features : List SFeature
small-features = conflict 1 2 ∷ filled-is num-empty ∷ []

open CEGIS small-features

-- Initial version space: {truep, falsep, feat(conflict 1 2),
--                          feat(filled-is 8)}
check-initial-vs : length (initial-vs 0) ≡ 4
check-initial-vs = refl

-- Observation 1: writing 2 into both row-0 holes is dead
-- (positions 1 and 2 share row 0)
dead-obs : PredObs
dead-obs = (2 ∷ 2 ∷ []) , true

check-vs-after-dead : length (refine (initial-vs 0) dead-obs) ≡ 2
check-vs-after-dead = refl

-- Observation 2: the correct prefix [2, 3] is NOT dead
alive-obs : PredObs
alive-obs = (2 ∷ 3 ∷ []) , false

-- After 2 observations: only feat(conflict 1 2) survives
check-vs-after-both :
  length (cegis-loop (initial-vs 0) (dead-obs ∷ alive-obs ∷ [])) ≡ 1
check-vs-after-both = refl

------------------------------------------------------------------------
-- PROPAGATION BONUS: Observation transfer between boards
--
-- Configs [2,2] and [4,4] have the same conflict pattern on the pair
-- (1, 2): both write equal digits into the two row-0 holes.  Observing
-- that one is dead classifies the other for free.
------------------------------------------------------------------------

board₁ board₂ : Config
board₁ = 2 ∷ 2 ∷ []
board₂ = 4 ∷ 4 ∷ []

conflict-pred : PredProg
conflict-pred = feat (conflict 1 2)

equiv-boards : FeatureEquiv conflict-pred board₁ board₂
equiv-boards = refl

propagation-demo :
  eval conflict-pred board₁ ≡ true →
  eval conflict-pred board₂ ≡ true
propagation-demo obs =
  trans (sym (propagation conflict-pred board₁ board₂ equiv-boards)) obs

------------------------------------------------------------------------
-- SUMMARY
--
--   1. SYNTHESIZE: 56 conflict features → is-dead-prog; filled-is →
--      is-solved-prog (what CEGIS produces from board observations)
--   2. INSTANTIATE: the PredProg terms ARE the environment dynamics
--   3. SOLVE: find-policy fills all 8 cells with the unique solution
--   4. VERIFY: the completed board passes the independent check
--   5. CAPABILITY: solve certifies solvability (= R) and doom (= 0)
--   6. CEGIS: 2 observations pin the conflict predicate exactly
--
-- All --safe, no postulates.
------------------------------------------------------------------------
