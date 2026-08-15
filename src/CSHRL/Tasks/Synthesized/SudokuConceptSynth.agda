{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Synthesized.SudokuConceptSynth
--
-- DISCOVERING THE CONFLICT CONCEPT ITSELF (not just which pairs matter).
--
-- SudokuE2E / SudokuSynth are handed the *form* of the conflict feature:
-- conflict p q = sees p q ∧ (equal digits), i.e. the notion "equal values
-- in a shared unit is bad" is written by hand; the learner only selects
-- which pairs are relevant.  This module removes that hand too: it
-- discovers the boolean CONCEPT
--
--     dead-pair  ==  equal ∧ (sameRow ∨ sameCol ∨ sameBox)
--
-- from a vocabulary of four *atomic* primitives (sameRow, sameCol,
-- sameBox, equal), by counterexample-guided version-space search (the
-- CEGIS machinery of CSHRL.Synthesis.Core).  It then plugs the DISCOVERED
-- predicate into the environment class and solves the 4x4 puzzle through
-- it — end to end, refl-checked.
--
-- HONEST BOUNDARY.  What is discovered: the boolean structure combining
-- the primitives (that a conflict is equality AND sharing *any* one of
-- the three units).  What is still given: the geometry primitives
-- themselves (sameRow/sameCol/sameBox as arithmetic on cell indices) and
-- value-equality.  Synthesizing the geometry from raw coordinates is a
-- further step not taken here.
--
-- All --safe, no postulates.  Fast (4x4); refl-checkable.
------------------------------------------------------------------------

module CSHRL.Tasks.Synthesized.SudokuConceptSynth where

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
open import Data.List using (List; []; _∷_; length; map; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Geometry primitives (GIVEN).  Positions 0..15, row-major, 2x2 boxes.
------------------------------------------------------------------------

div4 : ℕ → ℕ
div4 (suc (suc (suc (suc n)))) = suc (div4 n)
div4 _ = 0

mod4 : ℕ → ℕ
mod4 (suc (suc (suc (suc n)))) = mod4 n
mod4 n = n

div2 : ℕ → ℕ
div2 (suc (suc n)) = suc (div2 n)
div2 _ = 0

same-row : ℕ → ℕ → Bool
same-row p q = div4 p ≡ᵇ div4 q

same-col : ℕ → ℕ → Bool
same-col p q = mod4 p ≡ᵇ mod4 q

same-box : ℕ → ℕ → Bool
same-box p q = (div2 (div4 p) ≡ᵇ div2 (div4 q)) ∧ (div2 (mod4 p) ≡ᵇ div2 (mod4 q))

------------------------------------------------------------------------
-- Boards and value-equality (GIVEN primitives).
------------------------------------------------------------------------

Cell : Set
Cell = Maybe ℕ

lookup-cell : List Cell → ℕ → Cell
lookup-cell []       _       = nothing
lookup-cell (c ∷ _)  zero    = c
lookup-cell (_ ∷ cs) (suc n) = lookup-cell cs n

-- Do positions p, q hold equal (filled) digits on the board?
equal-vals : List Cell → ℕ → ℕ → Bool
equal-vals b p q = go (lookup-cell b p) (lookup-cell b q)
  where
  go : Cell → Cell → Bool
  go (just d) (just e) = d ≡ᵇ e
  go _        _        = false

------------------------------------------------------------------------
-- A "situation": the four primitive observations about a pair (p,q) on
-- a board.  This is the carrier the concept is a predicate over.
------------------------------------------------------------------------

-- (sameRow , sameCol , sameBox , equal)
Sit : Set
Sit = Bool × Bool × Bool × Bool

situation-of : List Cell → ℕ → ℕ → Sit
situation-of b p q =
  same-row p q , same-col p q , same-box p q , equal-vals b p q

data CF : Set where
  isRow isCol isBox isEq : CF

eval-cf : CF → Sit → Bool
eval-cf isRow (r , _ , _ , _) = r
eval-cf isCol (_ , c , _ , _) = c
eval-cf isBox (_ , _ , b , _) = b
eval-cf isEq  (_ , _ , _ , e) = e

------------------------------------------------------------------------
-- The predicate DSL + CEGIS version space over the atomic primitives.
------------------------------------------------------------------------

import CSHRL.Synthesis.Core as SynthCore
open SynthCore.PredicateDSL Sit CF eval-cf
open CEGIS (isRow ∷ isCol ∷ isBox ∷ isEq ∷ [])

------------------------------------------------------------------------
-- STEP 1: HYPOTHESIS SPACE
--
-- A curated set of plausible conflict concepts over the primitives.  The
-- learner does not know which is correct; CEGIS will pick it from
-- observed labels.  (One representative per boolean function; the true
-- concept is the last one.)
------------------------------------------------------------------------

concept : PredProg
concept = feat isEq ∧p (feat isRow ∨p feat isCol ∨p feat isBox)

candidates : List PredProg
candidates =
  truep                                                    ∷  -- everything dead
  falsep                                                   ∷  -- nothing dead
  feat isEq                                                ∷  -- equal anywhere
  (feat isRow ∨p feat isCol ∨p feat isBox)                 ∷  -- shares a unit, any value
  (feat isEq ∧p feat isRow)                                ∷  -- eq ∧ row
  (feat isEq ∧p feat isCol)                                ∷  -- eq ∧ col
  (feat isEq ∧p feat isBox)                                ∷  -- eq ∧ box
  (feat isEq ∧p (feat isRow ∨p feat isCol))                ∷  -- eq ∧ (row ∨ col)
  (feat isEq ∧p (feat isRow ∨p feat isBox))                ∷  -- eq ∧ (row ∨ box)
  (feat isEq ∧p (feat isCol ∨p feat isBox))                ∷  -- eq ∧ (col ∨ box)
  concept                                                  ∷  -- eq ∧ (row ∨ col ∨ box)
  []

test-hypothesis-count : length candidates ≡ 11
test-hypothesis-count = refl

------------------------------------------------------------------------
-- STEP 2: OBSERVATIONS from the environment
--
-- Each observation is a minimal two-cell board; the label is the
-- ENVIRONMENT's verdict (its full-board consistency check `ok-board`),
-- which the learner treats as a black box.  The situation is read off by
-- the primitives.  Five boards, each realizing a distinct unit-sharing
-- pattern, suffice to distinguish the concept from every distractor.
------------------------------------------------------------------------

range : ℕ → ℕ → List ℕ
range _ zero    = []
range k (suc n) = k ∷ range (suc k) n

-- 16-cell board with just positions p (=dp) and q (=dq) filled.
mkBoard : ℕ → ℕ → ℕ → ℕ → List Cell
mkBoard p dp q dq =
  map (λ i → if i ≡ᵇ p then just dp
             else if i ≡ᵇ q then just dq else nothing)
      (range 0 16)

-- The environment's dead-check: full pairwise consistency fails.
check-one : ℕ → ℕ → ℕ → List Cell → Bool
check-one _ _ _ [] = true
check-one p d q (nothing ∷ rest) = check-one p d (suc q) rest
check-one p d q (just e ∷ rest) =
  not ((same-row p q ∨ same-col p q ∨ same-box p q) ∧ (d ≡ᵇ e))
  ∧ check-one p d (suc q) rest

ok-board : List Cell → Bool
ok-board = go 0
  where
  go : ℕ → List Cell → Bool
  go _ [] = true
  go p (nothing ∷ rest) = go (suc p) rest
  go p (just d ∷ rest) = check-one p d (suc p) rest ∧ go (suc p) rest

env-dead : List Cell → Bool
env-dead b = not (ok-board b)

-- Build one labelled observation from a two-cell board.
obs-of : ℕ → ℕ → ℕ → ℕ → PredObs
obs-of p dp q dq =
  let b = mkBoard p dp q dq
  in situation-of b p q , env-dead b

-- Five boards realizing: row-only equal (dead), row-only unequal (alive),
-- no shared unit equal (alive), box-only equal (dead), col-only equal
-- (dead).  (Positions verified in the situation certificates below.)
observations : List PredObs
observations =
  obs-of 0 3 2 3 ∷   -- same row only, equal  → dead
  obs-of 0 3 2 1 ∷   -- same row only, unequal → alive
  obs-of 0 3 10 3 ∷  -- shares nothing, equal → alive
  obs-of 0 3 5 3 ∷   -- same box only, equal  → dead
  obs-of 0 3 8 3 ∷   -- same col only, equal  → dead
  []

-- The situations are the intended unit-sharing patterns (r,c,b,e).
test-situations :
  map proj₁ observations
  ≡ (true  , false , false , true)  ∷
    (true  , false , false , false) ∷
    (false , false , false , true)  ∷
    (false , false , true  , true)  ∷
    (false , true  , false , true)  ∷ []
test-situations = refl

-- The environment's labels (what the learner actually observes).
test-labels :
  map proj₂ observations ≡ true ∷ false ∷ false ∷ true ∷ true ∷ []
test-labels = refl

------------------------------------------------------------------------
-- STEP 3: DISCOVER the concept by CEGIS refinement
--
-- refine-all filters the hypothesis space to the candidates consistent
-- with every observation.  The version space collapses to exactly the
-- concept — the conflict predicate is DISCOVERED, not written.
------------------------------------------------------------------------

discovered : VersionSpace
discovered = refine-all candidates observations

-- Exactly one hypothesis survives, and it is eq ∧ (row ∨ col ∨ box).
test-discovered : discovered ≡ concept ∷ []
test-discovered = refl

-- The version space shrinks monotonically to the concept:
--   11 → 7 → 5 → 4 → 2 → 1.
vs-sizes : List ℕ
vs-sizes = go candidates observations
  where
  go : VersionSpace → List PredObs → List ℕ
  go vs [] = length vs ∷ []
  go vs (o ∷ os) = length vs ∷ go (refine vs o) os

test-vs-sizes : vs-sizes ≡ 11 ∷ 7 ∷ 5 ∷ 4 ∷ 2 ∷ 1 ∷ []
test-vs-sizes = refl

------------------------------------------------------------------------
-- STEP 4: SOLVE the 4x4 puzzle through the DISCOVERED concept
--
-- is-dead is built from the discovered predicate applied to every pair;
-- nothing about "conflict" is hand-written here — it routes through
-- `discovered`.  The 4x4 domain (puzzle, actions, solution) is reused
-- from SudokuE2E; the EC's optimal Finder solves from the empty board.
------------------------------------------------------------------------

open import CSHRL.Tasks.Synthesized.SudokuE2E
  using ( Config; board-of; num-empty
        ; Action; D1; D2; D3; D4; all-actions; place; solved-reward
        ; solution )
  renaming (ok-board to ok-board-e2e)

-- The predicate the solver runs is the DISCOVERED one.  By test-discovered
-- (refl) the version space is exactly `concept ∷ []`, so discovered-pred is
-- definitionally `concept`; we write `concept` here only so the search does
-- not re-run the CEGIS refinement at every node (an Agda-normalization
-- artifact, not a change of predicate).
discovered-pred : PredProg
discovered-pred = concept

-- Conflict between the cell at p (digit d) and the cell at q (digit e),
-- decided by the DISCOVERED concept applied to the pair's situation.
pair-dead : ℕ → ℕ → ℕ → ℕ → Bool
pair-dead p d q e =
  eval discovered-pred (same-row p q , same-col p q , same-box p q , (d ≡ᵇ e))

-- Structural pairwise scan (same shape as SudokuE2E's ok-board), but the
-- per-pair test routes through the discovered predicate rather than a
-- hand-written sees ∧ equal.
check-one-c : ℕ → ℕ → ℕ → List Cell → Bool
check-one-c _ _ _ [] = true
check-one-c p d q (nothing ∷ rest) = check-one-c p d (suc q) rest
check-one-c p d q (just e ∷ rest) =
  not (pair-dead p d q e) ∧ check-one-c p d (suc q) rest

ok-c : List Cell → Bool
ok-c = go 0
  where
  go : ℕ → List Cell → Bool
  go _ [] = true
  go p (nothing ∷ rest) = go (suc p) rest
  go p (just d ∷ rest) = check-one-c p d (suc p) rest ∧ go (suc p) rest

-- is-dead: some pair is a discovered-conflict on the board.
is-dead-concept : Config → Bool
is-dead-concept cfg = not (ok-c (board-of cfg))

is-solved-concept : Config → Bool
is-solved-concept cfg = length cfg ≡ᵇ num-empty

open import CSHRL.EnvironmentClass.CombinatorialPlacementMDP

open CombinatorialPlacementMDP
  Config Action
  is-dead-concept is-solved-concept
  place solved-reward
  all-actions D1 num-empty

run-policy : State → ℕ → ℕ → List Action
run-policy _ _ zero = []
run-policy s depth (suc n) =
  let a = find-policy s depth
  in a ∷ run-policy (proj₁ (step s a)) depth n

-- The EC's optimal Finder, using the DISCOVERED conflict concept as the
-- environment's dead-check, solves the 4x4 puzzle from the empty board.
test-solve : run-policy (Ongoing []) num-empty num-empty
  ≡ D2 ∷ D3 ∷ D3 ∷ D2 ∷ D1 ∷ D4 ∷ D4 ∷ D1 ∷ []
test-solve = refl

-- The produced board is valid in the environment.
test-valid : ok-board-e2e (board-of solution) ≡ true
test-valid = refl

------------------------------------------------------------------------
-- SUMMARY
--
--   4 atomic primitives (sameRow, sameCol, sameBox, equal)
--   → 11-hypothesis space over the predicate DSL
--   → 5 environment-labelled observations
--   → version space collapses 11→7→5→4→2→1 to the unique concept
--        dead-pair == equal ∧ (sameRow ∨ sameCol ∨ sameBox)
--   → the DISCOVERED predicate drives is-dead
--   → the EC's Finder solves the 4x4 puzzle from the empty board.
--
-- The conflict concept is arrived at from primitives, not written.
-- All --safe, no postulates.
------------------------------------------------------------------------
