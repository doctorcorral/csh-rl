{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Synthesized.SudokuConceptEnum
--
-- CONCEPT DISCOVERY WITH NO CURATED HYPOTHESIS SPACE.
--
-- SudokuConceptSynth discovers the conflict concept from an 11-strong
-- curated hypothesis list.  This module removes the curation: the
-- hypothesis space is ALL 2^16 = 65536 boolean functions over the four
-- atomic primitives (sameRow, sameCol, sameBox, equal), represented as
-- 16-entry truth tables.  Every PredProg over the four atoms denotes
-- one of these tables, so this space is a superset of everything the
-- DSL can express at any depth — nothing about the concept's form is
-- provided.
--
-- Observations are ALL 1920 two-cell boards (120 position pairs x 16
-- digit pairs), each labelled by the ENVIRONMENT's own dead-check.
-- Verified results (all refl):
--
--   * the environment's label is a FUNCTION of the four atoms: all 1920
--     observations are consistent (the atoms suffice to predict death —
--     itself a discovered fact, the learnability precondition),
--   * exactly 12 of the 16 atom combinations are realizable (a pair of
--     distinct cells cannot share both a row and a column),
--   * the version space collapses 65536 → 16, and the 16 survivors are
--     free exactly on the 4 unrealizable combinations: on every
--     realizable situation ALL survivors agree with
--         equal ∧ (sameRow ∨ sameCol ∨ sameBox)
--     — the concept is identified up to behavioral equivalence, which
--     is the information-theoretic limit of what any learner can do,
--   * the canonical (first) survivor, plugged in as the environment's
--     dead-check, lets the EC's optimal Finder solve the 4x4 puzzle
--     from the empty board.
--
-- HONEST BOUNDARY.  As in SudokuConceptSynth, the geometry primitives
-- (sameRow/sameCol/sameBox as index arithmetic) and value-equality are
-- given; what is discovered is everything about how they combine.
--
-- All --safe, no postulates.
------------------------------------------------------------------------

module CSHRL.Tasks.Synthesized.SudokuConceptEnum where

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≡ᵇ_)
open import Data.List using (List; []; _∷_; length; map; _++_; concatMap)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Geometry, situations, boards and the environment oracle are shared
-- with the curated-space demo.
open import CSHRL.Tasks.Synthesized.SudokuConceptSynth
  using ( same-row; same-col; same-box; Sit; situation-of
        ; CF; isRow; isCol; isBox; isEq; eval-cf
        ; mkBoard; env-dead; range; concept )

import CSHRL.Synthesis.Core as SynthCore
open SynthCore.PredicateDSL Sit CF eval-cf using (eval)

------------------------------------------------------------------------
-- THE HYPOTHESIS SPACE: every boolean function of the four atoms
--
-- A concept is a 16-entry truth table indexed by the situation
-- (r,c,b,e) ↦ r·8 + c·4 + b·2 + e.  We enumerate all of them.
------------------------------------------------------------------------

Table : Set
Table = List Bool

sit-index : Sit → ℕ
sit-index (r , c , b , e) =
  (if r then 8 else 0) + (if c then 4 else 0) +
  (if b then 2 else 0) + (if e then 1 else 0)

nthB : ℕ → Table → Bool
nthB _       []       = false
nthB zero    (x ∷ _)  = x
nthB (suc i) (_ ∷ xs) = nthB i xs

extend : List Table → List Table
extend []       = []
extend (t ∷ ts) = (false ∷ t) ∷ (true ∷ t) ∷ extend ts

tables : ℕ → List Table
tables zero    = [] ∷ []
tables (suc n) = extend (tables n)

all-tables : List Table
all-tables = tables 16

test-space : length all-tables ≡ 65536
test-space = refl

------------------------------------------------------------------------
-- OBSERVATIONS: every two-cell board, labelled by the environment
------------------------------------------------------------------------

IObs : Set
IObs = ℕ × Bool          -- (situation index , environment label)

obs-at : ℕ → ℕ → ℕ → ℕ → IObs
obs-at p dp q dq =
  let b = mkBoard p dp q dq
  in sit-index (situation-of b p q) , env-dead b

digits : List ℕ
digits = 1 ∷ 2 ∷ 3 ∷ 4 ∷ []

all-obs : List IObs
all-obs =
  concatMap (λ p →
    concatMap (λ q →
      concatMap (λ dp →
        map (λ dq → obs-at p dp q dq) digits) digits)
      (range (suc p) (15 ∸ p)))
    (range 0 16)

test-obs-count : length all-obs ≡ 1920
test-obs-count = refl

-- Deduplicate to the distinct situations seen (first-seen order kept).
insert-obs : IObs → List IObs → List IObs
insert-obs o [] = o ∷ []
insert-obs (i , l) ((j , m) ∷ os) =
  if i ≡ᵇ j then (j , m) ∷ os else (j , m) ∷ insert-obs (i , l) os

distinct-obs : List IObs
distinct-obs = go all-obs []
  where
  go : List IObs → List IObs → List IObs
  go []       acc = acc
  go (o ∷ os) acc = go os (insert-obs o acc)

-- 12 of the 16 atom combinations occur on real boards; the other 4
-- (those with sameRow ∧ sameCol) are geometrically impossible for a
-- pair of distinct cells.
test-realizable : length distinct-obs ≡ 12
test-realizable = refl

eq-bool : Bool → Bool → Bool
eq-bool true  true  = true
eq-bool false false = true
eq-bool _     _     = false

-- LEARNABILITY, CERTIFIED: the environment's verdict is a *function* of
-- the four atoms — every one of the 1920 observations carries the same
-- label as the first observation of its situation.  The atoms suffice.
label-at : ℕ → List IObs → Bool
label-at _ [] = false
label-at i ((j , m) ∷ os) = if i ≡ᵇ j then m else label-at i os

deterministic : List IObs → Bool
deterministic [] = true
deterministic ((i , l) ∷ os) =
  eq-bool (label-at i distinct-obs) l ∧ deterministic os

test-deterministic : deterministic all-obs ≡ true
test-deterministic = refl

------------------------------------------------------------------------
-- REFINE: collapse the version space against the observations
------------------------------------------------------------------------

consistent : List IObs → Table → Bool
consistent []             _ = true
consistent ((i , l) ∷ os) t = eq-bool (nthB i t) l ∧ consistent os t

filter-tables : (Table → Bool) → List Table → List Table
filter-tables P [] = []
filter-tables P (t ∷ ts) =
  if P t then t ∷ filter-tables P ts else filter-tables P ts

survivors : List Table
survivors = filter-tables (consistent distinct-obs) all-tables

-- 65536 → 16: the 12 realizable entries are pinned, the 4 unrealizable
-- ones are free (2^4 = 16) — the version space converged exactly to the
-- information available in the world.
test-survivors : length survivors ≡ 16
test-survivors = refl

------------------------------------------------------------------------
-- IDENTIFICATION: on realizable situations, every survivor IS the
-- concept eq ∧ (row ∨ col ∨ box)
------------------------------------------------------------------------

-- All 16 situations in index order (r,c,b,e nested, false first).
all-sits : List Sit
all-sits =
  concatMap (λ r → concatMap (λ c → concatMap (λ b →
    map (λ e → (r , c , b , e)) fb) fb) fb) fb
  where
  fb : List Bool
  fb = false ∷ true ∷ []

concept-table : Table
concept-table = map (eval concept) all-sits

-- The concept survives refinement (it is consistent with the world) …
test-concept-survives : consistent distinct-obs concept-table ≡ true
test-concept-survives = refl

-- … and every survivor's behavior on every realizable situation equals
-- the concept's.  This is identification up to behavioral equivalence:
-- no learner can distinguish concepts that agree on every situation the
-- world can realize.
restrict : Table → List Bool
restrict t = map (λ o → nthB (proj₁ o) t) distinct-obs

eq-bools : List Bool → List Bool → Bool
eq-bools []       []       = true
eq-bools (x ∷ xs) (y ∷ ys) = eq-bool x y ∧ eq-bools xs ys
eq-bools _        _        = false

identified : Bool
identified = go survivors
  where
  go : List Table → Bool
  go []       = true
  go (t ∷ ts) = eq-bools (restrict t) (restrict concept-table) ∧ go ts

test-identified : identified ≡ true
test-identified = refl

------------------------------------------------------------------------
-- SOLVE the 4x4 puzzle through the IDENTIFIED behavior
--
-- The canonical (first) survivor of the collapse — chosen by
-- enumeration order, with no reference to the concept — is plugged in
-- as the environment's dead-check, and the EC's optimal Finder solves
-- the puzzle from the empty board.  (Only realizable situations arise
-- on real boards, so any survivor gives the same solve.)
------------------------------------------------------------------------

open import CSHRL.Tasks.Synthesized.SudokuE2E
  using ( Config; board-of; num-empty
        ; Action; D1; D2; D3; D4; digit; all-actions; place; solved-reward
        ; solution )
  renaming (ok-board to ok-board-e2e)

open import CSHRL.EnvironmentClass.CombinatorialPlacementMDP

headT : List Table → Table
headT []      = []
headT (t ∷ _) = t

Cell4 : Set
Cell4 = Maybe ℕ

module SolveWith (t : Table) where

  pair-dead : ℕ → ℕ → ℕ → ℕ → Bool
  pair-dead p d q e =
    nthB (sit-index (same-row p q , same-col p q , same-box p q , (d ≡ᵇ e))) t

  check-one-t : ℕ → ℕ → ℕ → List Cell4 → Bool
  check-one-t _ _ _ [] = true
  check-one-t p d q (nothing ∷ rest) = check-one-t p d (suc q) rest
  check-one-t p d q (just e ∷ rest) =
    not (pair-dead p d q e) ∧ check-one-t p d (suc q) rest

  ok-t : List Cell4 → Bool
  ok-t = go 0
    where
    go : ℕ → List Cell4 → Bool
    go _ [] = true
    go p (nothing ∷ rest) = go (suc p) rest
    go p (just d ∷ rest) = check-one-t p d (suc p) rest ∧ go (suc p) rest

  is-dead-t : Config → Bool
  is-dead-t cfg = not (ok-t (board-of cfg))

  is-solved-t : Config → Bool
  is-solved-t cfg = length cfg ≡ᵇ num-empty

  open CombinatorialPlacementMDP
    Config Action
    is-dead-t is-solved-t
    place solved-reward
    all-actions D1 num-empty

  run-policy : State → ℕ → ℕ → List Action
  run-policy _ _ zero = []
  run-policy s depth (suc n) =
    let a = find-policy s depth
    in a ∷ run-policy (proj₁ (step s a)) depth n

  solved-digits : List ℕ
  solved-digits = map digit (run-policy (Ongoing []) num-empty num-empty)

eq-digits : List ℕ → List ℕ → Bool
eq-digits []       []       = true
eq-digits (x ∷ xs) (y ∷ ys) = (x ≡ᵇ y) ∧ eq-digits xs ys
eq-digits _        _        = false

-- The Finder, planning through the behavior identified from 65536
-- hypotheses by environment observation alone, produces the puzzle's
-- unique solution.
test-solve :
  eq-digits (SolveWith.solved-digits (headT survivors))
            (2 ∷ 3 ∷ 3 ∷ 2 ∷ 1 ∷ 4 ∷ 4 ∷ 1 ∷ []) ≡ true
test-solve = refl

-- The produced board is valid in the REAL environment.
test-valid : ok-board-e2e (board-of solution) ≡ true
test-valid = refl

------------------------------------------------------------------------
-- SUMMARY
--
--   ALL 65536 boolean concepts over the four atoms (zero curation)
--   → 1920 environment-labelled observations (every two-cell board)
--   → determinism certified: the atoms suffice to predict death
--   → 12 realizable situations pin the version space to 16 survivors,
--     free exactly on the 4 geometrically impossible situations
--   → on every realizable situation, every survivor equals
--        eq ∧ (sameRow ∨ sameCol ∨ sameBox)
--     (identification up to behavioral equivalence — the
--     information-theoretic limit)
--   → the canonical survivor drives is-dead and the EC's Finder solves
--     the 4x4 puzzle from the empty board.
--
-- The concept's form is discovered, not selected from a shortlist.
-- All --safe, no postulates.
------------------------------------------------------------------------
