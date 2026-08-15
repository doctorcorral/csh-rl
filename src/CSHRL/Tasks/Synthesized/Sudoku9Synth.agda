{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Synthesized.Sudoku9Synth
--
-- AUTOMATIC ENVIRONMENT SYNTHESIS AT FULL 9x9 SCALE.
--
-- SudokuSynth learns the 4x4 dynamics from scratch by online CEGIS.
-- This module does the same on the full 9x9 puzzle (38 givens, 43
-- holes, a 9^43-leaf raw game tree) and shows that the *cost of
-- arriving at the dynamics is linear*, not brute force:
--
--   WALK    – the learner starts blind (candidate is-dead = falsep) and
--             interacts with the environment: at each reachable board it
--             probes all nine digits and compares its prediction with
--             the observed outcome.
--   REFINE  – each disagreement is a counterexample; the vocabulary
--             features firing on the witness are absorbed into the
--             compact disjunctive candidate.
--   VERIFY  – a CEGAR sweep re-walks the environment and certifies the
--             learned candidate agrees with the true environment on every
--             reachable probe (no solution used; no counterexample left).
--   SOLVE   – a forward survival solver driven by the LEARNED is-dead is
--             run from the EMPTY board and produces the puzzle's unique
--             solution.  It receives no part of the answer.
--
-- Verified results (all refl, one combined boolean certificate
-- `test-outcome` so the 43-step walk is evaluated exactly once — see
-- the note above `outcome-ok`):
--   * the blind candidate mispredicts (motivates the loop),
--   * 344 counterexample observations are absorbed — 43 fill steps x 8
--     dead digits — versus a raw board space of 9^43 ~ 10^41.  The loop
--     pays only for disagreements: its cost is linear in horizon x
--     actions, the dissolution effect at full scale,
--   * 637 of the 810 vocabulary features are learned (the other 173
--     never fire on a reachable counterexample),
--   * the CEGAR sweep is clean (learned == environment everywhere
--     reachable), and
--   * the survival solver, run from the empty board through the learned
--     model, reproduces the unique solution.
--
-- SCOPE, HONESTLY.  The solve is genuine and from scratch, but it is a
-- one-step-survival policy, not the EC's depth-lookahead optimal Finder.
-- Survival suffices here *because this instance is conflict-forced*
-- (exactly one digit survives per cell).  A non-forced instance needs
-- the Finder's search; that Finder solves 4x4 from the empty board by
-- refl in SudokuSynth (run-policy (Ongoing []) 8 8 ≡ solution), but a
-- depth-43 rollout is beyond Agda's call-by-name normalizer (no sharing
-- of repeated subterms; unary naturals), so it cannot be normalized at
-- 9x9.  (The Rocq port runs the full 43-step optimal rollout of the
-- hand-written 9x9 instance by vm_compute, which is call-by-value with
-- sharing; here the point is that the *learned* model solves it.)
--
-- All --safe, no postulates.  With the single-boolean certificate the
-- whole module — learn, verify, solve — checks in ~40 seconds.
------------------------------------------------------------------------

module CSHRL.Tasks.Synthesized.Sudoku9Synth where

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; pred; _+_; _∸_; _≡ᵇ_)
open import Data.List using (List; []; _∷_; length; map; _++_; foldl; concatMap)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- DOMAIN: full 9x9 Sudoku (positions 0..80, row-major)
------------------------------------------------------------------------

div9 : ℕ → ℕ
div9 (suc (suc (suc (suc (suc (suc (suc (suc (suc n))))))))) = suc (div9 n)
div9 _ = 0

mod9 : ℕ → ℕ
mod9 (suc (suc (suc (suc (suc (suc (suc (suc (suc n))))))))) = mod9 n
mod9 n = n

div3 : ℕ → ℕ
div3 (suc (suc (suc n))) = suc (div3 n)
div3 _ = 0

-- Two positions see each other: same row, column, or 3x3 box.
sees : ℕ → ℕ → Bool
sees p q =
  (div9 p ≡ᵇ div9 q) ∨
  (mod9 p ≡ᵇ mod9 q) ∨
  ((div3 (div9 p) ≡ᵇ div3 (div9 q)) ∧ (div3 (mod9 p) ≡ᵇ div3 (mod9 q)))

Cell : Set
Cell = Maybe ℕ

-- The conflict-forced puzzle from CSHRL.Tasks.Verified.Sudoku9.
template : List Cell
template =
  -- row 0
  nothing ∷ nothing ∷ just 3  ∷ just 4  ∷ just 5  ∷ nothing ∷ just 7  ∷ just 8  ∷ nothing ∷
  -- row 1
  just 4  ∷ nothing ∷ just 6  ∷ nothing ∷ just 8  ∷ just 9  ∷ nothing ∷ nothing ∷ just 3  ∷
  -- row 2
  nothing ∷ nothing ∷ nothing ∷ just 1  ∷ just 2  ∷ nothing ∷ nothing ∷ nothing ∷ just 6  ∷
  -- row 3
  just 2  ∷ nothing ∷ just 4  ∷ nothing ∷ just 6  ∷ nothing ∷ nothing ∷ nothing ∷ just 1  ∷
  -- row 4
  nothing ∷ just 6  ∷ nothing ∷ just 8  ∷ just 9  ∷ just 1  ∷ just 2  ∷ nothing ∷ just 4  ∷
  -- row 5
  just 8  ∷ just 9  ∷ nothing ∷ nothing ∷ nothing ∷ nothing ∷ just 5  ∷ nothing ∷ nothing ∷
  -- row 6
  just 3  ∷ nothing ∷ nothing ∷ nothing ∷ nothing ∷ just 8  ∷ just 9  ∷ nothing ∷ nothing ∷
  -- row 7
  nothing ∷ just 7  ∷ nothing ∷ nothing ∷ just 1  ∷ nothing ∷ nothing ∷ nothing ∷ just 5  ∷
  -- row 8
  just 9  ∷ just 1  ∷ just 2  ∷ just 3  ∷ just 4  ∷ nothing ∷ nothing ∷ just 7  ∷ nothing ∷ []

num-empty : ℕ
num-empty = 43

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

nthℕ : ℕ → List ℕ → ℕ
nthℕ _       []       = 0
nthℕ zero    (x ∷ _)  = x
nthℕ (suc i) (_ ∷ xs) = nthℕ i xs

-- Positions of the empty cells, in row-major order.
holes-of : ℕ → List Cell → List ℕ
holes-of _ [] = []
holes-of p (nothing ∷ t) = p ∷ holes-of (suc p) t
holes-of p (just _  ∷ t) = holes-of (suc p) t

hole-positions : List ℕ
hole-positions = holes-of 0 template

data Action : Set where
  A1 A2 A3 A4 A5 A6 A7 A8 A9 : Action

digit : Action → ℕ
digit A1 = 1
digit A2 = 2
digit A3 = 3
digit A4 = 4
digit A5 = 5
digit A6 = 6
digit A7 = 7
digit A8 = 8
digit A9 = 9

all-actions : List Action
all-actions = A1 ∷ A2 ∷ A3 ∷ A4 ∷ A5 ∷ A6 ∷ A7 ∷ A8 ∷ A9 ∷ []

place : Config → Action → Config
place cfg a = cfg ++ (digit a ∷ [])

solved-reward : ℕ
solved-reward = 100

------------------------------------------------------------------------
-- Full-board consistency: the honest environment oracle
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- FEATURES and the predicate DSL (the synthesis vocabulary)
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

import CSHRL.Synthesis.Core as SynthCore
open SynthCore.PredicateDSL Config SFeature eval-sfeature

any-feat : List SFeature → PredProg
any-feat []            = falsep
any-feat (f ∷ [])      = feat f
any-feat (f ∷ f₂ ∷ fs) = feat f ∨p any-feat (f₂ ∷ fs)

private
  range : ℕ → ℕ → List ℕ
  range _ zero    = []
  range k (suc n) = k ∷ range (suc k) n

  filterᵇ : (ℕ → Bool) → List ℕ → List ℕ
  filterᵇ f [] = []
  filterᵇ f (x ∷ xs) =
    if f x then x ∷ filterᵇ f xs else filterᵇ f xs

-- The 810 seeing pairs of the 9x9 grid (each cell sees 20 others).
conflict-feats : List SFeature
conflict-feats =
  concatMap
    (λ p → map (conflict p) (filterᵇ (sees p) (range (suc p) (80 ∸ p))))
    (range 0 81)

check-feat-count : length conflict-feats ≡ 810
check-feat-count = refl

------------------------------------------------------------------------
-- The environment as a black box: place a digit, observe death
------------------------------------------------------------------------

env-is-dead : Config → Bool
env-is-dead cfg = not (ok-board (board-of cfg))

------------------------------------------------------------------------
-- Version-space refinement for the disjunctive fragment
--
-- The candidate is always  any-feat vs  for a learned feature list vs.
-- On a counterexample the vocabulary features firing on the witness are
-- appended.  Two facts about a forced-path walk keep this cheap and
-- exact (both confirmed by the run's refl certificates):
--
--   * only the just-placed cell can introduce a new conflict, so it
--     suffices to scan the features touching that cell (`touching`)
--     rather than the whole 810-feature vocabulary; the firing set is
--     identical;
--   * along the forced path each feature fires at exactly one
--     counterexample, so no membership/dedup test is needed — the
--     accumulated list is already duplicate-free (length 637).
------------------------------------------------------------------------

filter-feats : (SFeature → Bool) → List SFeature → List SFeature
filter-feats P [] = []
filter-feats P (f ∷ fs) =
  if P f then f ∷ filter-feats P fs else filter-feats P fs

-- Canonical (ascending) conflict feature for an unordered pair.
canon : ℕ → ℕ → SFeature
canon a b = if ltℕ a b then conflict a b else conflict b a
  where
  ltℕ : ℕ → ℕ → Bool
  ltℕ zero    (suc _) = true
  ltℕ _       zero    = false
  ltℕ (suc a) (suc b) = ltℕ a b

-- Candidate features touching a given cell (all pairs (lp, q), q ≠ lp).
touching : ℕ → List SFeature
touching lp =
  map (canon lp) (filter-ℕ (λ q → not (q ≡ᵇ lp)) (range 0 81))
  where
  filter-ℕ : (ℕ → Bool) → List ℕ → List ℕ
  filter-ℕ f [] = []
  filter-ℕ f (x ∷ xs) = if f x then x ∷ filter-ℕ f xs else filter-ℕ f xs

-- Vocabulary features firing on a witness board: the just-placed cell
-- (the last hole in the config) newly conflicts with a peer.
new-firing : Config → List SFeature
new-firing wit =
  filter-feats (λ f → eval-sfeature f wit) (touching lp)
  where
  lp : ℕ
  lp = nthℕ (pred (length wit)) hole-positions

-- The synthesized predicate as a PredProg artifact (a disjunction of
-- learned conflict features).  Its semantics is `eval is-dead-prog`;
-- `cand-is-dead` below computes exactly that, but builds the board once
-- per query instead of once per feature (eval-sfeature would rebuild
-- the 81-cell board 637 times), which is what makes the certificates
-- normalize in the type checker.
is-dead-prog : List SFeature → PredProg
is-dead-prog = any-feat

feat-fires : List Cell → ℕ → ℕ → Bool
feat-fires b p q = check (lookup-cell b p) (lookup-cell b q)
  where
  check : Cell → Cell → Bool
  check (just d) (just e) = sees p q ∧ (d ≡ᵇ e)
  check _        _        = false

any-fires : List Cell → List SFeature → Bool
any-fires b [] = false
any-fires b (conflict p q ∷ fs) = feat-fires b p q ∨ any-fires b fs
any-fires b (filled-is _ ∷ fs)  = any-fires b fs

cand-is-dead : List SFeature → Config → Bool
cand-is-dead vs cfg = any-fires (board-of cfg) vs

------------------------------------------------------------------------
-- Online CEGIS: walk the environment, absorb counterexamples
------------------------------------------------------------------------

LearnerState : Set
LearnerState = List SFeature × ℕ

-- A dead probe is a counterexample: along the forced path the candidate
-- never pre-predicts a fresh conflict (every earlier cell is
-- conflict-free), so "env dead" and "env dead ∧ candidate alive"
-- coincide — the observation count equals the number of dead probes.
probe : Config → LearnerState → Action → LearnerState
probe c (vs , n) a =
  let b = place c a in
  if env-is-dead b
    then (vs ++ new-firing b , suc n)
    else (vs , n)

probe-all : Config → LearnerState → LearnerState
probe-all c st = foldl (probe c) st all-actions

-- Advance along the first environment-alive action (interaction only).
first-alive : Config → Action
first-alive c = go all-actions
  where
  go : List Action → Action
  go [] = A1
  go (a ∷ as) = if env-is-dead (place c a) then go as else a

advance : Config → Config
advance c = place c (first-alive c)

walk : Config → LearnerState → ℕ → LearnerState
walk _ st zero = st
walk c st (suc n) = walk (advance c) (probe-all c st) n

learned : LearnerState
learned = walk [] ([] , 0) num-empty

synthesized : List SFeature
synthesized = proj₁ learned

------------------------------------------------------------------------
-- The loop is necessary: the blind candidate mispredicts
--
-- Digit 3 in the first hole (position 0) collides with the given 3 at
-- position 2 (same row and same box), so the environment kills it; the
-- empty candidate predicts alive.
------------------------------------------------------------------------

test-env-dies : env-is-dead (3 ∷ []) ≡ true
test-env-dies = refl

test-blind-wrong : cand-is-dead [] (3 ∷ []) ≡ false
test-blind-wrong = refl

synth-is-solved : Config → Bool
synth-is-solved = eval (feat (filled-is num-empty))

-- The unique solution of the puzzle (row-major over the 43 holes).
solution : Config
solution =
  1 ∷ 2 ∷ 6 ∷ 9 ∷ 5 ∷ 7 ∷ 1 ∷ 2 ∷ 7 ∷ 8 ∷ 9 ∷ 3 ∷ 4 ∷ 5 ∷ 3 ∷ 5 ∷ 7 ∷ 8 ∷
  9 ∷ 5 ∷ 7 ∷ 3 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 6 ∷ 7 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 1 ∷ 2 ∷ 6 ∷ 8 ∷
  9 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 8 ∷ []

------------------------------------------------------------------------
-- CEGAR verification sweep: no counterexample remains
--
-- Re-walk the environment along its own survival path and require the
-- learned candidate to agree with the observed outcome on every probe of
-- every reachable board.  This uses NO knowledge of the solution — it
-- walks by environment survival and compares the two classifiers.  A
-- clean sweep is the CEGAR fixpoint: the learned model has no remaining
-- counterexample against the true environment.
--
-- NOTE ON SHARING: the learned feature list is threaded as an explicit
-- PARAMETER (vs) through the sweep and the solver, and applied to the
-- walk's output exactly once, in `outcome-ok` below.  Referring to the
-- top-level `synthesized` inside these loops instead would re-unfold the
-- definition — and re-run the entire 43-step walk — at every one of the
-- ~800 calls, because Agda does not share top-level definition
-- unfoldings across occurrences.  An argument is a single shared thunk;
-- a definition occurrence is not.
------------------------------------------------------------------------

eq-bool : Bool → Bool → Bool
eq-bool true  true  = true
eq-bool false false = true
eq-bool _     _     = false

agree-all : List SFeature → Config → Bool
agree-all vs c = go all-actions
  where
  go : List Action → Bool
  go [] = true
  go (a ∷ as) =
    eq-bool (env-is-dead (place c a)) (cand-is-dead vs (place c a)) ∧ go as

verify : List SFeature → Config → ℕ → Bool
verify _  _ zero = true
verify vs c (suc n) = agree-all vs c ∧ verify vs (advance c) n

------------------------------------------------------------------------
-- SOLVE FROM SCRATCH through the LEARNED model
--
-- The solver is a forward one-step-survival policy driven by the LEARNED
-- is-dead: at each cell it takes the first action the *learned* model
-- does not classify as dead.  It receives NO part of the solution — it
-- produces all 43 digits from the empty board, and we then check the
-- result equals the puzzle's unique solution.
--
-- Honest scope: one-step survival suffices here *because this instance
-- is conflict-forced* (exactly one digit survives at each cell, so no
-- search or backtracking is needed).  A non-forced instance would need
-- the EC's depth-lookahead Finder; that Finder solves 4x4 from the empty
-- board by refl in SudokuSynth, but a depth-43 rollout is beyond Agda's
-- call-by-name normalizer, which is why 9x9 uses the survival solver.
------------------------------------------------------------------------

-- First action the LEARNED model deems alive (survival, no lookahead).
learned-alive : List SFeature → Config → Action
learned-alive vs c = go all-actions
  where
  go : List Action → Action
  go [] = A1
  go (a ∷ as) = if cand-is-dead vs (place c a) then go as else a

run-solver : List SFeature → Config → ℕ → Config
run-solver _  c zero    = c
run-solver vs c (suc n) = run-solver vs (place c (learned-alive vs c)) n

------------------------------------------------------------------------
-- THE COMBINED CERTIFICATE
--
-- Everything the run establishes, in one refl:
--
--   * 344 counterexample observations — 43 fill steps x 8 dead digits,
--     each observed dead once.  Compare the raw board space 9^43 ~ 10^41:
--     only disagreements are informative.
--   * 637 of the 810 vocabulary features forced into the candidate; the
--     other 173 never fire on a reachable counterexample and need never
--     be resolved.
--   * the CEGAR sweep over every reachable probe is clean, and
--   * the survival solver, from the EMPTY board, through the LEARNED
--     model only, produces the puzzle's unique solution.
--
-- The certificate is a SINGLE BOOLEAN (boolean reflection, as a
-- vm_compute proof in Rocq): the whole computation happens in one
-- evaluator run, inside which the learned list is one shared thunk, so
-- the walk is evaluated exactly once.  Returning a tuple of large
-- structures instead would let the conversion checker decompose the
-- comparison component-wise and reify unevaluated closures back into
-- syntax, duplicating — and re-running — the walk inside every
-- component (measured: the walk alone checks in seconds; the tuple
-- version of this certificate did not finish in hours).
------------------------------------------------------------------------

eq-config : Config → Config → Bool
eq-config []       []       = true
eq-config (x ∷ xs) (y ∷ ys) = (x ≡ᵇ y) ∧ eq-config xs ys
eq-config _        _        = false

outcome-ok : LearnerState → Bool
outcome-ok (vs , n) =
  (n ≡ᵇ 344) ∧ (length vs ≡ᵇ 637)
  ∧ verify vs [] num-empty
  ∧ eq-config (run-solver vs [] num-empty) solution

test-outcome : outcome-ok learned ≡ true
test-outcome = refl

------------------------------------------------------------------------
-- VERIFY: the produced board is valid and complete in the REAL env
------------------------------------------------------------------------

test-valid : ok-board (board-of solution) ≡ true
test-valid = refl

test-complete : synth-is-solved solution ≡ true
test-complete = refl

------------------------------------------------------------------------
-- SUMMARY
--
--   blind candidate → 344 environment counterexamples → 637 features →
--   CEGAR verify sweep clean (learned == environment on every reachable
--   probe, no solution used) → survival solver run from the EMPTY board
--   through the learned model produces the unique solution → board valid
--   in the real environment.
--
-- Cost of arriving at the dynamics: 43 x 9 = 387 environment probes,
-- linear in horizon x actions, against a 9^43 raw board space.  Nothing
-- brute-forced, nothing written by hand, and the solve receives no part
-- of the answer.  All --safe, no postulates.
------------------------------------------------------------------------
