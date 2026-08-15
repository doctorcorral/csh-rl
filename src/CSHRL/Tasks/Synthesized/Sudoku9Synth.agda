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
--   VERIFY  – the learned model is shown conflict-forced to exactly the
--             same solution as the environment: the candidate agrees
--             with the environment on every reachable probe (the CEGAR
--             fixpoint, no counterexample left).
--   SOLVE   – that same forcedness means every empty cell has a unique
--             surviving digit under the LEARNED dynamics, and the Finder
--             fills the final cells with the solution.
--
-- Verified results (all refl):
--   * the blind candidate mispredicts (motivates the loop),
--   * 344 counterexample observations are absorbed — 43 fill steps x 8
--     dead digits — versus a raw board space of 9^43 ~ 10^41.  The loop
--     pays only for disagreements: its cost is linear in horizon x
--     actions, the dissolution effect at full scale,
--   * 637 of the 810 vocabulary features are learned (the other 173
--     never fire on a reachable counterexample),
--   * the learned model is conflict-forced to the same solution as the
--     environment (candidate == environment on every reachable probe:
--     the CEGAR fixpoint, no remaining counterexample), and a
--     shallow-lookahead Finder rollout fills the last cells with the
--     solution.
--
-- WHY forcedness + a tail rollout, rather than a full 43-step
-- find-policy rollout: certifying a rollout by refl makes the type
-- checker execute a depth-43 lookahead search.  Agda's conversion
-- checker reduces call-by-name with no sharing of repeated subterms and
-- uses unary naturals, so the branching-9, depth-43 search re-expands
-- exponentially.  Forcedness is a flat 43x9 scan with no nested
-- lookahead; together with the placement trace bridge (see
-- CSHRL.Tasks.Verified.Sudoku9 and ports/*/Placement) it pins the full
-- policy mathematically.  (The Rocq port executes the full 43-step
-- rollout by vm_compute, which is call-by-value with sharing.)
--
-- All --safe, no postulates.  Heavy normalization: run in the slow CI
-- lane, not the main All.agda build.
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

------------------------------------------------------------------------
-- What the run discovered (all by refl):
--
--   * 344 counterexample observations — 43 fill steps x 8 dead digits,
--     each observed dead once.  Compare the raw board space 9^43 ~ 10^41:
--     only disagreements are informative.
--   * 637 of the 810 vocabulary features forced into the candidate; the
--     other 173 never fire on a reachable counterexample and need never
--     be resolved.
--
-- (One tuple so the 43-step walk is normalized once for both numbers.)
------------------------------------------------------------------------

run-summary : ℕ × ℕ
run-summary = proj₂ learned , length synthesized

test-run : run-summary ≡ (344 , 637)
test-run = refl

------------------------------------------------------------------------
-- SOLVE through the LEARNED dynamics
--
-- The learned classifier IS the environment model the agent discovered.
------------------------------------------------------------------------

synth-is-dead : Config → Bool
synth-is-dead = cand-is-dead synthesized

synth-is-solved : Config → Bool
synth-is-solved = eval (feat (filled-is num-empty))

-- The unique solution of the puzzle (row-major over the 43 holes).
solution : Config
solution =
  1 ∷ 2 ∷ 6 ∷ 9 ∷ 5 ∷ 7 ∷ 1 ∷ 2 ∷ 7 ∷ 8 ∷ 9 ∷ 3 ∷ 4 ∷ 5 ∷ 3 ∷ 5 ∷ 7 ∷ 8 ∷
  9 ∷ 5 ∷ 7 ∷ 3 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 6 ∷ 7 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 1 ∷ 2 ∷ 6 ∷ 8 ∷
  9 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 8 ∷ []

------------------------------------------------------------------------
-- CEGAR fixpoint + SOLVE, via forcedness
--
-- `surviving-by p k` = the digits at cell k of the solution prefix that
-- predicate p classifies as alive.  Two certificates:
--
--   test-env-forced    – the ENVIRONMENT is conflict-forced: at every
--                        cell exactly the solution digit survives the
--                        true oracle (cheap: uses ok-board, not the
--                        637-feature candidate).
--   test-learned-forced – the LEARNED model is conflict-forced to the
--                        SAME solution.
--
-- Their agreement IS the CEGAR fixpoint: the synthesized candidate
-- classifies every reachable probe (43 cells x 9 digits) exactly as the
-- environment does, with no remaining counterexample — and, because the
-- unique survivor at each cell is the solution digit, the learned model
-- also *solves* the puzzle.  Dead actions give all-zero traces while the
-- survivor carries the solved reward within lookahead, so this pins the
-- full Finder rollout.
------------------------------------------------------------------------

take' : ℕ → List ℕ → List ℕ
take' zero    _        = []
take' (suc n) []       = []
take' (suc n) (x ∷ xs) = x ∷ take' n xs

upTo : ℕ → List ℕ
upTo n = go n 0
  where
  go : ℕ → ℕ → List ℕ
  go zero    _ = []
  go (suc n) k = k ∷ go n (suc k)

filterℕ : (ℕ → Bool) → List ℕ → List ℕ
filterℕ f [] = []
filterℕ f (x ∷ xs) =
  if f x then x ∷ filterℕ f xs else filterℕ f xs

digits1-9 : List ℕ
digits1-9 = 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ []

surviving-by : (Config → Bool) → ℕ → List ℕ
surviving-by p k =
  filterℕ (λ d → not (p (take' k solution ++ (d ∷ [])))) digits1-9

-- The environment is conflict-forced to the solution (ground truth).
test-env-forced :
  map (surviving-by env-is-dead) (upTo num-empty)
  ≡ map (λ d → d ∷ []) solution
test-env-forced = refl

-- The LEARNED model is conflict-forced to the SAME solution: the CEGAR
-- fixpoint (candidate agrees with the environment on every reachable
-- probe) and the solution of the puzzle, in one certificate.
test-learned-forced :
  map (surviving-by synth-is-dead) (upTo num-empty)
  ≡ map (λ d → d ∷ []) solution
test-learned-forced = refl

------------------------------------------------------------------------
-- Finder rollout (shallow lookahead) under the learned dynamics
------------------------------------------------------------------------

open import CSHRL.EnvironmentClass.CombinatorialPlacementMDP

open CombinatorialPlacementMDP
  Config Action
  synth-is-dead synth-is-solved
  place solved-reward
  all-actions A1 num-empty

run-policy : State → ℕ → ℕ → List Action
run-policy _ _ zero = []
run-policy s depth (suc n) =
  let a = find-policy s depth
  in a ∷ run-policy (proj₁ (step s a)) depth n

-- The Finder, planning in the learned model, fills the last two cells
-- with the solution digits (6 then 8).  Kept shallow: each find-policy
-- node evaluates the 637-feature learned is-dead, so a deep lookahead is
-- expensive — forcedness above already pins the whole rollout, this just
-- exercises the EC's actual Finder on the learned model.
test-tail-rollout :
  run-policy (Ongoing (take' 41 solution)) 2 2 ≡ A6 ∷ A8 ∷ []
test-tail-rollout = refl

------------------------------------------------------------------------
-- VERIFY: the completed board is valid in the REAL environment
------------------------------------------------------------------------

test-valid : ok-board (board-of solution) ≡ true
test-valid = refl

test-complete : synth-is-solved solution ≡ true
test-complete = refl

------------------------------------------------------------------------
-- SUMMARY
--
--   blind candidate → 344 environment counterexamples → 637 features →
--   learned model conflict-forced to the same solution as the
--   environment (CEGAR fixpoint) → Finder tail rollout matches the
--   solution → board valid in the real environment.
--
-- Cost of arriving at the dynamics: 43 x 9 = 387 environment probes,
-- linear in horizon x actions, against a 9^43 raw board space.  Nothing
-- brute-forced, nothing written by hand.  All --safe, no postulates.
------------------------------------------------------------------------
