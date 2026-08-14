{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Synthesized.SudokuSynth
--
-- AUTOMATIC ENVIRONMENT SYNTHESIS: the dynamics are LEARNED, not given.
--
-- SudokuE2E shows the CPMDP critical path with a hand-constructed
-- is-dead-prog.  This module removes the hand: the learner starts with
-- an EMPTY feature set (candidate is-dead = falsep, "nothing ever
-- dies") and discovers the dynamics by online CEGIS:
--
--   WALK    – interact with the environment: at each reachable board,
--             probe every action and compare the candidate's prediction
--             with the observed outcome.
--   REFINE  – each disagreement is a counterexample observation; the
--             features that fire on the witness board are absorbed
--             into the candidate (version-space refinement in the
--             compact, disjunctive representation).
--   VERIFY  – a CEGAR-style sweep re-walks the environment and checks
--             that NO counterexample remains (by refl).
--   SOLVE   – the EC is instantiated with the LEARNED PredProg and the
--             Finder solves the puzzle through the learned dynamics.
--
-- Verified results (all refl):
--   * the blind candidate mispredicts (motivating the loop),
--   * 24 counterexample observations are absorbed during the walk
--     (vs 4^8 = 65,536 raw boards — the dissolution effect: only
--     disagreements are informative),
--   * 44 of the 56 vocabulary features are learned (the other 12 never
--     fire on any reachable counterexample; behaviourally irrelevant
--     features are correctly never forced into the candidate),
--   * the verification sweep finds no remaining counterexample,
--   * find-policy under the learned dynamics produces the unique
--     solution, and the learned model certifies solvability.
--
-- All --safe, no postulates.
------------------------------------------------------------------------

module CSHRL.Tasks.Synthesized.SudokuSynth where

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _≡ᵇ_)
open import Data.List using (List; []; _∷_; length; map; _++_; foldl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import CSHRL.Tasks.Synthesized.SudokuE2E
  using ( Config; board-of; num-empty; solved-reward
        ; Action; D1; D2; D3; D4; digit; all-actions; place
        ; SFeature; conflict; filled-is; eval-sfeature
        ; conflict-feats; any-feat; ok-board; solution )

import CSHRL.Synthesis.Core as SynthCore
open SynthCore.PredicateDSL Config SFeature eval-sfeature

------------------------------------------------------------------------
-- The environment (black box from the learner's perspective)
--
-- The learner may place a digit and OBSERVE whether the episode dies.
-- It never inspects this definition.
------------------------------------------------------------------------

env-is-dead : Config → Bool
env-is-dead cfg = not (ok-board (board-of cfg))

------------------------------------------------------------------------
-- Compact version space for the disjunctive fragment
--
-- The candidate is always  any-feat vs  for a learned feature list vs.
-- Refinement on a counterexample (a board observed dead that the
-- candidate predicted alive) absorbs every vocabulary feature that
-- fires on the witness.
------------------------------------------------------------------------

eq-feat : SFeature → SFeature → Bool
eq-feat (conflict p q)  (conflict p' q')  = (p ≡ᵇ p') ∧ (q ≡ᵇ q')
eq-feat (filled-is n)   (filled-is m)     = n ≡ᵇ m
eq-feat _ _ = false

member : SFeature → List SFeature → Bool
member f [] = false
member f (g ∷ gs) = eq-feat f g ∨ member f gs

filter-feats : (SFeature → Bool) → List SFeature → List SFeature
filter-feats P [] = []
filter-feats P (f ∷ fs) =
  if P f then f ∷ filter-feats P fs else filter-feats P fs

-- Features of the vocabulary that fire on a witness board and are not
-- yet part of the candidate.
new-firing : Config → List SFeature → List SFeature
new-firing b vs =
  filter-feats (λ f → eval-sfeature f b ∧ not (member f vs)) conflict-feats

-- Candidate prediction: evaluation of the learned PredProg term.
cand-is-dead : List SFeature → Config → Bool
cand-is-dead vs = eval (any-feat vs)

------------------------------------------------------------------------
-- Online CEGIS: walk the environment, absorb counterexamples
--
-- Learner state: (learned features, counterexamples absorbed so far).
-- At each board it probes all four digits; a probe is a counterexample
-- exactly when the environment says dead and the candidate says alive
-- (the candidate under-approximates by construction, so the converse
-- disagreement cannot occur).  It then advances along the observed
-- alive action.
------------------------------------------------------------------------

LearnerState : Set
LearnerState = List SFeature × ℕ

probe : Config → LearnerState → Action → LearnerState
probe c (vs , n) a =
  let b = place c a in
  if env-is-dead b ∧ not (cand-is-dead vs b)
    then (vs ++ new-firing b vs , suc n)
    else (vs , n)

probe-all : Config → LearnerState → LearnerState
probe-all c st = foldl (probe c) st all-actions

-- Advance along the first environment-alive action (interaction, not
-- introspection: the learner only uses observed outcomes).
first-alive : Config → Action
first-alive c = go all-actions
  where
  go : List Action → Action
  go [] = D1
  go (a ∷ as) = if env-is-dead (place c a) then go as else a

advance : Config → Config
advance c = place c (first-alive c)

walk : Config → LearnerState → ℕ → LearnerState
walk _ st zero = st
walk c st (suc n) = walk (advance c) (probe-all c st) n

-- The synthesis run: start blind, walk the whole episode.
learned : LearnerState
learned = walk [] ([] , 0) num-empty

synthesized : List SFeature
synthesized = proj₁ learned

------------------------------------------------------------------------
-- The loop is necessary: the blind candidate mispredicts
------------------------------------------------------------------------

-- Digit 1 in the first hole dies (row conflict with a given), but the
-- empty candidate predicts alive.
test-env-dies : env-is-dead (1 ∷ []) ≡ true
test-env-dies = refl

test-blind-wrong : cand-is-dead [] (1 ∷ []) ≡ false
test-blind-wrong = refl

------------------------------------------------------------------------
-- What the run discovered (all by refl)
------------------------------------------------------------------------

-- 24 counterexample observations were absorbed: 8 fill steps x 3 wrong
-- digits, each observed dead exactly once.  Compare 4^8 = 65,536 raw
-- boards: only disagreements are informative.
test-obs-count : proj₂ learned ≡ 24
test-obs-count = refl

-- They force 44 of the 56 vocabulary features into the candidate; the
-- remaining 12 never fire on a reachable counterexample and are never
-- (and need never be) resolved.
test-feat-count : length synthesized ≡ 44
test-feat-count = refl

------------------------------------------------------------------------
-- CEGAR verification sweep: no counterexample remains
--
-- Re-walk the environment and require the learned candidate to agree
-- with the observed outcome on every probe of every reachable board.
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
verify _ _ zero = true
verify vs c (suc n) = agree-all vs c ∧ verify vs (advance c) n

test-no-counterexample : verify synthesized [] num-empty ≡ true
test-no-counterexample = refl

------------------------------------------------------------------------
-- SOLVE through the LEARNED dynamics
--
-- The EC is opened with the synthesized PredProg — the environment
-- model the agent discovered, not the one we wrote.
------------------------------------------------------------------------

synth-is-dead : Config → Bool
synth-is-dead = cand-is-dead synthesized

synth-is-solved : Config → Bool
synth-is-solved = eval (feat (filled-is num-empty))

open import CSHRL.EnvironmentClass.CombinatorialPlacementMDP

open CombinatorialPlacementMDP
  Config Action
  synth-is-dead synth-is-solved
  place solved-reward
  all-actions D1 num-empty

run-policy : State → ℕ → ℕ → List Action
run-policy _ _ zero = []
run-policy s depth (suc n) =
  let a = find-policy s depth
  in a ∷ run-policy (proj₁ (step s a)) depth n

-- The Finder, planning inside the learned model, produces the unique
-- solution of the real puzzle.
test-solution : run-policy (Ongoing []) num-empty num-empty
  ≡ D2 ∷ D3 ∷ D3 ∷ D2 ∷ D1 ∷ D4 ∷ D4 ∷ D1 ∷ []
test-solution = refl

-- The completed board is valid in the REAL environment.
test-valid : ok-board (board-of solution) ≡ true
test-valid = refl

-- The learned model certifies solvability of the puzzle.
test-solvable : solve (Ongoing []) num-empty ≡ solved-reward
test-solvable = refl

------------------------------------------------------------------------
-- SUMMARY
--
--   blind candidate → 24 environment counterexamples → 44 features →
--   CEGAR sweep clean → Finder solves the puzzle in the learned model →
--   solution valid in the real environment.
--
-- Nothing about the dynamics was written by hand: is-dead was arrived
-- at from observations.  All --safe, no postulates.
------------------------------------------------------------------------
