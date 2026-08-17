{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Synthesized.SudokuNonForced
--
-- A NON-FORCED instance, done honestly: where survival fails and the
-- optimal Finder is genuinely needed.
--
-- SudokuSynth (4x4) and Sudoku9Synth (9x9) learn the dynamics of
-- CONFLICT-FORCED instances: at every cell exactly one digit survives,
-- every mistake dies immediately, and a one-step survival policy
-- solves the puzzle.  This module drops that property.  The 4x4
-- instance below (5 holes, unique solution) has TWO locally consistent
-- digits at its first hole: digit 1 creates no conflict, yet the
-- branch it opens is DOOMED — the next cell then has no consistent
-- digit.  Death is latent, not immediate.
--
-- Everything is learned and certified as before, with the differences
-- the non-forced setting demands:
--
--   EXPLORE – the CEGIS walk can no longer follow "the" forced path
--             (there isn't one); it explores the whole reachable
--             locally-consistent tree, absorbing counterexamples in
--             every branch.  The tree is small BECAUSE conflicts prune
--             it — the dissolution effect again.
--   VERIFY  – the CEGAR sweep certifies learned == environment on
--             every probe of every reachable state of the tree.
--   SOLVE   – certified BOTH ways:
--               * the survival policy provably FAILS
--                 (it walks into the doomed branch and gets stuck), and
--               * the EC's optimal Finder, planning to the horizon
--                 through the LEARNED model, produces the solution.
--   DOOM    – the latent-doom state is pinned: (1 ∷ []) is alive in
--             the environment AND in the learned model, yet its
--             capability profile is 0, while the good branch's is 100.
--
-- Verified results (all refl, one boolean certificate):
--   * the root has exactly TWO env-alive digits (the non-forced witness),
--   * 15 counterexample observations, 27 of 56 features learned over
--     the explored tree,
--   * the CEGAR tree sweep is clean,
--   * survival ≠ solution (it produces 1∷1∷1∷1∷1),
--   * Finder through the learned model ≡ solution (2∷1∷4∷3∷1),
--   * latent doom: solve (Ongoing (1 ∷ [])) ≡ 0 on an alive state,
--     solve (Ongoing (2 ∷ [])) ≡ 100.
--
-- WHY THIS SCALE.  Full-horizon lookahead explores the locally
-- consistent tree, whose size is exponential in the branching.  Here
-- (one branch point, 5 holes) it is tiny; at 9x9 with 43 holes even a
-- branching factor of 2 gives ~2^43 ≈ 10^13 nodes — prohibitive for
-- ANY evaluator (Rocq's vm_compute included), independent of Agda.
-- Non-forcedness is an algorithmic cost of planning, not a type-checker
-- artifact; the learning cost stays linear in the explored tree.
--
-- All --safe, no postulates.
------------------------------------------------------------------------

module CSHRL.Tasks.Synthesized.SudokuNonForced where

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≡ᵇ_)
open import Data.List using (List; []; _∷_; length; map; _++_; foldl; concatMap)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- DOMAIN: 4x4 Sudoku, positions 0..15, 2x2 boxes
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

sees : ℕ → ℕ → Bool
sees p q =
  (div4 p ≡ᵇ div4 q) ∨
  (mod4 p ≡ᵇ mod4 q) ∨
  ((div2 (div4 p) ≡ᵇ div2 (div4 q)) ∧ (div2 (mod4 p) ≡ᵇ div2 (mod4 q)))

Cell : Set
Cell = Maybe ℕ

-- . . 4 3 / . . 2 1 / . 2 3 4 / 3 4 1 2   (5 holes, unique solution,
-- and NOT conflict-forced: the first hole admits digits 1 and 2).
template : List Cell
template =
  nothing ∷ nothing ∷ just 4  ∷ just 3  ∷
  nothing ∷ nothing ∷ just 2  ∷ just 1  ∷
  nothing ∷ just 2  ∷ just 3  ∷ just 4  ∷
  just 3  ∷ just 4  ∷ just 1  ∷ just 2  ∷ []

num-empty : ℕ
num-empty = 5

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

-- The unique solution over the 5 holes (row-major).
solution : Config
solution = 2 ∷ 1 ∷ 4 ∷ 3 ∷ 1 ∷ []

------------------------------------------------------------------------
-- Environment oracle: full pairwise consistency
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

env-is-dead : Config → Bool
env-is-dead cfg = not (ok-board (board-of cfg))

------------------------------------------------------------------------
-- THE NON-FORCED WITNESS: two digits survive at the root
------------------------------------------------------------------------

test-not-forced :
  map (λ a → env-is-dead (place [] a)) all-actions
  ≡ false ∷ false ∷ true ∷ true ∷ []
test-not-forced = refl

------------------------------------------------------------------------
-- FEATURES: the 56 seeing pairs (the synthesis vocabulary)
------------------------------------------------------------------------

data SFeature : Set where
  conflict : ℕ → ℕ → SFeature

feat-fires : List Cell → ℕ → ℕ → Bool
feat-fires b p q = check (lookup-cell b p) (lookup-cell b q)
  where
  check : Cell → Cell → Bool
  check (just d) (just e) = sees p q ∧ (d ≡ᵇ e)
  check _        _        = false

eval-sfeature : SFeature → Config → Bool
eval-sfeature (conflict p q) cfg = feat-fires (board-of cfg) p q

private
  range : ℕ → ℕ → List ℕ
  range _ zero    = []
  range k (suc n) = k ∷ range (suc k) n

  filterᵇ : (ℕ → Bool) → List ℕ → List ℕ
  filterᵇ f [] = []
  filterᵇ f (x ∷ xs) =
    if f x then x ∷ filterᵇ f xs else filterᵇ f xs

conflict-feats : List SFeature
conflict-feats =
  concatMap
    (λ p → map (conflict p) (filterᵇ (sees p) (range (suc p) (15 ∸ p))))
    (range 0 16)

check-vocab : length conflict-feats ≡ 56
check-vocab = refl

any-fires : List Cell → List SFeature → Bool
any-fires b [] = false
any-fires b (conflict p q ∷ fs) = feat-fires b p q ∨ any-fires b fs

cand-is-dead : List SFeature → Config → Bool
cand-is-dead vs cfg = any-fires (board-of cfg) vs

------------------------------------------------------------------------
-- TREE-EXPLORING CEGIS
--
-- Without forcedness there is no single path to walk: the learner
-- explores every env-alive branch of the reachable tree, probing all
-- actions at every node and absorbing counterexamples (env dead,
-- candidate alive).  Features can fire in more than one branch, so the
-- membership test is back (unlike the forced-path walks).
------------------------------------------------------------------------

eq-feat : SFeature → SFeature → Bool
eq-feat (conflict p q) (conflict p' q') = (p ≡ᵇ p') ∧ (q ≡ᵇ q')

member : SFeature → List SFeature → Bool
member f [] = false
member f (g ∷ gs) = eq-feat f g ∨ member f gs

filter-feats : (SFeature → Bool) → List SFeature → List SFeature
filter-feats P [] = []
filter-feats P (f ∷ fs) =
  if P f then f ∷ filter-feats P fs else filter-feats P fs

new-firing : Config → List SFeature → List SFeature
new-firing b vs =
  filter-feats (λ f → eval-sfeature f b ∧ not (member f vs)) conflict-feats

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

explore : Config → LearnerState → ℕ → LearnerState
explore _ st zero    = st
explore c st (suc n) = go all-actions (probe-all c st)
  where
  go : List Action → LearnerState → LearnerState
  go []       st' = st'
  go (a ∷ as) st' =
    if env-is-dead (place c a)
      then go as st'
      else go as (explore (place c a) st' n)

learned : LearnerState
learned = explore [] ([] , 0) num-empty

synthesized : List SFeature
synthesized = proj₁ learned

------------------------------------------------------------------------
-- CEGAR sweep over the WHOLE reachable tree
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

verify-tree : List SFeature → Config → ℕ → Bool
verify-tree _  _ zero    = true
verify-tree vs c (suc n) = agree-all vs c ∧ go all-actions
  where
  go : List Action → Bool
  go []       = true
  go (a ∷ as) =
    (if env-is-dead (place c a) then true
     else verify-tree vs (place c a) n)
    ∧ go as

------------------------------------------------------------------------
-- SURVIVAL vs the OPTIMAL FINDER through the learned model
------------------------------------------------------------------------

-- One-step survival (what solves forced instances): first action the
-- learned model deems alive, default D1.
learned-alive : List SFeature → Config → Action
learned-alive vs c = go all-actions
  where
  go : List Action → Action
  go [] = D1
  go (a ∷ as) = if cand-is-dead vs (place c a) then go as else a

run-survival : List SFeature → Config → ℕ → Config
run-survival _  c zero    = c
run-survival vs c (suc n) = run-survival vs (place c (learned-alive vs c)) n

is-solved : Config → Bool
is-solved cfg = length cfg ≡ᵇ num-empty

open import CSHRL.EnvironmentClass.CombinatorialPlacementMDP

module Through (vs : List SFeature) where
  open CombinatorialPlacementMDP
    Config Action
    (cand-is-dead vs) is-solved
    place solved-reward
    all-actions D1 num-empty

  run-policy : State → ℕ → ℕ → List Action
  run-policy _ _ zero = []
  run-policy s depth (suc n) =
    let a = find-policy s depth
    in a ∷ run-policy (proj₁ (step s a)) depth n

  finder-digits : List ℕ
  finder-digits = map digit (run-policy (Ongoing []) num-empty num-empty)

  -- Latent doom, through the learned model: (1 ∷ []) is alive in the
  -- environment and in the learned model, yet its capability profile is
  -- zero; the good branch (2 ∷ []) carries full capability.
  doom-ok : Bool
  doom-ok =
    not (env-is-dead (1 ∷ [])) ∧ not (cand-is-dead vs (1 ∷ []))
    ∧ (solve (Ongoing (1 ∷ [])) num-empty ≡ᵇ 0)
    ∧ (solve (Ongoing (2 ∷ [])) num-empty ≡ᵇ solved-reward)

eq-config : Config → Config → Bool
eq-config []       []       = true
eq-config (x ∷ xs) (y ∷ ys) = (x ≡ᵇ y) ∧ eq-config xs ys
eq-config _        _        = false

------------------------------------------------------------------------
-- THE COMBINED CERTIFICATE (single boolean; walk evaluated once)
--
--   * 15 counterexample observations over the explored tree, 27 of the
--     56 vocabulary features learned,
--   * the CEGAR sweep over every reachable probe is clean,
--   * SURVIVAL FAILS: it enters the doomed branch and produces
--     1∷1∷1∷1∷1, not the solution — one-step survival is refuted as a
--     solver for non-forced instances,
--   * the OPTIMAL FINDER through the learned model produces the unique
--     solution from the empty board, and
--   * latent doom is pinned (alive state with zero capability).
------------------------------------------------------------------------

outcome-ok : LearnerState → Bool
outcome-ok (vs , n) =
  (n ≡ᵇ 15) ∧ (length vs ≡ᵇ 27)
  ∧ verify-tree vs [] num-empty
  ∧ eq-config (run-survival vs [] num-empty) (1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ [])
  ∧ not (eq-config (run-survival vs [] num-empty) solution)
  ∧ eq-config (Through.finder-digits vs) solution
  ∧ Through.doom-ok vs

test-outcome : outcome-ok learned ≡ true
test-outcome = refl

-- The solution is valid and complete in the REAL environment.
test-valid : ok-board (board-of solution) ≡ true
test-valid = refl

test-complete : is-solved solution ≡ true
test-complete = refl

------------------------------------------------------------------------
-- SUMMARY
--
--   non-forced instance (two live digits at the root, death latent)
--   → tree-exploring CEGIS: 15 counterexamples, 27 features
--   → CEGAR sweep clean on the whole reachable tree
--   → survival policy PROVABLY FAILS (1∷1∷1∷1∷1 ≠ solution)
--   → the EC's optimal Finder through the LEARNED model solves it
--   → latent doom certified: alive state, capability 0.
--
-- Forcedness bought the linear solve at 9x9; this module certifies
-- what its absence costs (lookahead) and that the same learning loop
-- handles it — the tree, not the path, is explored, and the cost of
-- learning stays linear in the tree that conflicts leave reachable.
-- All --safe, no postulates.
------------------------------------------------------------------------
