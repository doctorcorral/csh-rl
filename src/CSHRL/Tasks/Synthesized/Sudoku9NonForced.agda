{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Synthesized.Sudoku9NonForced
--
-- NON-FORCED, FULL 9x9 SCALE: learning and optimal planning where
-- survival provably fails.
--
-- Sudoku9Synth's instance is conflict-forced, which linearizes both
-- the survival solve and the Finder's lookahead tree.  A worst-case
-- reading of what non-forcedness costs (branching^horizon) suggests
-- full scale is out of reach — but the worst case is not the real
-- cost: lookahead exits every branch at its first conflict, so the
-- relevant quantity is the size of the CONFLICT-PRUNED locally
-- consistent tree, an instance property.  For this instance (33
-- givens, 48 holes, unique solution, NOT conflict-forced from the very
-- first hole) that tree has only 60 nodes, and the full pipeline runs
-- inside the type checker.
--
--   EXPLORE – tree-exploring CEGIS (no forced path exists): probe all
--             nine digits at every reachable node of the tree,
--             absorbing counterexamples in every branch.  Features can
--             fire in several branches, so the membership test is
--             back; the scan stays localized to the just-placed cell.
--   VERIFY  – CEGAR sweep over every probe of every reachable state.
--   SOLVE   – certified BOTH ways at full scale:
--               * the one-step survival policy FAILS: at the sixth
--                 hole digits 1 and 7 are both locally alive; survival
--                 picks 1 and diverges from the unique solution,
--               * the EC's optimal Finder, planning to horizon 48
--                 through the LEARNED model, produces the solution.
--
-- Verified results (all refl, one boolean certificate):
--   * the root already branches: digits 1 and 2 both survive
--     (test-not-forced) — this instance is non-forced at hole 0,
--   * 379 counterexample observations over the explored tree, 681 of
--     the 810 vocabulary features learned,
--   * the CEGAR tree sweep is clean,
--   * survival ≠ solution, Finder ≡ solution.
--
-- All --safe, no postulates.  ~15 min (the Finder's 12k lookahead
-- evaluations dominate); runs in the slow CI lane.
------------------------------------------------------------------------

module CSHRL.Tasks.Synthesized.Sudoku9NonForced where

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; pred; _+_; _∸_; _≡ᵇ_)
open import Data.List using (List; []; _∷_; length; map; _++_; foldl; concatMap)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- DOMAIN: 9x9, positions 0..80 (as Sudoku9Synth, different instance)
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

sees : ℕ → ℕ → Bool
sees p q =
  (div9 p ≡ᵇ div9 q) ∨
  (mod9 p ≡ᵇ mod9 q) ∨
  ((div3 (div9 p) ≡ᵇ div3 (div9 q)) ∧ (div3 (mod9 p) ≡ᵇ div3 (mod9 q)))

Cell : Set
Cell = Maybe ℕ

-- The Sudoku9Synth puzzle minus five givens (positions 21, 27, 37, 44,
-- 79), leaving 33 givens and 48 holes.  Unique solution, and NOT
-- conflict-forced: hole 0 already admits digits 1 and 2.
template : List Cell
template =
  -- row 0
  nothing ∷ nothing ∷ just 3  ∷ just 4  ∷ just 5  ∷ nothing ∷ just 7  ∷ just 8  ∷ nothing ∷
  -- row 1
  just 4  ∷ nothing ∷ just 6  ∷ nothing ∷ just 8  ∷ just 9  ∷ nothing ∷ nothing ∷ just 3  ∷
  -- row 2
  nothing ∷ nothing ∷ nothing ∷ nothing ∷ just 2  ∷ nothing ∷ nothing ∷ nothing ∷ just 6  ∷
  -- row 3
  nothing ∷ nothing ∷ just 4  ∷ nothing ∷ just 6  ∷ nothing ∷ nothing ∷ nothing ∷ just 1  ∷
  -- row 4
  nothing ∷ nothing ∷ nothing ∷ just 8  ∷ just 9  ∷ just 1  ∷ just 2  ∷ nothing ∷ nothing ∷
  -- row 5
  just 8  ∷ just 9  ∷ nothing ∷ nothing ∷ nothing ∷ nothing ∷ just 5  ∷ nothing ∷ nothing ∷
  -- row 6
  just 3  ∷ nothing ∷ nothing ∷ nothing ∷ nothing ∷ just 8  ∷ just 9  ∷ nothing ∷ nothing ∷
  -- row 7
  nothing ∷ just 7  ∷ nothing ∷ nothing ∷ just 1  ∷ nothing ∷ nothing ∷ nothing ∷ just 5  ∷
  -- row 8
  just 9  ∷ just 1  ∷ just 2  ∷ just 3  ∷ just 4  ∷ nothing ∷ nothing ∷ nothing ∷ nothing ∷ []

num-empty : ℕ
num-empty = 48

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

-- The unique solution over the 48 holes (row-major).
solution : Config
solution =
  1 ∷ 2 ∷ 6 ∷ 9 ∷ 5 ∷ 7 ∷ 1 ∷ 2 ∷ 7 ∷ 8 ∷ 9 ∷ 1 ∷ 3 ∷ 4 ∷ 5 ∷ 2 ∷ 3 ∷ 5 ∷
  7 ∷ 8 ∷ 9 ∷ 5 ∷ 6 ∷ 7 ∷ 3 ∷ 4 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 6 ∷ 7 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷
  1 ∷ 2 ∷ 6 ∷ 8 ∷ 9 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ []

------------------------------------------------------------------------
-- Environment oracle
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
-- THE NON-FORCED WITNESS: hole 0 admits two digits
------------------------------------------------------------------------

test-not-forced :
  map (λ a → env-is-dead (place [] a)) all-actions
  ≡ false ∷ false ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ []
test-not-forced = refl

------------------------------------------------------------------------
-- FEATURES: the 810 seeing pairs
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

any-fires : List Cell → List SFeature → Bool
any-fires b [] = false
any-fires b (conflict p q ∷ fs) = feat-fires b p q ∨ any-fires b fs

cand-is-dead : List SFeature → Config → Bool
cand-is-dead vs cfg = any-fires (board-of cfg) vs

------------------------------------------------------------------------
-- TREE-EXPLORING CEGIS (localized scan, membership test back)
------------------------------------------------------------------------

private
  range : ℕ → ℕ → List ℕ
  range _ zero    = []
  range k (suc n) = k ∷ range (suc k) n

eq-feat : SFeature → SFeature → Bool
eq-feat (conflict p q) (conflict p' q') = (p ≡ᵇ p') ∧ (q ≡ᵇ q')

member : SFeature → List SFeature → Bool
member f [] = false
member f (g ∷ gs) = eq-feat f g ∨ member f gs

filter-feats : (SFeature → Bool) → List SFeature → List SFeature
filter-feats P [] = []
filter-feats P (f ∷ fs) =
  if P f then f ∷ filter-feats P fs else filter-feats P fs

canon : ℕ → ℕ → SFeature
canon a b = if ltℕ a b then conflict a b else conflict b a
  where
  ltℕ : ℕ → ℕ → Bool
  ltℕ zero    (suc _) = true
  ltℕ _       zero    = false
  ltℕ (suc a) (suc b) = ltℕ a b

touching : ℕ → List SFeature
touching lp =
  map (canon lp) (filter-ℕ (λ q → not (q ≡ᵇ lp) ∧ sees lp q) (range 0 81))
  where
  filter-ℕ : (ℕ → Bool) → List ℕ → List ℕ
  filter-ℕ f [] = []
  filter-ℕ f (x ∷ xs) = if f x then x ∷ filter-ℕ f xs else filter-ℕ f xs

-- Only the just-placed cell can create a new conflict (its parent node
-- is alive), so the scan stays local; features can fire in more than
-- one branch of the tree, so the membership test is required.
new-firing : Config → List SFeature → List SFeature
new-firing wit vs =
  filter-feats (λ f → eval-sfeature f wit ∧ not (member f vs)) (touching lp)
  where
  lp : ℕ
  lp = nthℕ (pred (length wit)) hole-positions

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
-- CEGAR sweep over the whole reachable tree
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
--
-- At the sixth hole both 1 and 7 are locally alive; the truth is 7.
-- Survival picks 1 and diverges — at full scale, one-step survival is
-- refuted the moment forcedness is dropped.
------------------------------------------------------------------------

learned-alive : List SFeature → Config → Action
learned-alive vs c = go all-actions
  where
  go : List Action → Action
  go [] = A1
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
    all-actions A1 num-empty

  run-policy : State → ℕ → ℕ → List Action
  run-policy _ _ zero = []
  run-policy s depth (suc n) =
    let a = find-policy s depth
    in a ∷ run-policy (proj₁ (step s a)) depth n

  finder-digits : List ℕ
  finder-digits = map digit (run-policy (Ongoing []) num-empty num-empty)

eq-config : Config → Config → Bool
eq-config []       []       = true
eq-config (x ∷ xs) (y ∷ ys) = (x ≡ᵇ y) ∧ eq-config xs ys
eq-config _        _        = false

------------------------------------------------------------------------
-- THE COMBINED CERTIFICATE (single boolean; learned list shared)
------------------------------------------------------------------------

outcome-ok : LearnerState → Bool
outcome-ok (vs , n) =
  (n ≡ᵇ 379) ∧ (length vs ≡ᵇ 681)
  ∧ verify-tree vs [] num-empty
  ∧ not (eq-config (run-survival vs [] num-empty) solution)
  ∧ eq-config (Through.finder-digits vs) solution

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
--   non-forced 9x9 instance (branching from the very first hole)
--   → tree-exploring CEGIS: 379 counterexamples, 681 of 810 features
--   → CEGAR sweep clean over the whole reachable tree
--   → survival PROVABLY FAILS at full scale
--   → the EC's optimal Finder through the LEARNED model, planning to
--     horizon 48, produces the unique solution.
--
-- The conflict-pruned tree of this instance has 60 nodes — the
-- worst-case branching^horizon bound is not the real cost of
-- non-forcedness; the reachable tree is.  Learning stays linear in
-- that tree; planning pays its lookahead (~12k evaluations here).
-- All --safe, no postulates.
------------------------------------------------------------------------
