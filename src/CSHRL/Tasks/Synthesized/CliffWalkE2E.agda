{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Synthesized.CliffWalkE2E
--
-- CLIFF WALKING — a well-known Sutton & Barto RL benchmark (Ch. 6).
--
-- Compact 4×6 grid (24 states):
--
--   S . . . . .     0  1  2  3  4  5     S = Start
--   . . . . . .     6  7  8  9 10 11     . = Safe
--   . . . . . .    12 13 14 15 16 17     C = Cliff (terminal, r=0)
--   S C C C C G    18 19 20 21 22 23     G = Goal  (terminal, r=1)
--
-- The agent starts at S (state 18, bottom-left).
-- The goal G is at state 23 (bottom-right).
-- The cliff C occupies states 19–22 (bottom row, between S and G).
--
-- Optimal safe path: 18→12→13→14→15→16→17→11→23 (8 steps)
-- Going right from S falls off the cliff immediately.
--
-- Features: coordinate (row-is, col-is) + dynamics (leads-terminal,
-- has-pos-reward, is-self-loop).
--
-- All --safe, no postulates.
------------------------------------------------------------------------

module CSHRL.Tasks.Synthesized.CliffWalkE2E where

open import Data.Bool using (Bool; true; false; not; if_then_else_; _∧_; _∨_)
open import Data.Nat  using (ℕ; zero; suc; _+_; _*_; _∸_; _≡ᵇ_; _⊔_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.List using (List; []; _∷_; length; map; _++_; concatMap)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (Dec; yes; no; ¬_)

------------------------------------------------------------------------
-- ═══════════════════════════════════════════════════════════════════
-- I. ENVIRONMENT: Cliff Walking 4×6
-- ═══════════════════════════════════════════════════════════════════
------------------------------------------------------------------------

data Action : Set where
  L D R U : Action

all-actions : List Action
all-actions = L ∷ D ∷ R ∷ U ∷ []

-- Grid: 4 rows × 6 columns, state = row * 6 + col
-- Computed arithmetically to avoid LiteralTooBig on pattern matching

private
  ltᵇ : ℕ → ℕ → Bool
  ltᵇ _       zero    = false
  ltᵇ zero    (suc _) = true
  ltᵇ (suc m) (suc n) = ltᵇ m n

grid-row : ℕ → ℕ
grid-row s =
  if ltᵇ s 6  then 0
  else if ltᵇ s 12 then 1
  else if ltᵇ s 18 then 2
  else 3

grid-col : ℕ → ℕ
grid-col s =
  if ltᵇ s 6  then s
  else if ltᵇ s 12 then s ∸ 6
  else if ltᵇ s 18 then s ∸ 12
  else s ∸ 18

to-state : ℕ → ℕ → ℕ
to-state r c = r * 6 + c

-- Map topology: cliff = row 3 cols 1-4, goal = row 3 col 5

is-cliff : ℕ → Bool
is-cliff s = (grid-row s ≡ᵇ 3) ∧ not (grid-col s ≡ᵇ 0) ∧ not (grid-col s ≡ᵇ 5)

is-goal : ℕ → Bool
is-goal s = (grid-row s ≡ᵇ 3) ∧ (grid-col s ≡ᵇ 5)

is-terminal : ℕ → Bool
is-terminal s = is-cliff s ∨ is-goal s

reward-fn : ℕ → ℕ
reward-fn s = if is-goal s then 1 else 0

-- Movement: terminal states absorb; non-terminal states move on the grid

private
  go : ℕ → ℕ → Action → ℕ
  go r c L = if c ≡ᵇ 0 then to-state r c else to-state r (c ∸ 1)
  go r c D = if r ≡ᵇ 3 then to-state r c else to-state (r + 1) c
  go r c R = if c ≡ᵇ 5 then to-state r c else to-state r (c + 1)
  go r c U = if r ≡ᵇ 0 then to-state r c else to-state (r ∸ 1) c

move : ℕ → Action → ℕ
move s a = if is-terminal s then s else go (grid-row s) (grid-col s) a

step : ℕ → Action → ℕ × ℕ
step s a = let s' = move s a in (s' , reward-fn s')

all-states : List ℕ
all-states = 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷
             6 ∷ 7 ∷ 8 ∷ 9 ∷ 10 ∷ 11 ∷
             12 ∷ 13 ∷ 14 ∷ 15 ∷ 16 ∷ 17 ∷
             18 ∷ 19 ∷ 20 ∷ 21 ∷ 22 ∷ 23 ∷ []

-- Sanity checks
test-start : to-state 3 0 ≡ 18
test-start = refl

test-goal : to-state 3 5 ≡ 23
test-goal = refl

test-move-start-R : move 18 R ≡ 19
test-move-start-R = refl

test-move-start-U : move 18 U ≡ 12
test-move-start-U = refl

test-cliff-absorb : move 19 R ≡ 19
test-cliff-absorb = refl

test-goal-absorb : move 23 L ≡ 23
test-goal-absorb = refl

test-move-12-R : move 12 R ≡ 13
test-move-12-R = refl

test-move-17-D : move 17 D ≡ 23
test-move-17-D = refl

test-move-wall : move 0 U ≡ 0
test-move-wall = refl

------------------------------------------------------------------------
-- ═══════════════════════════════════════════════════════════════════
-- II. RAW FEATURES
-- ═══════════════════════════════════════════════════════════════════
------------------------------------------------------------------------

data CWFeature : Set where
  row-is         : ℕ → CWFeature
  col-is         : ℕ → CWFeature
  has-pos-reward : Action → CWFeature
  is-self-loop   : Action → CWFeature
  leads-terminal : Action → CWFeature

eval-cw : CWFeature → ℕ → Bool
eval-cw (row-is k)         s = grid-row s ≡ᵇ k
eval-cw (col-is k)         s = grid-col s ≡ᵇ k
eval-cw (has-pos-reward a)  s = not (reward-fn (move s a) ≡ᵇ 0)
eval-cw (is-self-loop a)   s = move s a ≡ᵇ s
eval-cw (leads-terminal a) s = is-terminal (move s a)

------------------------------------------------------------------------
-- ═══════════════════════════════════════════════════════════════════
-- III. FEATURE DISCOVERY PIPELINE
-- ═══════════════════════════════════════════════════════════════════
------------------------------------------------------------------------

private
  range4 : List ℕ
  range4 = 0 ∷ 1 ∷ 2 ∷ 3 ∷ []

  range6 : List ℕ
  range6 = 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []

  all-true-list : List Bool → Bool
  all-true-list []           = true
  all-true-list (false ∷ _)  = false
  all-true-list (true ∷ xs)  = all-true-list xs

  all-false-list : List Bool → Bool
  all-false-list []          = true
  all-false-list (true ∷ _)  = false
  all-false-list (false ∷ xs) = all-false-list xs

  bfilter : ∀ {A : Set} → (A → Bool) → List A → List A
  bfilter _ []       = []
  bfilter p (x ∷ xs) = if p x then x ∷ bfilter p xs else bfilter p xs

-- Enumeration: 4 row + 6 col + 4 reward + 4 loop + 4 terminal = 22
enumerate-cw : List CWFeature
enumerate-cw =
  map row-is range4 ++
  map col-is range6 ++
  map has-pos-reward all-actions ++
  map is-self-loop all-actions ++
  map leads-terminal all-actions

test-enum-count : length enumerate-cw ≡ 22
test-enum-count = refl

-- Non-trivial filtering
is-nontrivial : CWFeature → Bool
is-nontrivial f =
  let vals = map (eval-cw f) all-states
  in not (all-true-list vals) ∧ not (all-false-list vals)

discovered : List CWFeature
discovered = bfilter is-nontrivial enumerate-cw

test-discovered-count : length discovered ≡ 22
test-discovered-count = refl

------------------------------------------------------------------------
-- ═══════════════════════════════════════════════════════════════════
-- IV. KEY FEATURE EVALUATIONS — cliff detection
-- ═══════════════════════════════════════════════════════════════════
------------------------------------------------------------------------

-- leads-terminal D: true at row 2 cols 1-4 (above cliff) and at terminals
test-danger-12D : eval-cw (leads-terminal D) 12 ≡ false
test-danger-12D = refl

test-danger-13D : eval-cw (leads-terminal D) 13 ≡ true
test-danger-13D = refl

test-danger-16D : eval-cw (leads-terminal D) 16 ≡ true
test-danger-16D = refl

test-danger-17D : eval-cw (leads-terminal D) 17 ≡ true
test-danger-17D = refl

-- has-pos-reward D: true only at state 17 (above goal, D→23→reward 1)
test-reward-17D : eval-cw (has-pos-reward D) 17 ≡ true
test-reward-17D = refl

test-reward-16D : eval-cw (has-pos-reward D) 16 ≡ false
test-reward-16D = refl

-- is-self-loop identifies terminal states and wall-bounces
test-loop-cliff : eval-cw (is-self-loop R) 19 ≡ true
test-loop-cliff = refl

test-loop-wall : eval-cw (is-self-loop U) 0 ≡ true
test-loop-wall = refl

------------------------------------------------------------------------
-- ═══════════════════════════════════════════════════════════════════
-- V. OPTIMAL POLICY AND TRAJECTORY VERIFICATION
-- ═══════════════════════════════════════════════════════════════════
------------------------------------------------------------------------

-- Optimal policy: go Up from start, Right along row 2, Down to goal.
-- Row 3 col 0 (start) → Up; row 2 → Right; row 2 col 5 → Down to goal.
-- Other rows: go Down toward row 2, then Right, then Down.
optimal-policy : ℕ → Action
optimal-policy s =
  let r = grid-row s
      c = grid-col s
  in if (r ≡ᵇ 3) ∧ (c ≡ᵇ 0) then U
     else if (r ≡ᵇ 2) ∧ (c ≡ᵇ 5) then D
     else if r ≡ᵇ 2 then R
     else if (r ≡ᵇ 1) ∧ (c ≡ᵇ 5) then D
     else if r ≡ᵇ 1 then R
     else if (r ≡ᵇ 0) ∧ (c ≡ᵇ 5) then D
     else if r ≡ᵇ 0 then R
     else L

-- Trajectory from Start (18) to Goal (23)
run-policy : ℕ → ℕ → List (Action × ℕ)
run-policy _ zero    = []
run-policy s (suc n) with is-terminal s
... | true  = []
... | false =
  let a  = optimal-policy s
      s' = move s a
  in (a , s') ∷ run-policy s' n

-- Safe path: 18→U→12→R→13→R→14→R→15→R→16→R→17→D→23
test-trajectory : run-policy 18 10
  ≡ (U , 12) ∷ (R , 13) ∷ (R , 14) ∷ (R , 15) ∷
    (R , 16) ∷ (R , 17) ∷ (D , 23) ∷ []
test-trajectory = refl

-- Rewards along the trajectory
collect-rewards : ℕ → ℕ → List ℕ
collect-rewards _ zero    = []
collect-rewards s (suc n) with is-terminal s
... | true  = []
... | false =
  let a       = optimal-policy s
      (s' , r) = step s a
  in r ∷ collect-rewards s' n

test-rewards : collect-rewards 18 10 ≡ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 1 ∷ []
test-rewards = refl

-- Verify: the trajectory avoids all cliffs
private
  traj-states : List ℕ
  traj-states = 18 ∷ 12 ∷ 13 ∷ 14 ∷ 15 ∷ 16 ∷ 17 ∷ 23 ∷ []

  all-safe : List ℕ → Bool
  all-safe []       = true
  all-safe (s ∷ ss) = not (is-cliff s) ∧ all-safe ss

test-all-safe : all-safe traj-states ≡ true
test-all-safe = refl

test-reaches-goal : is-goal 23 ≡ true
test-reaches-goal = refl

-- The risky path: going Right from start hits the cliff immediately
test-risky-path : move 18 R ≡ 19
test-risky-path = refl

test-risky-cliff : is-cliff 19 ≡ true
test-risky-cliff = refl

------------------------------------------------------------------------
-- ═══════════════════════════════════════════════════════════════════
-- VI. FDMDP EC INSTANTIATION — Finder cross-validation
-- ═══════════════════════════════════════════════════════════════════
------------------------------------------------------------------------

open import CSHRL.EnvironmentClass.FiniteDeterministicMDP as FDMDP-Mod

private
  _≤?ₙ_ : (m n : ℕ) → Dec (m ≤ n)
  zero  ≤?ₙ _     = yes z≤n
  suc _ ≤?ₙ zero  = no λ ()
  suc m ≤?ₙ suc n with m ≤?ₙ n
  ... | yes p  = yes (s≤s p)
  ... | no  np = no λ { (s≤s q) → np q }

module Finder = FDMDP-Mod.FiniteDeterministicMDP
  ℕ Action ℕ step _≤_ _≤?ₙ_ (λ {_} → ≤-refl) _⊔_ 0 all-actions L 8

module Memo = Finder.Memoized 24 (λ s → s) (λ i → i) 8

-- Finder agrees with optimal policy at key states (memoized DP)
test-finder-18 : Memo.fast-policy 18 ≡ U
test-finder-18 = refl

test-finder-12 : Memo.fast-policy 12 ≡ R
test-finder-12 = refl

test-finder-17 : Memo.fast-policy 17 ≡ D
test-finder-17 = refl

test-finder-13 : Memo.fast-policy 13 ≡ R
test-finder-13 = refl

test-finder-16 : Memo.fast-policy 16 ≡ R
test-finder-16 = refl

------------------------------------------------------------------------
-- ═══════════════════════════════════════════════════════════════════
-- VII. SYNTHESIS with discovered features
-- ═══════════════════════════════════════════════════════════════════
------------------------------------------------------------------------

open import CSHRL.Synthesis.FiniteDeterministicMDP
open FDMDPSynthesis ℕ Action step all-actions

open WithStateFeatures CWFeature eval-cw
open WithCEGIS discovered

test-vs-size : length (initial-vs 0) ≡ 24
test-vs-size = refl

-- Observations for "U ≤ D" (is Down at least as good as Up?):
-- At state 7 (row 1, col 1): D→13(row 2, safe), U→1(row 0) → True.
-- At state 13 (row 2, col 1): D→19(cliff!), U→7(safe) → False.
obs-U≤D : List PredObs
obs-U≤D = (13 , false) ∷ (7 , true) ∷ []

-- CEGIS discovers: "U ≤ D" ≈ feat(row-is 1)
-- At row 1, Down leads to row 2 (safe) — Down is fine.
-- At row 2, Down leads to row 3 (cliff!) — Down is bad.
synth-U≤D : synth-rank-pred 0 obs-U≤D ≡ just (feat (row-is 1))
synth-U≤D = refl

-- Observations for "R ≤ D" (is Down at least as good as Right?):
-- At state 12 (row 2, col 0): R→13(safe), D→18(start row) → True.
-- At state 14 (row 2, col 2): R→15(safe), D→20(cliff!) → False.
obs-R≤D : List PredObs
obs-R≤D = (12 , true) ∷ (14 , false) ∷ []

synth-R≤D : synth-rank-pred 0 obs-R≤D ≡ just (feat (col-is 0))
synth-R≤D = refl

------------------------------------------------------------------------
-- SUMMARY
--
-- Cliff Walking 4×6 — a Sutton & Barto benchmark — modeled as an
-- FDMDP with 24 states and 4 actions.
--
-- Key features:
--   • leads-terminal D identifies cliff-adjacent states (row 2, cols 1-4)
--   • has-pos-reward D pinpoints the goal-adjacent state (17)
--   • is-self-loop identifies terminal states and wall-bounces
--   • Coordinate features (row-is, col-is) partition the grid
--
-- Verified:
--   • Safe path: 18→12→13→14→15→16→17→23 (7 steps, avoids all cliffs)
--   • Risky path: 18→R→19(cliff!) — immediate failure
--   • Finder agrees with optimal policy at all tested states
--   • Trajectory is cliff-free and reaches the goal
--   • CEGIS discovers spatial cliff-avoidance predicates:
--       U≤D ↔ row-is 1 (Down is safe at row 1, deadly at row 2)
--       R≤D ↔ col-is 0 (Down is safe only at the leftmost column)
--
-- All --safe, no postulates.
------------------------------------------------------------------------
