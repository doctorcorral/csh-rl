{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Synthesized.FrozenLakeE2E
--
-- FROZENLAKE 4×4 — a well-known OpenAI Gym RL benchmark.
--
-- Map (standard):
--
--   S F F F     0  1  2  3     S = Start
--   F H F H     4  5  6  7     F = Frozen (safe)
--   F F F H     8  9 10 11     H = Hole (terminal, reward 0)
--   H F F G    12 13 14 15     G = Goal  (terminal, reward 1)
--
-- Raw features (standard RL): grid coordinates (row, col).
-- Dynamics features: reward and self-loop indicators per action.
--
-- The FTL discovers which features discriminate between state
-- classes, identifies safe/dangerous/terminal states, and verifies
-- the optimal policy trajectory from Start to Goal.
--
-- All --safe, no postulates.
------------------------------------------------------------------------

module CSHRL.Tasks.Synthesized.FrozenLakeE2E where

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
-- I. ENVIRONMENT: FrozenLake 4×4 (deterministic, non-slippery)
-- ═══════════════════════════════════════════════════════════════════
------------------------------------------------------------------------

data Action : Set where
  L D R U : Action

all-actions : List Action
all-actions = L ∷ D ∷ R ∷ U ∷ []

-- Grid structure (state = ℕ, position in 4×4 grid)

grid-row : ℕ → ℕ
grid-row 0  = 0
grid-row 1  = 0
grid-row 2  = 0
grid-row 3  = 0
grid-row 4  = 1
grid-row 5  = 1
grid-row 6  = 1
grid-row 7  = 1
grid-row 8  = 2
grid-row 9  = 2
grid-row 10 = 2
grid-row 11 = 2
grid-row 12 = 3
grid-row 13 = 3
grid-row 14 = 3
grid-row 15 = 3
grid-row _  = 0

grid-col : ℕ → ℕ
grid-col 0  = 0
grid-col 1  = 1
grid-col 2  = 2
grid-col 3  = 3
grid-col 4  = 0
grid-col 5  = 1
grid-col 6  = 2
grid-col 7  = 3
grid-col 8  = 0
grid-col 9  = 1
grid-col 10 = 2
grid-col 11 = 3
grid-col 12 = 0
grid-col 13 = 1
grid-col 14 = 2
grid-col 15 = 3
grid-col _  = 0

to-state : ℕ → ℕ → ℕ
to-state r c = r * 4 + c

-- Map topology

is-hole : ℕ → Bool
is-hole 5  = true
is-hole 7  = true
is-hole 11 = true
is-hole 12 = true
is-hole _  = false

is-goal : ℕ → Bool
is-goal 15 = true
is-goal _  = false

is-terminal : ℕ → Bool
is-terminal 5  = true
is-terminal 7  = true
is-terminal 11 = true
is-terminal 12 = true
is-terminal 15 = true
is-terminal _  = false

reward-fn : ℕ → ℕ
reward-fn 15 = 1
reward-fn _  = 0

-- Movement: terminal states absorb; non-terminal states move on the grid

private
  go : ℕ → ℕ → Action → ℕ
  go r c L = if c ≡ᵇ 0 then to-state r c else to-state r (c ∸ 1)
  go r c D = if r ≡ᵇ 3 then to-state r c else to-state (r + 1) c
  go r c R = if c ≡ᵇ 3 then to-state r c else to-state r (c + 1)
  go r c U = if r ≡ᵇ 0 then to-state r c else to-state (r ∸ 1) c

move : ℕ → Action → ℕ
move 5  _ = 5
move 7  _ = 7
move 11 _ = 11
move 12 _ = 12
move 15 _ = 15
move s  a = go (grid-row s) (grid-col s) a

step : ℕ → Action → ℕ × ℕ
step s a = let s' = move s a in (s' , reward-fn s')

all-states : List ℕ
all-states = 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷
             8 ∷ 9 ∷ 10 ∷ 11 ∷ 12 ∷ 13 ∷ 14 ∷ 15 ∷ []

-- Sanity checks on grid structure

test-move-0R : move 0 R ≡ 1
test-move-0R = refl

test-move-0D : move 0 D ≡ 4
test-move-0D = refl

test-move-0L : move 0 L ≡ 0
test-move-0L = refl

test-move-14R : move 14 R ≡ 15
test-move-14R = refl

test-move-hole : move 5 R ≡ 5
test-move-hole = refl

test-move-goal : move 15 L ≡ 15
test-move-goal = refl

test-move-4R : move 4 R ≡ 5
test-move-4R = refl

test-move-1D : move 1 D ≡ 5
test-move-1D = refl

------------------------------------------------------------------------
-- ═══════════════════════════════════════════════════════════════════
-- II. RAW FEATURES — standard RL state descriptors
-- ═══════════════════════════════════════════════════════════════════
--
-- Standard RL approach: state features are grid coordinates.
-- We add dynamics-derived features for richer discovery.
------------------------------------------------------------------------

data FLFeature : Set where
  row-is         : ℕ → FLFeature
  col-is         : ℕ → FLFeature
  has-pos-reward : Action → FLFeature
  is-self-loop   : Action → FLFeature
  leads-terminal : Action → FLFeature

eval-fl : FLFeature → ℕ → Bool
eval-fl (row-is k)         s = grid-row s ≡ᵇ k
eval-fl (col-is k)         s = grid-col s ≡ᵇ k
eval-fl (has-pos-reward a)  s = not (reward-fn (move s a) ≡ᵇ 0)
eval-fl (is-self-loop a)   s = move s a ≡ᵇ s
eval-fl (leads-terminal a) s = is-terminal (move s a)

------------------------------------------------------------------------
-- ═══════════════════════════════════════════════════════════════════
-- III. FEATURE DISCOVERY PIPELINE
-- ═══════════════════════════════════════════════════════════════════
------------------------------------------------------------------------

private
  range4 : List ℕ
  range4 = 0 ∷ 1 ∷ 2 ∷ 3 ∷ []

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

-- Enumeration: 4 row + 4 col + 4 reward + 4 loop + 4 terminal = 20

enumerate-fl : List FLFeature
enumerate-fl =
  map row-is range4 ++
  map col-is range4 ++
  map has-pos-reward all-actions ++
  map is-self-loop all-actions ++
  map leads-terminal all-actions

test-enum-count : length enumerate-fl ≡ 20
test-enum-count = refl

-- Non-trivial filtering

is-nontrivial : FLFeature → Bool
is-nontrivial f =
  let vals = map (eval-fl f) all-states
  in not (all-true-list vals) ∧ not (all-false-list vals)

discovered : List FLFeature
discovered = bfilter is-nontrivial enumerate-fl

-- has-pos-reward L/D/U: true only at {15} (goal self-loop) → nontrivial
-- has-pos-reward R: true at {14,15} → nontrivial
-- is-self-loop: many non-trivial patterns
-- leads-terminal: many non-trivial patterns
-- All row-is and col-is are non-trivial (each selects 4 of 16 states)

test-discovered-count : length discovered ≡ 20
test-discovered-count = refl

------------------------------------------------------------------------
-- Feature vector analysis
------------------------------------------------------------------------

feature-vector : List FLFeature → ℕ → List Bool
feature-vector []       _ = []
feature-vector (f ∷ fs) s = eval-fl f s ∷ feature-vector fs s

-- Terminal states have distinctive feature vectors:
-- holes are self-loops for ALL actions but have no positive reward
-- goal is a self-loop for all actions WITH positive reward

test-fv-hole : eval-fl (is-self-loop L) 5  ≡ true
test-fv-hole = refl

test-fv-hole-r : eval-fl (has-pos-reward L) 5  ≡ false
test-fv-hole-r = refl

test-fv-goal-loop : eval-fl (is-self-loop L) 15 ≡ true
test-fv-goal-loop = refl

test-fv-goal-rew : eval-fl (has-pos-reward L) 15 ≡ true
test-fv-goal-rew = refl

-- Danger detection: leads-terminal identifies states adjacent to holes/goal

test-danger-1D : eval-fl (leads-terminal D) 1 ≡ true
test-danger-1D = refl

test-danger-4R : eval-fl (leads-terminal R) 4 ≡ true
test-danger-4R = refl

test-danger-14R : eval-fl (leads-terminal R) 14 ≡ true
test-danger-14R = refl

test-safe-0R : eval-fl (leads-terminal R) 0 ≡ false
test-safe-0R = refl

test-safe-0D : eval-fl (leads-terminal D) 0 ≡ false
test-safe-0D = refl

-- Coordinate features partition the grid into rows and columns
test-row0 : eval-fl (row-is 0) 2 ≡ true
test-row0 = refl

test-row3 : eval-fl (row-is 3) 14 ≡ true
test-row3 = refl

test-col2 : eval-fl (col-is 2) 10 ≡ true
test-col2 = refl

------------------------------------------------------------------------
-- ═══════════════════════════════════════════════════════════════════
-- IV. OPTIMAL POLICY AND TRAJECTORY VERIFICATION
-- ═══════════════════════════════════════════════════════════════════
------------------------------------------------------------------------

-- Optimal policy for deterministic FrozenLake 4×4.
-- At terminal states, action is irrelevant (self-loop).
optimal-policy : ℕ → Action
optimal-policy 0  = D
optimal-policy 1  = R
optimal-policy 2  = D
optimal-policy 3  = L
optimal-policy 4  = D
optimal-policy 6  = D
optimal-policy 8  = R
optimal-policy 9  = D
optimal-policy 10 = D
optimal-policy 13 = R
optimal-policy 14 = R
optimal-policy _  = L

-- Trajectory from Start (0) to Goal (15)

run-policy : ℕ → ℕ → List (Action × ℕ)
run-policy _ zero    = []
run-policy s (suc n) with is-terminal s
... | true  = []
... | false =
  let a  = optimal-policy s
      s' = move s a
  in (a , s') ∷ run-policy s' n

-- Optimal path: 0 →D 4 →D 8 →R 9 →D 13 →R 14 →R 15
test-trajectory : run-policy 0 7
  ≡ (D , 4)  ∷ (D , 8)  ∷ (R , 9)  ∷
    (D , 13) ∷ (R , 14) ∷ (R , 15) ∷ []
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

test-rewards : collect-rewards 0 7 ≡ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 1 ∷ []
test-rewards = refl

-- Verify: the trajectory avoids all holes
private
  traj-states : List ℕ
  traj-states = 0 ∷ 4 ∷ 8 ∷ 9 ∷ 13 ∷ 14 ∷ 15 ∷ []

  all-safe : List ℕ → Bool
  all-safe []       = true
  all-safe (s ∷ ss) = not (is-hole s) ∧ all-safe ss

test-all-safe : all-safe traj-states ≡ true
test-all-safe = refl

-- Verify: the final state IS the goal
test-reaches-goal : is-goal 15 ≡ true
test-reaches-goal = refl

-- Alternative path from state 2: 2→D→6→D→10→D→14→R→15
test-alt-trajectory : run-policy 2 6
  ≡ (D , 6) ∷ (D , 10) ∷ (D , 14) ∷ (R , 15) ∷ []
test-alt-trajectory = refl

------------------------------------------------------------------------
-- ═══════════════════════════════════════════════════════════════════
-- V. FDMDP EC INSTANTIATION — Finder cross-validation
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
  ℕ Action ℕ step _≤_ _≤?ₙ_ (λ {_} → ≤-refl) _⊔_ 0 all-actions L 6

-- Finder agrees with optimal policy at key states
test-finder-0  : Finder.find-policy 0  6 ≡ D
test-finder-0  = refl

test-finder-14 : Finder.find-policy 14 6 ≡ R
test-finder-14 = refl

test-finder-8  : Finder.find-policy 8  6 ≡ R
test-finder-8  = refl

test-finder-9  : Finder.find-policy 9  6 ≡ D
test-finder-9  = refl

test-finder-13 : Finder.find-policy 13 6 ≡ R
test-finder-13 = refl

------------------------------------------------------------------------
-- ═══════════════════════════════════════════════════════════════════
-- VI. SYNTHESIS with discovered features
-- ═══════════════════════════════════════════════════════════════════
------------------------------------------------------------------------

open import CSHRL.Synthesis.FiniteDeterministicMDP
open FDMDPSynthesis ℕ Action step all-actions

open WithStateFeatures FLFeature eval-fl
open WithCEGIS discovered

-- The version space with 20 features at depth 0: 22 candidates
test-vs-size : length (initial-vs 0) ≡ 22
test-vs-size = refl

-- Observations for "D ≤ R" (Right at least as good as Down):
-- At state 14: R→15(goal!), D→14(wall) → Right dominates. True.
-- At state 10: R→11(hole!), D→14(toward goal) → Down dominates. False.
obs-D≤R : List PredObs
obs-D≤R = (14 , true) ∷ (10 , false) ∷ []

-- CEGIS discovers: "D ≤ R" ≈ feat(row-is 3)
-- At row 3, Right reaches the goal (14→15) or is safe.
synth-D≤R : synth-rank-pred 0 obs-D≤R ≡ just (feat (row-is 3))
synth-D≤R = refl

test-synth-eval-14 : eval (feat (row-is 3)) 14 ≡ true
test-synth-eval-14 = refl

test-synth-eval-10 : eval (feat (row-is 3)) 10 ≡ false
test-synth-eval-10 = refl

-- CEGIS maps coordinate features to spatial ranking predicates:
-- "Right dominates Down at the bottom row" — a meaningful RL insight
-- discovered from just 2 observations and coordinate features.

-- Observations for "U ≤ D" — at state 0 (row 0, U→wall, D→4):
obs-U≤D : List PredObs
obs-U≤D = (0 , true) ∷ (14 , false) ∷ []

synth-U≤D : synth-rank-pred 0 obs-U≤D ≡ just (feat (row-is 0))
synth-U≤D = refl

-- "Down dominates Up at the top row" — another spatial insight.

------------------------------------------------------------------------
-- ═══════════════════════════════════════════════════════════════════
-- VII. FULLY AUTOMATED POLICY SYNTHESIS
--
-- No human-provided observations. The complete pipeline:
--   1. Environment + features (Sections I-III)
--   2. Finder computes optimal action at EVERY non-terminal state
--   3. Observations GENERATED AUTOMATICALLY from Finder
--   4. Cascading CEGIS synthesizes PredProg per action
--   5. Policy RECONSTRUCTED from PredProg — a portable artifact
--   6. Verified: matches Finder at ALL 11 non-terminal states,
--      trajectory reaches goal, avoids all holes
--
-- ZERO human in the loop beyond environment spec + features.
-- ═══════════════════════════════════════════════════════════════════
------------------------------------------------------------------------

_≟ᵃ_ : Action → Action → Bool
L ≟ᵃ L = true
D ≟ᵃ D = true
R ≟ᵃ R = true
U ≟ᵃ U = true
_ ≟ᵃ _ = false

private
  bfilterℕ : (ℕ → Bool) → List ℕ → List ℕ
  bfilterℕ _ []       = []
  bfilterℕ p (x ∷ xs) = if p x then x ∷ bfilterℕ p xs else bfilterℕ p xs

  bfilter-pair : (ℕ × Action → Bool) → List (ℕ × Action) → List (ℕ × Action)
  bfilter-pair _ [] = []
  bfilter-pair p (x ∷ xs) = if p x then x ∷ bfilter-pair p xs
                             else bfilter-pair p xs

non-terminal-states : List ℕ
non-terminal-states = bfilterℕ (λ s → not (is-terminal s)) all-states

test-nt-count : length non-terminal-states ≡ 11
test-nt-count = refl

-- Step 1: Precompute Finder's optimal action at every non-terminal state.
-- Evaluated ONCE; all observations derive from this map.
finder-map : List (ℕ × Action)
finder-map = map (λ s → (s , Finder.find-policy s 6)) non-terminal-states

private
  extract : Maybe PredProg → PredProg
  extract (just p) = p
  extract nothing  = falsep

-- Step 2: Cascading CEGIS.

-- Stage 1: "Is L optimal?" — L is rare and has a clean depth-0 predicate.
obs-is-L : List PredObs
obs-is-L = map (λ { (s , a) → (s , a ≟ᵃ L) }) finder-map

pl : PredProg
pl = extract (synth-rank-pred 0 obs-is-L)

-- Stage 2: "Is R optimal?" — among non-L states.
remaining-after-L : List (ℕ × Action)
remaining-after-L = bfilter-pair (λ { (s , a) → not (a ≟ᵃ L) }) finder-map

obs-is-R : List PredObs
obs-is-R = map (λ { (s , a) → (s , a ≟ᵃ R) }) remaining-after-L

pr : PredProg
pr = extract (synth-rank-pred 1 obs-is-R)

-- Stage 3: D is the default for all remaining states.

-- Step 3: Reconstruct policy from synthesized predicates.
auto-policy : ℕ → Action
auto-policy s =
  if eval pl s then L
  else if eval pr s then R
  else D

-- Step 4: Verify the auto-policy trajectory from Start.
run-auto : ℕ → ℕ → List (Action × ℕ)
run-auto _ zero    = []
run-auto s (suc n) with is-terminal s
... | true  = []
... | false =
  let a  = auto-policy s
      s' = move s a
  in (a , s') ∷ run-auto s' n

test-auto-traj : run-auto 0 7
  ≡ (D , 4)  ∷ (D , 8)  ∷ (R , 9)  ∷
    (D , 13) ∷ (R , 14) ∷ (R , 15) ∷ []
test-auto-traj = refl

-- Auto-policy rewards
auto-rewards : ℕ → ℕ → List ℕ
auto-rewards _ zero    = []
auto-rewards s (suc n) with is-terminal s
... | true  = []
... | false =
  let a       = auto-policy s
      (s' , r) = step s a
  in r ∷ auto-rewards s' n

test-auto-rewards : auto-rewards 0 7 ≡ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 1 ∷ []
test-auto-rewards = refl

-- Hole avoidance
private
  auto-traj-states : List ℕ
  auto-traj-states = 0 ∷ 4 ∷ 8 ∷ 9 ∷ 13 ∷ 14 ∷ 15 ∷ []

test-auto-safe : all-safe auto-traj-states ≡ true
test-auto-safe = refl

-- Step 5: Verify auto-policy matches Finder at ALL non-terminal states.
private
  check-all : List (ℕ × Action) → Bool
  check-all [] = true
  check-all ((s , a) ∷ rest) = (auto-policy s ≟ᵃ a) ∧ check-all rest

test-auto-all-match : check-all finder-map ≡ true
test-auto-all-match = refl

------------------------------------------------------------------------
-- SUMMARY
--
-- FrozenLake 4×4: FULLY AUTOMATED policy synthesis.
--
--   Environment spec + features
--   → Finder oracle (11 states)
--   → Cascading CEGIS (D at depth 0, R at depth 0)
--   → PredProg-based policy
--   → Verified: matches Finder at ALL 11 non-terminal states,
--               trajectory: 0→4→8→9→13→14→15 (same optimal path),
--               rewards: 0,0,0,0,0,1 (reaches goal),
--               all states on trajectory are hole-free.
--
-- ZERO human-provided observations.
-- The synthesized predicates are PORTABLE: they depend only on
-- features (row, column), not on state indices.
--
-- All --safe, no postulates.
------------------------------------------------------------------------
