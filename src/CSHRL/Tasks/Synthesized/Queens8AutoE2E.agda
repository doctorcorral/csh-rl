{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Synthesized.Queens8AutoE2E
--
-- 8-QUEENS WITHOUT HAND-CRAFTED FEATURES
--
-- Complete feature discovery pipeline at N=8 scale:
--
--   1. ENUMERATE: 93 candidate features (84 pairwise + 9 length)
--   2. FILTER:    Keep conflict indicators → 84 pairwise survive
--   3. REDUCE:    Eliminate atomics subsumed by composites → 28 pair-any
--   4. DISCOVER:  is-solved from solved/non-solved samples → len-is 8
--   5. EQUIVALENCE: discovered pair-any ≡ hand-crafted attacks (pointwise)
--   6. SOLVE:     CPMDP EC produces [0,4,7,5,2,6,1,3]
--
-- All --safe, no postulates.
------------------------------------------------------------------------

module CSHRL.Tasks.Synthesized.Queens8AutoE2E where

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_; not)
open import Data.Nat  using (ℕ; zero; suc; _+_; _∸_; _≡ᵇ_; _⊔_; _≤_; z≤n; s≤s)
open import Data.List using (List; []; _∷_; length; map; _++_; concatMap)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import CSHRL.Synthesis.FeatureTemplate

------------------------------------------------------------------------
-- Domain: 8-Queens
------------------------------------------------------------------------

N : ℕ
N = 8

Config : Set
Config = List ℕ

data Action : Set where
  C0 C1 C2 C3 C4 C5 C6 C7 : Action

action-to-ℕ : Action → ℕ
action-to-ℕ C0 = 0
action-to-ℕ C1 = 1
action-to-ℕ C2 = 2
action-to-ℕ C3 = 3
action-to-ℕ C4 = 4
action-to-ℕ C5 = 5
action-to-ℕ C6 = 6
action-to-ℕ C7 = 7

all-actions : List Action
all-actions = C0 ∷ C1 ∷ C2 ∷ C3 ∷ C4 ∷ C5 ∷ C6 ∷ C7 ∷ []

place : Config → Action → Config
place xs a = xs ++ (action-to-ℕ a ∷ [])

solved-reward : ℕ
solved-reward = 100

------------------------------------------------------------------------
-- ═══════════════════════════════════════════════════════════════════
-- STAGE 1: ENUMERATE
-- ═══════════════════════════════════════════════════════════════════
------------------------------------------------------------------------

candidates : List ListNatFeature
candidates = enumerate-all N

-- C(8,2) = 28 pairs × 3 variants + 9 length = 93
test-candidates : length candidates ≡ 93
test-candidates = refl

------------------------------------------------------------------------
-- ═══════════════════════════════════════════════════════════════════
-- STAGE 2: FILTER against alive samples
-- ═══════════════════════════════════════════════════════════════════
------------------------------------------------------------------------

alive-samples : List Config
alive-samples =
  [] ∷
  (0 ∷ []) ∷
  (0 ∷ 2 ∷ []) ∷
  (0 ∷ 4 ∷ 7 ∷ []) ∷
  (0 ∷ 4 ∷ 7 ∷ 5 ∷ []) ∷
  (0 ∷ 4 ∷ 7 ∷ 5 ∷ 2 ∷ []) ∷
  (0 ∷ 4 ∷ 7 ∷ 5 ∷ 2 ∷ 6 ∷ []) ∷
  (0 ∷ 4 ∷ 7 ∷ 5 ∷ 2 ∷ 6 ∷ 1 ∷ []) ∷
  (0 ∷ 4 ∷ 7 ∷ 5 ∷ 2 ∷ 6 ∷ 1 ∷ 3 ∷ []) ∷
  []

discovered : List ListNatFeature
discovered = filter-by-alive alive-samples candidates

-- All 84 pairwise features survive; all 9 length features eliminated
test-discovered : length discovered ≡ 84
test-discovered = refl

------------------------------------------------------------------------
-- ═══════════════════════════════════════════════════════════════════
-- STAGE 3: ELIMINATE REDUNDANCY
-- ═══════════════════════════════════════════════════════════════════
------------------------------------------------------------------------

reduced : List ListNatFeature
reduced = eliminate-redundant discovered

-- 28 composite pair-any features survive
test-reduced : length reduced ≡ 28
test-reduced = refl

------------------------------------------------------------------------
-- ═══════════════════════════════════════════════════════════════════
-- STAGE 4: DISCOVER is-solved
-- ═══════════════════════════════════════════════════════════════════
------------------------------------------------------------------------

solved-samples : List Config
solved-samples =
  (0 ∷ 4 ∷ 7 ∷ 5 ∷ 2 ∷ 6 ∷ 1 ∷ 3 ∷ []) ∷
  (0 ∷ 6 ∷ 3 ∷ 5 ∷ 7 ∷ 1 ∷ 4 ∷ 2 ∷ []) ∷
  []

non-solved-samples : List Config
non-solved-samples =
  [] ∷
  (0 ∷ []) ∷
  (0 ∷ 2 ∷ []) ∷
  (0 ∷ 4 ∷ 7 ∷ []) ∷
  (0 ∷ 4 ∷ 7 ∷ 5 ∷ []) ∷
  (0 ∷ 0 ∷ []) ∷
  (0 ∷ 1 ∷ []) ∷
  []

solved-feats : List ListNatFeature
solved-feats = filter-solved solved-samples non-solved-samples candidates

-- Exactly one feature survives: len-is 8
test-solved : length solved-feats ≡ 1
test-solved = refl

------------------------------------------------------------------------
-- ═══════════════════════════════════════════════════════════════════
-- BUILD PREDICATES from discovered features
-- ═══════════════════════════════════════════════════════════════════
------------------------------------------------------------------------

import CSHRL.Synthesis.Core as SynthCore
open SynthCore.PredicateDSL Config ListNatFeature eval-list-feature

any-feat : List ListNatFeature → PredProg
any-feat []            = falsep
any-feat (f ∷ [])      = feat f
any-feat (f ∷ g ∷ fs)  = feat f ∨p any-feat (g ∷ fs)

is-dead-prog : PredProg
is-dead-prog = any-feat reduced

is-solved-prog : PredProg
is-solved-prog = any-feat solved-feats

synth-is-dead : Config → Bool
synth-is-dead = eval is-dead-prog

synth-is-solved : Config → Bool
synth-is-solved = eval is-solved-prog

------------------------------------------------------------------------
-- Classification tests on the synthesized predicates
------------------------------------------------------------------------

check-empty-dead   : synth-is-dead []  ≡ false
check-empty-dead   = refl

check-empty-solved : synth-is-solved [] ≡ false
check-empty-solved = refl

check-00-dead : synth-is-dead (0 ∷ 0 ∷ []) ≡ true
check-00-dead = refl

check-01-dead : synth-is-dead (0 ∷ 1 ∷ []) ≡ true
check-01-dead = refl

check-02-alive : synth-is-dead (0 ∷ 2 ∷ []) ≡ false
check-02-alive = refl

check-047-alive : synth-is-dead (0 ∷ 4 ∷ 7 ∷ []) ≡ false
check-047-alive = refl

check-solution-dead :
  synth-is-dead (0 ∷ 4 ∷ 7 ∷ 5 ∷ 2 ∷ 6 ∷ 1 ∷ 3 ∷ []) ≡ false
check-solution-dead = refl

check-solution-solved :
  synth-is-solved (0 ∷ 4 ∷ 7 ∷ 5 ∷ 2 ∷ 6 ∷ 1 ∷ 3 ∷ []) ≡ true
check-solution-solved = refl

------------------------------------------------------------------------
-- ═══════════════════════════════════════════════════════════════════
-- EQUIVALENCE: discovered pair-any ≡ hand-crafted attacks
-- ═══════════════════════════════════════════════════════════════════
--
-- The hand-crafted check-attack computes:
--   (ci ≡ᵇ cj) ∨ (|i−j| ≡ᵇ |ci−cj|)
-- Our pair-any i j computes exactly the same thing (with guards).
-- We verify pointwise equivalence on critical test boards.
------------------------------------------------------------------------

private
  hand-check-attack : ℕ → ℕ → Config → Bool
  hand-check-attack i j xs =
    has-index xs i ∧ has-index xs j ∧
    ((safe-index xs i ≡ᵇ safe-index xs j) ∨
     (abs-diff (safe-index xs i) (safe-index xs j) ≡ᵇ abs-diff i j))

  hand-is-dead : Config → Bool
  hand-is-dead xs = any-true (map (λ { (i , j) → hand-check-attack i j xs })
                                  (all-pairs N))
    where
      any-true : List Bool → Bool
      any-true []           = false
      any-true (true ∷ _)   = true
      any-true (false ∷ bs) = any-true bs

-- Equivalence on boards of varying sizes
equiv-empty : synth-is-dead [] ≡ hand-is-dead []
equiv-empty = refl

equiv-00 : synth-is-dead (0 ∷ 0 ∷ []) ≡ hand-is-dead (0 ∷ 0 ∷ [])
equiv-00 = refl

equiv-02 : synth-is-dead (0 ∷ 2 ∷ []) ≡ hand-is-dead (0 ∷ 2 ∷ [])
equiv-02 = refl

equiv-047 : synth-is-dead (0 ∷ 4 ∷ 7 ∷ [])
          ≡ hand-is-dead (0 ∷ 4 ∷ 7 ∷ [])
equiv-047 = refl

equiv-0475 : synth-is-dead (0 ∷ 4 ∷ 7 ∷ 5 ∷ [])
           ≡ hand-is-dead (0 ∷ 4 ∷ 7 ∷ 5 ∷ [])
equiv-0475 = refl

equiv-sol : synth-is-dead (0 ∷ 4 ∷ 7 ∷ 5 ∷ 2 ∷ 6 ∷ 1 ∷ 3 ∷ [])
          ≡ hand-is-dead (0 ∷ 4 ∷ 7 ∷ 5 ∷ 2 ∷ 6 ∷ 1 ∷ 3 ∷ [])
equiv-sol = refl

------------------------------------------------------------------------
-- ═══════════════════════════════════════════════════════════════════
-- INSTANTIATE and SOLVE — Finder through auto-discovered predicates
-- ═══════════════════════════════════════════════════════════════════
------------------------------------------------------------------------

open import CSHRL.EnvironmentClass.CombinatorialPlacementMDP

open CombinatorialPlacementMDP
  Config Action
  synth-is-dead synth-is-solved
  place solved-reward
  all-actions C0 N

-- Full policy rollout: 8 steps from the empty board
run-policy : State → ℕ → ℕ → List Action
run-policy _ _ zero = []
run-policy s depth (suc n) =
  let a = find-policy s depth
  in a ∷ run-policy (proj₁ (step s a)) depth n

-- The auto-discovered predicates produce the same 8-Queens solution
test-solution : run-policy (Ongoing []) N N
  ≡ C0 ∷ C4 ∷ C7 ∷ C5 ∷ C2 ∷ C6 ∷ C1 ∷ C3 ∷ []
test-solution = refl

------------------------------------------------------------------------
-- Partial completions
------------------------------------------------------------------------

-- From 6-queen prefix: complete to [1,3]
test-from-6 : run-policy (Ongoing (0 ∷ 4 ∷ 7 ∷ 5 ∷ 2 ∷ 6 ∷ [])) N 2
  ≡ C1 ∷ C3 ∷ []
test-from-6 = refl

-- From 7-queen prefix: last placement is C3
test-from-7 : run-policy (Ongoing (0 ∷ 4 ∷ 7 ∷ 5 ∷ 2 ∷ 6 ∷ 1 ∷ [])) N 1
  ≡ C3 ∷ []
test-from-7 = refl

-- From 4-queen prefix: complete to [2,6,1,3]
test-from-4 : run-policy (Ongoing (0 ∷ 4 ∷ 7 ∷ 5 ∷ [])) N 4
  ≡ C2 ∷ C6 ∷ C1 ∷ C3 ∷ []
test-from-4 = refl

------------------------------------------------------------------------
-- Independent validation
------------------------------------------------------------------------

private
  all-safe : Config → Bool
  all-safe = go 0
    where
      check-one : ℕ → ℕ → ℕ → Config → Bool
      check-one _ _ _ [] = true
      check-one r1 c1 r2 (c2 ∷ rest) =
        not ((c1 ≡ᵇ c2) ∨ (abs-diff r1 r2 ≡ᵇ abs-diff c1 c2))
        ∧ check-one r1 c1 (suc r2) rest

      go : ℕ → Config → Bool
      go _ [] = true
      go row (c ∷ rest) = check-one row c (suc row) rest ∧ go (suc row) rest

test-valid : all-safe (0 ∷ 4 ∷ 7 ∷ 5 ∷ 2 ∷ 6 ∷ 1 ∷ 3 ∷ []) ≡ true
test-valid = refl

------------------------------------------------------------------------
-- SUMMARY
--
-- The FTL pipeline at N=8 scale:
--
--   93 candidates → 84 conflict indicators → 28 composite features
--                                          → 1 solved feature (len-is 8)
--
-- Auto-discovered predicates:
--   • Match hand-crafted attacks (pointwise equivalence, refl)
--   • Drive the Finder to produce [0,4,7,5,2,6,1,3]
--   • Complete partial placements correctly
--   • Independent all-safe validation confirms correctness
--
-- All --safe, no postulates.
------------------------------------------------------------------------
