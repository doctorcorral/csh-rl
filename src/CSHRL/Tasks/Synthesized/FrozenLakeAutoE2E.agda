{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Synthesized.FrozenLakeAutoE2E
--
-- FROZENLAKE 4×4 — fully automated policy synthesis with
-- AUTOMATICALLY GENERATED features.
--
-- Key difference from FrozenLakeE2E: features are derived
-- AUTOMATICALLY from the state count (16) and step function.
-- No human-written feature template (row-is, col-is, etc.).
--
-- The AutoFTL discovers:
--   - 16 state-identity features (state-is k)
--   - 28 factorization features (mod-is/div-is for divisors 2,4,8)
--     → div-is 4 k ≡ row-is k, mod-is 4 k ≡ col-is k (emergent!)
--   - 12 dynamics features (reward, self-loop, leads-terminal)
--   = 56 non-trivial features total
--
-- The cascading CEGIS pipeline synthesizes a PredProg-based policy
-- that matches the Finder at ALL 11 non-terminal states.
--
-- ZERO human feature engineering. All --safe, no postulates.
------------------------------------------------------------------------

module CSHRL.Tasks.Synthesized.FrozenLakeAutoE2E where

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
-- I. ENVIRONMENT (imported from FrozenLakeE2E)
-- ═══════════════════════════════════════════════════════════════════
------------------------------------------------------------------------

import CSHRL.Tasks.Synthesized.FrozenLakeE2E as FL
open FL using ( Action; L; D; R; U; all-actions
              ; step; is-terminal; move; all-states
              ; is-hole; is-goal; _≟ᵃ_ )

------------------------------------------------------------------------
-- ═══════════════════════════════════════════════════════════════════
-- II. AUTO-FEATURE TEMPLATE LANGUAGE
--
-- Features derived AUTOMATICALLY from state count + step function.
-- ZERO human feature engineering.
-- ═══════════════════════════════════════════════════════════════════
------------------------------------------------------------------------

import CSHRL.Synthesis.AutoFeatureNat as AFN
open AFN.AutoFTL Action step all-actions 16 is-terminal

-- Divisors of 16: {2, 4, 8}
-- → mod-is 4 k ≡ col-is k, div-is 4 k ≡ row-is k (emergent!)
test-divisors : divisors ≡ 2 ∷ 4 ∷ 8 ∷ []
test-divisors = refl

-- 16 state-is + 28 factorization + 12 dynamics = 56
test-enum-count : length enumerate-auto ≡ 56
test-enum-count = refl

-- All 56 features are non-trivial for FrozenLake 4×4
test-discovered-count : length discovered ≡ 56
test-discovered-count = refl

-- Enriched: base 56 + 37 threshold features = 93
-- 15 state-ge + 22 factorization thresholds = 37
test-enriched-count : length enumerate-enriched ≡ 93
test-enriched-count = refl

test-discovered-enriched-count : length discovered-enriched ≡ 93
test-discovered-enriched-count = refl

------------------------------------------------------------------------
-- ═══════════════════════════════════════════════════════════════════
-- III. AUTO-FEATURES MATCH HAND-CRAFTED SEMANTICS
--
-- The factorization features AUTOMATICALLY recover the grid
-- coordinates that were hand-crafted in FrozenLakeE2E:
--   div-is 4 k evaluates identically to row-is k
--   mod-is 4 k evaluates identically to col-is k
--
-- Threshold features express grid REGIONS:
--   div-ge 4 k ≡ "row ≥ k"  — bottom k rows
--   mod-ge 4 k ≡ "col ≥ k"  — right of column k
-- ═══════════════════════════════════════════════════════════════════
------------------------------------------------------------------------

-- div-is 4 k ≡ row-is k
test-auto-row0 : eval-auto (div-is 4 0) 2 ≡ true
test-auto-row0 = refl

test-auto-row3 : eval-auto (div-is 4 3) 14 ≡ true
test-auto-row3 = refl

test-auto-row-neg : eval-auto (div-is 4 0) 8 ≡ false
test-auto-row-neg = refl

-- mod-is 4 k ≡ col-is k
test-auto-col2 : eval-auto (mod-is 4 2) 10 ≡ true
test-auto-col2 = refl

test-auto-col0 : eval-auto (mod-is 4 0) 4 ≡ true
test-auto-col0 = refl

-- div-ge 4 k ≡ "row ≥ k" (emergent row REGIONS)
test-auto-row-ge2 : eval-auto (div-ge 4 2) 9 ≡ true
test-auto-row-ge2 = refl

test-auto-row-ge2-neg : eval-auto (div-ge 4 2) 4 ≡ false
test-auto-row-ge2-neg = refl

-- mod-ge 4 k ≡ "col ≥ k" (emergent column REGIONS)
test-auto-col-ge2 : eval-auto (mod-ge 4 2) 6 ≡ true
test-auto-col-ge2 = refl

test-auto-col-ge2-neg : eval-auto (mod-ge 4 2) 5 ≡ false
test-auto-col-ge2-neg = refl

-- Dynamics features (same semantics as hand-crafted)
test-auto-leads-term : eval-auto (leads-terminal D) 1 ≡ true
test-auto-leads-term = refl

test-auto-self-loop : eval-auto (is-self-loop L) 0 ≡ true
test-auto-self-loop = refl

test-auto-reward : eval-auto (has-pos-reward R) 14 ≡ true
test-auto-reward = refl

------------------------------------------------------------------------
-- ═══════════════════════════════════════════════════════════════════
-- IV. FDMDP EC INSTANTIATION + CEGIS
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

module Memo = Finder.Memoized 16 (λ s → s) (λ i → i) 6

open import CSHRL.Synthesis.FiniteDeterministicMDP
open FDMDPSynthesis ℕ Action step all-actions
open WithStateFeatures AutoFeature eval-auto
open WithCEGIS discovered

-- Version space with 56 auto-features at depth 0: 58 candidates
test-vs-size : length (initial-vs 0) ≡ 58
test-vs-size = refl

------------------------------------------------------------------------
-- ═══════════════════════════════════════════════════════════════════
-- V. FULLY AUTOMATED POLICY SYNTHESIS
--
-- ZERO human-provided observations. ZERO human-written features.
-- The complete pipeline:
--   1. Auto-FTL generates 56 features from state count + step
--   2. Finder computes optimal action at every non-terminal state
--   3. Observations GENERATED AUTOMATICALLY from Finder
--   4. Cascading CEGIS synthesizes PredProg per action
--   5. Policy RECONSTRUCTED from PredProg
--   6. Verified: matches Finder at ALL 11 non-terminal states
-- ═══════════════════════════════════════════════════════════════════
------------------------------------------------------------------------

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
-- Uses memoized DP Finder: O(depth × states × actions) vs O(actions^depth).
finder-map : List (ℕ × Action)
finder-map = map (λ s → (s , Memo.policy s)) non-terminal-states

private
  extract : Maybe PredProg → PredProg
  extract (just p) = p
  extract nothing  = falsep

-- Step 2: Cascading CEGIS with AUTO-FEATURES.

-- Stage 1: "Is L optimal?" — depth 0.
obs-is-L : List PredObs
obs-is-L = map (λ { (s , a) → (s , a ≟ᵃ L) }) finder-map

pl : PredProg
pl = extract (synth-rank-pred 0 obs-is-L)

-- Stage 2: "Is R optimal?" — among non-L states, depth 1.
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

------------------------------------------------------------------------
-- ═══════════════════════════════════════════════════════════════════
-- VI. VERIFICATION
-- ═══════════════════════════════════════════════════════════════════
------------------------------------------------------------------------

-- Trajectory from Start (0) to Goal (15)
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

-- Rewards: reaches goal with reward 1
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
  all-safe : List ℕ → Bool
  all-safe []       = true
  all-safe (s ∷ ss) = not (is-hole s) ∧ all-safe ss

  auto-traj-states : List ℕ
  auto-traj-states = 0 ∷ 4 ∷ 8 ∷ 9 ∷ 13 ∷ 14 ∷ 15 ∷ []

test-auto-safe : all-safe auto-traj-states ≡ true
test-auto-safe = refl

-- Auto-policy matches Finder at ALL non-terminal states
private
  check-all : List (ℕ × Action) → Bool
  check-all [] = true
  check-all ((s , a) ∷ rest) = (auto-policy s ≟ᵃ a) ∧ check-all rest

test-auto-all-match : check-all finder-map ≡ true
test-auto-all-match = refl

------------------------------------------------------------------------
-- SUMMARY
--
-- FrozenLake 4×4: FULLY AUTOMATED policy synthesis with
-- AUTOMATICALLY GENERATED features.
--
--   State count (16) + step function
--   → AutoFTL: 56 non-trivial features (ZERO human engineering)
--     - div-is 4 k AUTOMATICALLY = row-is k
--     - mod-is 4 k AUTOMATICALLY = col-is k
--   → Finder oracle (11 states)
--   → Cascading CEGIS (L at depth 0, R at depth 1)
--   → PredProg-based policy
--   → Verified: matches Finder at ALL 11 non-terminal states,
--               trajectory: 0→4→8→9→13→14→15 (optimal path),
--               rewards: 0,0,0,0,0,1 (reaches goal),
--               all states on trajectory are hole-free.
--
-- The synthesized predicates use EMERGENT spatial concepts:
--   pl uses state-is (identity) for the rare L-optimal state
--   pr uses div-is (row) and leads-terminal (dynamics)
--   — these were DISCOVERED, not hand-crafted.
--
-- ZERO human-provided observations. ZERO human-written features.
-- All --safe, no postulates.
------------------------------------------------------------------------
