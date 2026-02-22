{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- Maze via Synthesis: Postulate-Free Preservation
--
-- The classic Maze task uses `postulate preserves-impl`.
-- This module replaces that postulate with a verified proof
-- using the synthesis infrastructure:
--   - Decision tree ranking: Fwd > Bwd at all positions
--   - Feature coherence (identity features)
--   - Preservation proven at each state
--   - CoindHomo assembled via preservation transfer
--
-- This demonstrates: synthesis can ELIMINATE postulates from
-- existing tasks, upgrading Classic → Verified.
------------------------------------------------------------------------

module CSHRL.Tasks.Synthesized.MazeSynth where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _≤_; _⊔_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst)
open import Codata.Guarded.Stream using (Stream; head; tail; tabulate)
open import Function using (_∘_)
open import Data.List using (List; _∷_; [])
open import Data.Unit using (⊤; tt)

------------------------------------------------------------------------
-- Domain (same as Classic.Maze)
------------------------------------------------------------------------

data State : Set where
  P0 : State
  P1 : State
  P2 : State

data Action : Set where
  Fwd : Action
  Bwd : Action

move : State → Action → State
move P0 Fwd = P1
move P0 Bwd = P0
move P1 Fwd = P2
move P1 Bwd = P0
move P2 Fwd = P2
move P2 Bwd = P1

reward-fn : State → ℕ
reward-fn P2 = 1
reward-fn _  = 0

step : State → Action → State × ℕ
step s a = (move s a , reward-fn (move s a))

all-actions : List Action
all-actions = Fwd ∷ Bwd ∷ []

------------------------------------------------------------------------
-- Open Synthesis Infrastructure
------------------------------------------------------------------------

open import CSHRL.Synthesis.Core
open SynthesisCore State Action step all-actions

------------------------------------------------------------------------
-- Observations (all 6 transitions)
------------------------------------------------------------------------

observations : List Observation
observations =
  obs P0 Fwd P1 0 ∷  obs P0 Bwd P0 0 ∷
  obs P1 Fwd P2 1 ∷  obs P1 Bwd P0 0 ∷
  obs P2 Fwd P2 1 ∷  obs P2 Bwd P1 0 ∷ []

observations-valid : AllValid observations
observations-valid = refl , refl , refl , refl , refl , refl , tt

------------------------------------------------------------------------
-- Feature Setup: Identity abstraction
------------------------------------------------------------------------

open WithFeatures State (λ s → s)

------------------------------------------------------------------------
-- Decision Tree: Fwd > Bwd everywhere
------------------------------------------------------------------------

rank-cmp : Action → Action → Bool
rank-cmp Fwd Fwd = true
rank-cmp Fwd Bwd = false   -- Fwd is NOT dominated by Bwd
rank-cmp Bwd Fwd = true    -- Bwd IS dominated by Fwd
rank-cmp Bwd Bwd = true

ranking-tree : RankTree
ranking-tree = rleaf rank-cmp

------------------------------------------------------------------------
-- Feature Coherence (trivial for identity)
------------------------------------------------------------------------

coherent : FeatureCoherent
coherent s₁ .s₁ a b refl av = av

------------------------------------------------------------------------
-- Solve Properties
--
-- Key facts:
--   solve P2 n = 1  for all n
--   solve P1 n = 1  for all n
--   solve P0 0 = 0
--   solve P0 (suc n) = 1  for all n
------------------------------------------------------------------------

≤ₛ-refl : ∀ (s : Stream ℕ) → s ≤ₛ s
head≤ (≤ₛ-refl s) = ≤-refl
tail≤ (≤ₛ-refl s) = ≤ₛ-refl (tail s)

mutual
  solve-P2 : ∀ n → solve P2 n ≡ 1
  solve-P2 zero = refl
  solve-P2 (suc n) rewrite solve-P2 n | solve-P1 n = refl

  solve-P1 : ∀ n → solve P1 n ≡ 1
  solve-P1 zero = refl
  solve-P1 (suc zero) rewrite solve-P2 zero = refl
  solve-P1 (suc (suc n)) rewrite solve-P2 (suc n) | solve-P0-suc n = refl

  solve-P0-suc : ∀ n → solve P0 (suc n) ≡ 1
  solve-P0-suc zero rewrite solve-P1 zero = refl
  solve-P0-suc (suc n) rewrite solve-P1 (suc n) | solve-P0-suc n = refl

------------------------------------------------------------------------
-- Stream Ordering Infrastructure
------------------------------------------------------------------------

iter-head : ℕ → Stream ℕ → ℕ
iter-head zero    s = head s
iter-head (suc n) s = iter-head n (tail s)

iter-head-tab : ∀ (f : ℕ → ℕ) n → iter-head n (tabulate f) ≡ f n
iter-head-tab f zero    = refl
iter-head-tab f (suc n) = iter-head-tab (f ∘ suc) n

iter-head-val : ∀ s n → iter-head n (value s) ≡ solve s n
iter-head-val s n = iter-head-tab (solve s) n

HeadGen : Stream ℕ → Stream ℕ → Set
HeadGen s₁ s₂ = ∀ n → iter-head n s₁ ≤ iter-head n s₂

build-≤ₛ : ∀ (s₁ s₂ : Stream ℕ) → HeadGen s₁ s₂ → s₁ ≤ₛ s₂
head≤ (build-≤ₛ s₁ s₂ gen) = gen 0
tail≤ (build-≤ₛ s₁ s₂ gen) = build-≤ₛ (tail s₁) (tail s₂) (λ n → gen (suc n))

-- Generic generator: if solve s₁ n ≤ solve s₂ n for all n, streams are ordered
gen-from-solve : ∀ s₁ s₂ → (∀ n → solve s₁ n ≤ solve s₂ n) →
  HeadGen (value s₁) (value s₂)
gen-from-solve s₁ s₂ h n =
  subst (λ x → x ≤ iter-head n (value s₂)) (sym (iter-head-val s₁ n))
    (subst (solve s₁ n ≤_) (sym (iter-head-val s₂ n)) (h n))

------------------------------------------------------------------------
-- Solve Ordering Lemmas
------------------------------------------------------------------------

-- solve P0 n ≤ solve P1 n
solve-P0≤P1 : ∀ n → solve P0 n ≤ solve P1 n
solve-P0≤P1 zero = z≤n
solve-P0≤P1 (suc n) rewrite solve-P0-suc n | solve-P1 (suc n) = ≤-refl

-- solve P0 n ≤ solve P2 n
solve-P0≤P2 : ∀ n → solve P0 n ≤ solve P2 n
solve-P0≤P2 zero = z≤n
solve-P0≤P2 (suc n) rewrite solve-P0-suc n | solve-P2 (suc n) = ≤-refl

-- solve P1 n ≤ solve P2 n
solve-P1≤P2 : ∀ n → solve P1 n ≤ solve P2 n
solve-P1≤P2 n rewrite solve-P1 n | solve-P2 n = ≤-refl

------------------------------------------------------------------------
-- Value Stream Orderings
------------------------------------------------------------------------

P0≤P1 : value P0 ≤ₛ value P1
P0≤P1 = build-≤ₛ (value P0) (value P1) (gen-from-solve P0 P1 solve-P0≤P1)

P0≤P2 : value P0 ≤ₛ value P2
P0≤P2 = build-≤ₛ (value P0) (value P2) (gen-from-solve P0 P2 solve-P0≤P2)

P1≤P2 : value P1 ≤ₛ value P2
P1≤P2 = build-≤ₛ (value P1) (value P2) (gen-from-solve P1 P2 solve-P1≤P2)

------------------------------------------------------------------------
-- Preservation at Each State
------------------------------------------------------------------------

preserves-P0 : PreservesAt ranking-tree P0
preserves-P0 Fwd Fwd _ = ≤ₛ-refl (action-value P0 Fwd)
preserves-P0 Bwd Bwd _ = ≤ₛ-refl (action-value P0 Bwd)
head≤ (preserves-P0 Bwd Fwd _) = ≤-refl
tail≤ (preserves-P0 Bwd Fwd _) = P0≤P1

preserves-P1 : PreservesAt ranking-tree P1
preserves-P1 Fwd Fwd _ = ≤ₛ-refl (action-value P1 Fwd)
preserves-P1 Bwd Bwd _ = ≤ₛ-refl (action-value P1 Bwd)
head≤ (preserves-P1 Bwd Fwd _) = z≤n
tail≤ (preserves-P1 Bwd Fwd _) = P0≤P2

preserves-P2 : PreservesAt ranking-tree P2
preserves-P2 Fwd Fwd _ = ≤ₛ-refl (action-value P2 Fwd)
preserves-P2 Bwd Bwd _ = ≤ₛ-refl (action-value P2 Bwd)
head≤ (preserves-P2 Bwd Fwd _) = z≤n
tail≤ (preserves-P2 Bwd Fwd _) = P1≤P2

------------------------------------------------------------------------
-- Assemble CoindHomo via Preservation Transfer
------------------------------------------------------------------------

rep-preserves : ∀ s → PreservesAt ranking-tree s
rep-preserves P0 = preserves-P0
rep-preserves P1 = preserves-P1
rep-preserves P2 = preserves-P2

------------------------------------------------------------------------
-- Assemble CoindHomo directly
------------------------------------------------------------------------

tree-preserves-all : ∀ a b s →
  TreeRanks ranking-tree s a b →
  action-value s a ≤ₛ action-value s b
tree-preserves-all a b s =
  preservation-transfer ranking-tree coherent s s refl
    (rep-preserves s) a b

------------------------------------------------------------------------
-- RESULT: Verified CoindHomo, zero postulates.
--
-- Compare with Classic.Maze which uses:
--   postulate preserves-impl : ...
--
-- This version proves preservation from solve properties,
-- using the synthesis infrastructure for structure.
------------------------------------------------------------------------

instance
  MazeSynthHomo : CoindHomo
  MazeSynthHomo = record
    { _≤ₐ_ = TreeRanks ranking-tree
    ; preserves = tree-preserves-all
    }

verified-homo : CoindHomo
verified-homo = MazeSynthHomo

-- Verify: the ranking agrees with the Finder
test-tree-P0 : tree-rank ranking-tree P0 Bwd Fwd ≡ true
test-tree-P0 = refl

test-tree-P1 : tree-rank ranking-tree P1 Bwd Fwd ≡ true
test-tree-P1 = refl

test-tree-P2 : tree-rank ranking-tree P2 Bwd Fwd ≡ true
test-tree-P2 = refl
