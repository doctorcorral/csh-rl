{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Stochastic.FrozenLakeSlippery
--
-- FROZENLAKE 4×4 (slippery) — stochastic variant of the OpenAI Gym
-- benchmark with is_slippery=True.
--
-- Map (standard):
--
--   S F F F     0  1  2  3     S = Start
--   F H F H     4  5  6  7     F = Frozen (safe)
--   F F F H     8  9 10 11     H = Hole (terminal, reward 0)
--   H F F G    12 13 14 15     G = Goal  (terminal, reward 1)
--
-- Slippery mechanics: each action has 1/3 probability of executing
-- the intended direction, 1/3 each for the two perpendicular
-- directions.  E.g., choosing Right → {Right 1/3, Down 1/3, Up 1/3}.
--
-- This is the FIRST stochastic RL benchmark in the synthesis pipeline.
-- Uses StochasticFiniteMDP (expected-trace Finder) for policy
-- computation, then FDMDPSynthesis for CEGIS-based policy synthesis.
--
-- All --safe, no postulates.
------------------------------------------------------------------------

module CSHRL.Tasks.Stochastic.FrozenLakeSlippery where

open import Data.Bool using (Bool; true; false; not; if_then_else_; _∧_; _∨_)
open import Data.Nat  using (ℕ; zero; suc; _+_; _*_; _∸_; _≡ᵇ_; _⊔_; _≤_; z≤n; s≤s; _≤?_)
open import Data.Nat.Properties using (≤-refl)
open import Data.List using (List; []; _∷_; length; map; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (Dec; yes; no; ¬_)

open import CSHRL.Probability.Finite using (Dist; pure; bernoulli)

------------------------------------------------------------------------
-- I. ENVIRONMENT: FrozenLake 4×4 (slippery)
------------------------------------------------------------------------

data Action : Set where
  L D R U : Action

all-actions : List Action
all-actions = L ∷ D ∷ R ∷ U ∷ []

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

------------------------------------------------------------------------
-- II. SLIPPERY STEP FUNCTION
--
-- Gym convention: action a slips to {a, perp-left(a), perp-right(a)}
-- each with probability 1/3 (weight 1 each, total weight 3).
------------------------------------------------------------------------

private
  perp-left : Action → Action
  perp-left L = U
  perp-left D = L
  perp-left R = D
  perp-left U = R

  perp-right : Action → Action
  perp-right L = D
  perp-right D = R
  perp-right R = U
  perp-right U = L

  outcome : ℕ → Action → ℕ × ℕ
  outcome s a = let s' = move s a in (s' , reward-fn s')

-- Uniform branching factor 3 at ALL states (including terminal).
-- Terminal states emit 3 copies of the self-loop to ensure
-- unnormalized expected values are commensurable across the grid.
-- Without this, terminal (weight 1) vs non-terminal (weight 3)
-- makes the memoized DP values grow at different rates (1^k vs 3^k).
slip-step : ℕ → Action → Dist (ℕ × ℕ)
slip-step s a with is-terminal s
... | true  = let r = reward-fn s in
              ((s , r) , 1) ∷ ((s , r) , 1) ∷ ((s , r) , 1) ∷ []
... | false = ( outcome s a              , 1)
            ∷ ( outcome s (perp-left a)  , 1)
            ∷ ( outcome s (perp-right a) , 1)
            ∷ []

------------------------------------------------------------------------
-- Sanity checks
------------------------------------------------------------------------

-- From state 0, action R: outcomes are R→1, D→4, U→0(stay)
test-slip-0R : slip-step 0 R
  ≡ ((1 , 0) , 1) ∷ ((4 , 0) , 1) ∷ ((0 , 0) , 1) ∷ []
test-slip-0R = refl

-- From state 14, action R: outcomes are R→15(goal!), D→14(wall), U→10
test-slip-14R : slip-step 14 R
  ≡ ((15 , 1) , 1) ∷ ((14 , 0) , 1) ∷ ((10 , 0) , 1) ∷ []
test-slip-14R = refl

-- From state 1, action D: outcomes are D→5(hole!), L→0, R→2
test-slip-1D : slip-step 1 D
  ≡ ((5 , 0) , 1) ∷ ((0 , 0) , 1) ∷ ((2 , 0) , 1) ∷ []
test-slip-1D = refl

-- Terminal state: 3 copies of self-loop (uniform branching)
test-slip-terminal : slip-step 15 R
  ≡ ((15 , 1) , 1) ∷ ((15 , 1) , 1) ∷ ((15 , 1) , 1) ∷ []
test-slip-terminal = refl

-- Hole: 3 copies of self-loop (uniform branching)
test-slip-hole : slip-step 5 R
  ≡ ((5 , 0) , 1) ∷ ((5 , 0) , 1) ∷ ((5 , 0) , 1) ∷ []
test-slip-hole = refl

------------------------------------------------------------------------
-- III. STOCHASTIC EC + FINDER
------------------------------------------------------------------------

private
  max-ℕ : ℕ → ℕ → ℕ
  max-ℕ m n with m ≤? n
  ... | yes _ = n
  ... | no  _ = m

open import CSHRL.EnvironmentClass.StochasticFiniteMDP

open StochasticFiniteMDP
  ℕ Action ℕ slip-step
  _≤_ _≤?_ (λ {_} → ≤-refl) max-ℕ 0
  _+_ _*_ 0
  all-actions L 6

------------------------------------------------------------------------
-- IV. MEMOIZED FINDER (deep horizon)
--
-- The recursive Finder at horizon 6 is dominated by tie-breaking
-- (reaching the goal in 6 slippery steps has ~0.1% probability).
-- The memoized DP Finder enables deeper horizons in seconds,
-- producing a meaningful policy where safety-aware actions emerge.
------------------------------------------------------------------------

module Memo = MemoizedStochastic 16 (λ n → n) (λ n → n) 10

private
  bfilterℕ : (ℕ → Bool) → List ℕ → List ℕ
  bfilterℕ _ []       = []
  bfilterℕ p (x ∷ xs) = if p x then x ∷ bfilterℕ p xs else bfilterℕ p xs

all-states : List ℕ
all-states = 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷
             8 ∷ 9 ∷ 10 ∷ 11 ∷ 12 ∷ 13 ∷ 14 ∷ 15 ∷ []

non-terminal-states : List ℕ
non-terminal-states = bfilterℕ (λ s → not (is-terminal s)) all-states

test-nt-count : length non-terminal-states ≡ 11
test-nt-count = refl

-- Probe the memoized Finder's policy at each non-terminal state.
-- At depth 10, expected values break the shallow-horizon ties
-- and reflect genuine safety/progress trade-offs.

test-memo-14 : Memo.fast-policy 14 ≡ D
test-memo-14 = refl

test-memo-13 : Memo.fast-policy 13 ≡ R
test-memo-13 = refl

test-memo-10 : Memo.fast-policy 10 ≡ L
test-memo-10 = refl

test-memo-9  : Memo.fast-policy 9  ≡ D
test-memo-9  = refl

test-memo-8  : Memo.fast-policy 8  ≡ U
test-memo-8  = refl

test-memo-6  : Memo.fast-policy 6  ≡ L
test-memo-6  = refl

test-memo-4  : Memo.fast-policy 4  ≡ L
test-memo-4  = refl

test-memo-3  : Memo.fast-policy 3  ≡ U
test-memo-3  = refl

test-memo-2  : Memo.fast-policy 2  ≡ R
test-memo-2  = refl

test-memo-1  : Memo.fast-policy 1  ≡ U
test-memo-1  = refl

test-memo-0  : Memo.fast-policy 0  ≡ D
test-memo-0  = refl

------------------------------------------------------------------------
-- V. FEATURES AND SYNTHESIS
------------------------------------------------------------------------

data FLFeature : Set where
  row-is : ℕ → FLFeature
  col-is : ℕ → FLFeature

eval-fl : FLFeature → ℕ → Bool
eval-fl (row-is k) s = grid-row s ≡ᵇ k
eval-fl (col-is k) s = grid-col s ≡ᵇ k

private
  range4 : List ℕ
  range4 = 0 ∷ 1 ∷ 2 ∷ 3 ∷ []

discovered : List FLFeature
discovered = map row-is range4 ++ map col-is range4

test-feature-count : length discovered ≡ 8
test-feature-count = refl

open import CSHRL.Synthesis.FiniteDeterministicMDP

private
  det-step : ℕ → Action → ℕ × ℕ
  det-step s a = (move s a , reward-fn (move s a))

open FDMDPSynthesis ℕ Action det-step all-actions
open WithStateFeatures FLFeature eval-fl
open WithCEGIS discovered

------------------------------------------------------------------------
-- VI. FULLY AUTOMATED POLICY SYNTHESIS
--
-- Memoized Finder (depth 10): precomputed finder-map avoids
-- redundant DP recomputation during synthesis.
-- Cascade: D (3 states) → L (3) → U (3) → default R (2).
------------------------------------------------------------------------

_≟ᵃ_ : Action → Action → Bool
L ≟ᵃ L = true
D ≟ᵃ D = true
R ≟ᵃ R = true
U ≟ᵃ U = true
_ ≟ᵃ _ = false

-- Precomputed from individual Memo.fast-policy probes above
finder-map : List (ℕ × Action)
finder-map = (0 , D) ∷ (1 , U) ∷ (2 , R) ∷ (3 , U) ∷ (4 , L) ∷ (6 , L)
           ∷ (8 , U) ∷ (9 , D) ∷ (10 , L) ∷ (13 , R) ∷ (14 , D) ∷ []

private
  bfilter-pair : (ℕ × Action → Bool) → List (ℕ × Action) → List (ℕ × Action)
  bfilter-pair _ [] = []
  bfilter-pair p (x ∷ xs) = if p x then x ∷ bfilter-pair p xs
                             else bfilter-pair p xs

  dt-pool : List PredProg
  dt-pool = initial-vs 0

-- Stage 1: "Is D?" — progress states {0, 9, 14}
obs-is-D : List PredObs
obs-is-D = map (λ { (s , a) → (s , a ≟ᵃ D) }) finder-map

pD : PredProg
pD = synth-decision-tree dt-pool 8 obs-is-D

-- Stage 2: "Is L?" among non-D states — safe retreat {4, 6, 10}
remaining-after-D : List (ℕ × Action)
remaining-after-D = bfilter-pair (λ { (s , a) → not (a ≟ᵃ D) }) finder-map

obs-is-L : List PredObs
obs-is-L = map (λ { (s , a) → (s , a ≟ᵃ L) }) remaining-after-D

pL : PredProg
pL = synth-decision-tree dt-pool 8 obs-is-L

-- Stage 3: "Is U?" among non-D, non-L states — safety {1, 3, 8}
remaining-after-DL : List (ℕ × Action)
remaining-after-DL = bfilter-pair (λ { (s , a) → not (a ≟ᵃ L) }) remaining-after-D

obs-is-U : List PredObs
obs-is-U = map (λ { (s , a) → (s , a ≟ᵃ U) }) remaining-after-DL

pU : PredProg
pU = synth-decision-tree dt-pool 8 obs-is-U

-- Stage 4: R is default {2, 13}

auto-policy : ℕ → Action
auto-policy s =
  if eval pD s then D
  else if eval pL s then L
  else if eval pU s then U
  else R

------------------------------------------------------------------------
-- VII. VERIFICATION
------------------------------------------------------------------------

private
  check-all : List (ℕ × Action) → Bool
  check-all [] = true
  check-all ((s , a) ∷ rest) = (auto-policy s ≟ᵃ a) ∧ check-all rest

test-auto-all-match : check-all finder-map ≡ true
test-auto-all-match = refl
