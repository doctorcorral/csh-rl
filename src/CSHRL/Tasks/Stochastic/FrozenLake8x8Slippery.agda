{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Stochastic.FrozenLake8x8Slippery
--
-- FROZENLAKE 8×8 (slippery) — stochastic variant scaling to 64 states.
--
-- Standard OpenAI Gym map:
--
--   S F F F F F F F     0  1  2  3  4  5  6  7
--   F F F F F F F F     8  9 10 11 12 13 14 15
--   F F F H F F F F    16 17 18 19 20 21 22 23
--   F F F F F H F F    24 25 26 27 28 29 30 31
--   F F F H F F F F    32 33 34 35 36 37 38 39
--   F H H F F F H F    40 41 42 43 44 45 46 47
--   F H F F H F H F    48 49 50 51 52 53 54 55
--   F F F H F F F G    56 57 58 59 60 61 62 63
--
-- 64 states, 53 non-terminal (10 holes + 1 goal).
-- Slippery: 1/3 intended, 1/3 perp-left, 1/3 perp-right.
-- Uniform branching factor 3 at all states (including terminal).
--
-- Uses MemoizedStochastic Finder for policy computation.
-- All --safe, no postulates.
------------------------------------------------------------------------

module CSHRL.Tasks.Stochastic.FrozenLake8x8Slippery where

open import Data.Bool using (Bool; true; false; not; if_then_else_; _∧_; _∨_)
open import Data.Nat  using (ℕ; zero; suc; _+_; _*_; _∸_; _≡ᵇ_; _⊔_; _≤_; z≤n; s≤s; _≤?_)
open import Data.Nat.Properties using (≤-refl)
open import Data.List using (List; []; _∷_; length; map; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)

open import CSHRL.Probability.Finite using (Dist; pure; bernoulli)
open import CSHRL.Utils.NatArithmetic using (divℕ; modℕ; range)

------------------------------------------------------------------------
-- I. ENVIRONMENT: FrozenLake 8×8 (arithmetic-based)
------------------------------------------------------------------------

data Action : Set where
  L D R U : Action

all-actions : List Action
all-actions = L ∷ D ∷ R ∷ U ∷ []

is-hole : ℕ → Bool
is-hole s = (s ≡ᵇ 19) ∨ (s ≡ᵇ 29) ∨ (s ≡ᵇ 35) ∨ (s ≡ᵇ 41) ∨
            (s ≡ᵇ 42) ∨ (s ≡ᵇ 46) ∨ (s ≡ᵇ 49) ∨ (s ≡ᵇ 52) ∨
            (s ≡ᵇ 54) ∨ (s ≡ᵇ 59)

is-goal : ℕ → Bool
is-goal s = s ≡ᵇ 63

is-terminal : ℕ → Bool
is-terminal s = is-hole s ∨ is-goal s

reward-fn : ℕ → ℕ
reward-fn s = if s ≡ᵇ 63 then 1 else 0

private
  go : ℕ → ℕ → Action → ℕ
  go r c L = if c ≡ᵇ 0 then r * 8 + c else r * 8 + (c ∸ 1)
  go r c D = if r ≡ᵇ 7 then r * 8 + c else (r + 1) * 8 + c
  go r c R = if c ≡ᵇ 7 then r * 8 + c else r * 8 + (c + 1)
  go r c U = if r ≡ᵇ 0 then r * 8 + c else (r ∸ 1) * 8 + c

move : ℕ → Action → ℕ
move s a = if is-terminal s then s else go (divℕ s 8) (modℕ s 8) a

------------------------------------------------------------------------
-- II. SLIPPERY STEP (uniform branching factor 3)
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

test-slip-0R : slip-step 0 R
  ≡ ((1 , 0) , 1) ∷ ((8 , 0) , 1) ∷ ((0 , 0) , 1) ∷ []
test-slip-0R = refl

-- State 62 (row 7, col 6): R→63(goal), D→62(wall), U→54
test-slip-62R : slip-step 62 R
  ≡ ((63 , 1) , 1) ∷ ((62 , 0) , 1) ∷ ((54 , 0) , 1) ∷ []
test-slip-62R = refl

test-slip-terminal : slip-step 63 R
  ≡ ((63 , 1) , 1) ∷ ((63 , 1) , 1) ∷ ((63 , 1) , 1) ∷ []
test-slip-terminal = refl

test-slip-hole : slip-step 19 R
  ≡ ((19 , 0) , 1) ∷ ((19 , 0) , 1) ∷ ((19 , 0) , 1) ∷ []
test-slip-hole = refl

------------------------------------------------------------------------
-- III. STOCHASTIC EC + MEMOIZED FINDER
------------------------------------------------------------------------

private
  max-ℕ : ℕ → ℕ → ℕ
  max-ℕ m n with m ≤? n
  ... | yes p = n
  ... | no  p = m

open import CSHRL.EnvironmentClass.StochasticFiniteMDP

open StochasticFiniteMDP
  ℕ Action ℕ slip-step
  _≤_ _≤?_ (λ {_} → ≤-refl) max-ℕ 0
  _+_ _*_ 0
  all-actions L 6

module Memo = MemoizedStochastic 64 (λ n → n) (λ n → n) 10

------------------------------------------------------------------------
-- IV. NON-TERMINAL STATES
------------------------------------------------------------------------

private
  bfilterℕ : (ℕ → Bool) → List ℕ → List ℕ
  bfilterℕ _ []       = []
  bfilterℕ p (x ∷ xs) = if p x then x ∷ bfilterℕ p xs else bfilterℕ p xs

all-states : List ℕ
all-states = range 64

non-terminal-states : List ℕ
non-terminal-states = bfilterℕ (λ s → not (is-terminal s)) all-states

test-nt-count : length non-terminal-states ≡ 53
test-nt-count = refl

------------------------------------------------------------------------
-- V. POLICY VERIFICATION
--
-- Probe Memo.fast-policy at key states. The depth-10 memoized Finder
-- produces a safety-aware policy across the 8×8 grid.
------------------------------------------------------------------------

-- Probe actual policy at key states (depth-10 memoized Finder)
test-memo-0 : Memo.fast-policy 0 ≡ L
test-memo-0 = refl

test-memo-62 : Memo.fast-policy 62 ≡ D
test-memo-62 = refl

test-memo-61 : Memo.fast-policy 61 ≡ D
test-memo-61 = refl

test-memo-60 : Memo.fast-policy 60 ≡ D
test-memo-60 = refl

test-memo-56 : Memo.fast-policy 56 ≡ D
test-memo-56 = refl

test-memo-57 : Memo.fast-policy 57 ≡ D
test-memo-57 = refl

------------------------------------------------------------------------
-- VI. FEATURES AND SYNTHESIS
------------------------------------------------------------------------

-- Grid coordinates for 8×8
grid-row : ℕ → ℕ
grid-row s = divℕ s 8

grid-col : ℕ → ℕ
grid-col s = modℕ s 8

data FLFeature : Set where
  row-is : ℕ → FLFeature
  col-is : ℕ → FLFeature

eval-fl : FLFeature → ℕ → Bool
eval-fl (row-is k) s = grid-row s ≡ᵇ k
eval-fl (col-is k) s = grid-col s ≡ᵇ k

private
  range8 : List ℕ
  range8 = 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ []

-- row/col: decision tree builds conjunctions (e.g. row-is 7 ∧ col-is 6)
discovered : List FLFeature
discovered = map row-is range8 ++ map col-is range8

test-feature-count : length discovered ≡ 16
test-feature-count = refl

open import CSHRL.Synthesis.FiniteDeterministicMDP

private
  det-step : ℕ → Action → ℕ × ℕ
  det-step s a = (move s a , reward-fn (move s a))

open FDMDPSynthesis ℕ Action det-step all-actions
open WithStateFeatures FLFeature eval-fl
open WithCEGIS discovered

------------------------------------------------------------------------
-- VII. FULLY AUTOMATED POLICY SYNTHESIS
--
-- Memoized Finder (depth 10): finder-map from all 53 non-terminal states.
-- Cascade order determined by policy distribution.
------------------------------------------------------------------------

_≟ᵃ_ : Action → Action → Bool
L ≟ᵃ L = true
D ≟ᵃ D = true
R ≟ᵃ R = true
U ≟ᵃ U = true
_ ≟ᵃ _ = false

finder-map : List (ℕ × Action)
finder-map = map (λ s → (s , Memo.fast-policy s)) non-terminal-states

private
  bfilter-pair : (ℕ × Action → Bool) → List (ℕ × Action) → List (ℕ × Action)
  bfilter-pair _ [] = []
  bfilter-pair p (x ∷ xs) = if p x then x ∷ bfilter-pair p xs
                             else bfilter-pair p xs

  dt-pool : List PredProg
  dt-pool = initial-vs 0

-- Cascade: D first, then L, U, R default. Decision tree builds conjunctions.
obs-is-D : List PredObs
obs-is-D = map (λ { (s , a) → (s , a ≟ᵃ D) }) finder-map

pD : PredProg
pD = synth-decision-tree dt-pool 8 obs-is-D

remaining-after-D : List (ℕ × Action)
remaining-after-D = bfilter-pair (λ { (s , a) → not (a ≟ᵃ D) }) finder-map

obs-is-L : List PredObs
obs-is-L = map (λ { (s , a) → (s , a ≟ᵃ L) }) remaining-after-D

pL : PredProg
pL = synth-decision-tree dt-pool 8 obs-is-L

remaining-after-DL : List (ℕ × Action)
remaining-after-DL = bfilter-pair (λ { (s , a) → not (a ≟ᵃ L) }) remaining-after-D

obs-is-U : List PredObs
obs-is-U = map (λ { (s , a) → (s , a ≟ᵃ U) }) remaining-after-DL

pU : PredProg
pU = synth-decision-tree dt-pool 8 obs-is-U

-- R is default

auto-policy : ℕ → Action
auto-policy s =
  if eval pD s then D
  else if eval pL s then L
  else if eval pU s then U
  else R

------------------------------------------------------------------------
-- VIII. VERIFICATION
------------------------------------------------------------------------

private
  check-all : List (ℕ × Action) → Bool
  check-all [] = true
  check-all ((s , a) ∷ rest) = (auto-policy s ≟ᵃ a) ∧ check-all rest

test-auto-all-match : check-all finder-map ≡ true
test-auto-all-match = refl

------------------------------------------------------------------------
-- SUMMARY
--
-- FrozenLake 8×8 Slippery: 64 states, 53 non-terminal.
-- MemoizedStochastic at depth 10 + decision-tree CEGIS synthesis.
-- Verified: auto-policy matches Finder at all 53 non-terminal states.
------------------------------------------------------------------------
