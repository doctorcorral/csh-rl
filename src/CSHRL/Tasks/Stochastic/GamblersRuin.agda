{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- GamblersRuin: A Classic Stochastic MDP
--
-- A gambler starts with $1 out of $2 needed to win.
-- Each round they can BET or QUIT:
-- - BET: 50% chance to win $1, 50% chance to lose $1
-- - QUIT: stay at current wealth
-- 
-- Terminal states: $0 (ruin) or $2 (goal reached)
--
-- This is a classic absorbing Markov chain from probability theory,
-- demonstrating CSHRL's stochastic extension on a well-studied problem.
--
-- OPTIMAL POLICY: Bet (maximizes probability of reaching goal)
-- With fair coin (p=0.5), betting gives P(win) = 1/2 from middle.
------------------------------------------------------------------------

module CSHRL.Tasks.Stochastic.GamblersRuin where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; _≤?_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Codata.Guarded.Stream using (head; tail)

open import CSHRL.Probability.Finite using (Dist; pure; _>>=_; fmap; bernoulli)

------------------------------------------------------------------------
-- MDP Definition
------------------------------------------------------------------------

-- States: Wealth levels 0, 1, 2
-- Ruin = $0 (terminal, lost)
-- Middle = $1 (can bet)
-- Goal = $2 (terminal, won)
data State : Set where
  Ruin   : State   -- $0, terminal (lost)
  Middle : State   -- $1, can still play
  Goal   : State   -- $2, terminal (won)

-- Actions: Bet or Quit
data Action : Set where
  Bet  : Action   -- Gamble $1
  Quit : Action   -- Stop playing

-- Rewards are natural numbers
Reward : Set
Reward = ℕ

-- Stochastic step function
-- BET from Middle: 50% → Goal (reward 1), 50% → Ruin (reward 0)
-- QUIT from Middle: 100% → Middle (reward 0)
-- From terminal states: always stay (reward 0)
step : State → Action → Dist (State × Reward)
step Middle Bet  = bernoulli (Goal , 1) 1 (Ruin , 0) 1   -- Fair coin
step Middle Quit = pure (Middle , 0)                      -- Stay put
step Ruin   _    = pure (Ruin , 0)                        -- Terminal (lost)
step Goal   _    = pure (Goal , 0)                        -- Terminal (won)

------------------------------------------------------------------------
-- Reward Structure
------------------------------------------------------------------------

_≤ᵣ_ : Reward → Reward → Set
_≤ᵣ_ = _≤_

≤ᵣ-dec : (r s : Reward) → Dec (r ≤ᵣ s)
≤ᵣ-dec = _≤?_

≤ᵣ-refl : ∀ {r} → r ≤ᵣ r
≤ᵣ-refl = ≤-refl

_+ᵣ_ : Reward → Reward → Reward
_+ᵣ_ = _+_

_*ᵣ_ : ℕ → Reward → Reward
_*ᵣ_ = _*_

zeroᵣ : Reward
zeroᵣ = 0

max : Reward → Reward → Reward
max m n with m ≤? n
... | yes _ = n
... | no  _ = m

bottom : Reward
bottom = 0

------------------------------------------------------------------------
-- Finiteness Requirements
------------------------------------------------------------------------

all-actions : List Action
all-actions = Bet ∷ Quit ∷ []

default-action : Action
default-action = Quit

horizon : ℕ
horizon = 3

------------------------------------------------------------------------
-- Import Stochastic EC
------------------------------------------------------------------------

open import CSHRL.EnvironmentClass.StochasticFiniteMDP

open StochasticFiniteMDP 
  State Action Reward step 
  _≤ᵣ_ ≤ᵣ-dec ≤ᵣ-refl max bottom 
  _+ᵣ_ _*ᵣ_ zeroᵣ 
  all-actions default-action horizon

------------------------------------------------------------------------
-- Expected Values Analysis
------------------------------------------------------------------------

-- From Middle state with Bet action:
-- E[immediate] = (1 * 1 + 0 * 1) / 2 = 0.5 (unnormalized: 1, weight 2)

-- From Middle state with Quit action:
-- E[immediate] = 0

-- Betting has higher expected immediate reward than quitting.
-- This matches the classical analysis: with a fair coin,
-- betting gives the best chance of reaching the goal.

------------------------------------------------------------------------
-- Ranking Tests
------------------------------------------------------------------------

test-trace-bet : List Reward
test-trace-bet = expected-trace-action Middle Bet 1

test-trace-quit : List Reward
test-trace-quit = expected-trace-action Middle Quit 1

test-ranking : List Action
test-ranking = find-ranking Middle horizon

test-policy : Action
test-policy = find-policy Middle horizon

------------------------------------------------------------------------
-- LEXICOGRAPHIC PRESERVATION PROOFS
------------------------------------------------------------------------

-- Same structure as CoinFlip: lexicographic comparison with conditional tail.

-- Helper: 1 ≤ 0 is absurd
1≤0-absurd : 1 ≤ 0 → ∀ {A : Set} → A
1≤0-absurd ()

------------------------------------------------------------------------
-- Head Preservation
------------------------------------------------------------------------

gambler-head-lex-≤ : ∀ s a b →
                     s ranks a ≤ b →
                     head (expected-action-value s a) ≤ᵣ head (expected-action-value s b)

-- Terminal states: both actions give 0 immediate reward
gambler-head-lex-≤ Ruin Bet Bet _ = ≤ᵣ-refl
gambler-head-lex-≤ Ruin Bet Quit p = proj₁ p
gambler-head-lex-≤ Ruin Quit Bet p = proj₁ p
gambler-head-lex-≤ Ruin Quit Quit _ = ≤ᵣ-refl
gambler-head-lex-≤ Goal Bet Bet _ = ≤ᵣ-refl
gambler-head-lex-≤ Goal Bet Quit p = proj₁ p
gambler-head-lex-≤ Goal Quit Bet p = proj₁ p
gambler-head-lex-≤ Goal Quit Quit _ = ≤ᵣ-refl

-- Middle state: the interesting case
gambler-head-lex-≤ Middle Bet Bet _ = ≤ᵣ-refl
gambler-head-lex-≤ Middle Quit Quit _ = ≤ᵣ-refl
gambler-head-lex-≤ Middle Quit Bet _ = z≤n  -- 0 ≤ 1 ✓
gambler-head-lex-≤ Middle Bet Quit (h≤ , _) = 1≤0-absurd h≤  -- 1 ≤ 0 is absurd

------------------------------------------------------------------------
-- Tail Preservation (Conditional)
------------------------------------------------------------------------

gambler-tail-lex-≤ : ∀ s a b →
                     s ranks a ≤ b →
                     head (expected-action-value s a) ≡ head (expected-action-value s b) →
                     tail (expected-action-value s a) ≤ₛ-lex tail (expected-action-value s b)

-- Terminal states: reflexivity
gambler-tail-lex-≤ Ruin _ _ _ _ = ≤ₛ-lex-refl _
gambler-tail-lex-≤ Goal _ _ _ _ = ≤ₛ-lex-refl _

-- Middle state with same action: reflexivity
gambler-tail-lex-≤ Middle Bet Bet _ _ = ≤ₛ-lex-refl _
gambler-tail-lex-≤ Middle Quit Quit _ _ = ≤ₛ-lex-refl _

-- Middle state, Quit ≤ Bet: 0 ≡ 1 is absurd
gambler-tail-lex-≤ Middle Quit Bet _ ()

-- Middle state, Bet ≤ Quit: impossible ranking
gambler-tail-lex-≤ Middle Bet Quit (h≤ , _) _ = 1≤0-absurd h≤

------------------------------------------------------------------------
-- Verified CoindHomo Instance
------------------------------------------------------------------------

open WithLexPreservation gambler-head-lex-≤ gambler-tail-lex-≤ public

------------------------------------------------------------------------
-- Policy Verification
------------------------------------------------------------------------

-- The policy from Middle should be Bet (higher expected value)
test-policy-is-bet : test-policy ≡ Bet
test-policy-is-bet = refl

------------------------------------------------------------------------
-- Classical Connection
--
-- The Gambler's Ruin problem has a well-known solution:
-- - With fair coin (p = 0.5), P(reaching goal from $k out of $N) = k/N
-- - From Middle ($1 out of $2), P(win) = 1/2
-- - Quitting gives P(win) = 0 (stay at $1 forever, never reach $2)
--
-- CSHRL correctly identifies Bet as the optimal action because:
-- - E[reward | Bet] = 0.5 (half chance of getting 1)
-- - E[reward | Quit] = 0 (no reward, stuck forever)
--
-- The lexicographic preservation proof works identically to CoinFlip
-- because both have the same structure: a fair coin flip vs. staying put.
------------------------------------------------------------------------
