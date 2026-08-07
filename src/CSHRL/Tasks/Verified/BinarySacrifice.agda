{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Verified.BinarySacrifice
--
-- A concrete MDP proving CoinductiveHomomorphism is strictly more
-- general than CoindHomo.
--
-- The "Sacrifice Now, Gain Later" environment:
--
--   Start ──GoParadise (r=0)──▸ Paradise ⟳ (r=1)
--         ╲
--          ╲─GoTrap (r=1)──▸ Trap ⟳ (r=0)
--
-- GoParadise sacrifices immediate reward (0 vs 1) but leads to
-- Paradise (reward 1 forever). GoTrap grabs the immediate reward
-- but leads to Trap (reward 0 forever).
--
-- Results proved in this module:
--   ✓ CoinductiveHomomorphism correctly ranks GoParadise > GoTrap
--     (Paradise is a better state than Trap)
--   ✗ CoindHomo cannot rank GoTrap ≤ GoParadise
--     (immediate reward 1 > 0 violates head≤)
--   ✗ CoindHomo cannot rank GoParadise ≤ GoTrap either
--     (value Paradise > value Trap violates tail≤ then head≤)
--
-- The old Finder (comparing action-value traces) would pick GoTrap:
--   trace(GoTrap)     = [1, 0, 0, ...]   ← wins lexicographically
--   trace(GoParadise) = [0, 1, 1, ...]
--
-- The adapted Finder (comparing successor-value traces) picks GoParadise:
--   future(GoTrap)     = [0, 0, 0, ...]
--   future(GoParadise) = [1, 1, 1, ...]   ← wins
------------------------------------------------------------------------

module CSHRL.Tasks.Verified.BinarySacrifice where

open import Data.Nat using (ℕ; zero; suc; _⊔_; _≤_; z≤n)
open import Data.Nat.Properties using (≤-refl)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Codata.Guarded.Stream using (Stream; head; tail; tabulate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)

open import CSHRL.Core
open import CSHRL.Core.CoinductiveHomomorphism

------------------------------------------------------------------------
-- MDP Definition
------------------------------------------------------------------------

data State : Set where
  Start Paradise Trap : State

data Action : Set where
  GoParadise GoTrap : Action

step : State → Action → State × ℕ
step Start GoParadise = Paradise , 0
step Start GoTrap     = Trap , 1
step Paradise _       = Paradise , 1
step Trap _           = Trap , 0

all-actions : List Action
all-actions = GoParadise ∷ GoTrap ∷ []

open Core State Action ℕ step _≤_ _⊔_ 0 all-actions
open SuccessorCore State Action ℕ step _≤_ _⊔_ 0 all-actions

------------------------------------------------------------------------
-- Absorbing state values are constant
------------------------------------------------------------------------

solve-trap : ∀ n → solve Trap n ≡ 0
solve-trap zero    = refl
solve-trap (suc n) rewrite solve-trap n = refl

solve-paradise : ∀ n → solve Paradise n ≡ 1
solve-paradise zero    = refl
solve-paradise (suc n) rewrite solve-paradise n = refl

------------------------------------------------------------------------
-- Stream ordering helpers
------------------------------------------------------------------------

tabulate-≤ₛ : ∀ {f g : ℕ → ℕ} →
  (∀ n → f n ≤ g n) → tabulate f ≤ₛ tabulate g
head≤ (tabulate-≤ₛ pw) = pw zero
tail≤ (tabulate-≤ₛ pw) = tabulate-≤ₛ (λ n → pw (suc n))

≤ₛ-refl : ∀ (s : StreamR) → s ≤ₛ s
head≤ (≤ₛ-refl s) = ≤-refl
tail≤ (≤ₛ-refl s) = ≤ₛ-refl (tail s)

value-trap≤paradise : value Trap ≤ₛ value Paradise
value-trap≤paradise = tabulate-≤ₛ lemma
  where
    lemma : ∀ n → solve Trap n ≤ solve Paradise n
    lemma n rewrite solve-trap n | solve-paradise n = z≤n

------------------------------------------------------------------------
-- ✓ CoinductiveHomomorphism holds
--
-- GoParadise is ranked above GoTrap at Start because Paradise is a
-- better state than Trap—regardless of the immediate transition reward.
------------------------------------------------------------------------

ranking : State → Action → Action → Set
ranking Start GoTrap     GoParadise = ⊤
ranking Start GoParadise GoParadise = ⊤
ranking Start GoTrap     GoTrap     = ⊤
ranking Start GoParadise GoTrap     = ⊥
ranking Paradise _ _ = ⊤
ranking Trap     _ _ = ⊤

sacrifice-homomorphism : CoinductiveHomomorphism
sacrifice-homomorphism = record { _≤ₐ_ = ranking ; preserves = prf }
  where
    prf : ∀ a b s → ranking s a b →
          successor-value s a ≤ₛ successor-value s b
    prf GoTrap     GoParadise Start   tt = value-trap≤paradise
    prf GoParadise GoParadise Start   tt = ≤ₛ-refl (value Paradise)
    prf GoTrap     GoTrap     Start   tt = ≤ₛ-refl (value Trap)
    prf GoParadise GoTrap     Start   ()
    prf _          _          Paradise tt = ≤ₛ-refl (value Paradise)
    prf _          _          Trap     tt = ≤ₛ-refl (value Trap)

------------------------------------------------------------------------
-- ✗ CoindHomo cannot express the correct ranking
--
-- Neither direction works at Start. The actions are "incomparable"
-- under CoindHomo, even though one is clearly better.
------------------------------------------------------------------------

-- Forward: GoTrap ≤ GoParadise requires head≤: 1 ≤ 0
coindHomo-forward-impossible :
  (homo : CoindHomo) →
  CoindHomo._≤ₐ_ homo Start GoTrap GoParadise → ⊥
coindHomo-forward-impossible homo prf
  with head≤ (CoindHomo.preserves homo GoTrap GoParadise Start prf)
... | ()

-- Reverse: GoParadise ≤ GoTrap requires tail≤, which at the head gives 1 ≤ 0
coindHomo-reverse-impossible :
  (homo : CoindHomo) →
  CoindHomo._≤ₐ_ homo Start GoParadise GoTrap → ⊥
coindHomo-reverse-impossible homo prf
  with head≤ (tail≤ (CoindHomo.preserves homo GoParadise GoTrap Start prf))
... | ()
