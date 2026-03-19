{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Stochastic.ThreeZoneDemo
--
-- A convenient abstraction demo: 3-zone classification.
--
-- Extends the Regional Policy idea to three abstract states (Low,
-- Medium, High), showing the framework scales beyond binary abstraction.
-- State = ℕ (unbounded), abstracted to Zone = Low | Medium | High.
--
-- Policy by zone:
--   Low:    Invest  > Conserve  (growth opportunity)
--   Medium: Balanced (both similar)
--   High:   Conserve > Invest    (saturation)
--
-- The demo verifies the ranking on 3 abstract states, then lifts to
-- all of ℕ.  Minimal formalization, maximal clarity.
--
-- All --safe, no postulates.
------------------------------------------------------------------------

module CSHRL.Tasks.Stochastic.ThreeZoneDemo where

open import Data.Nat using (ℕ; zero; suc; _≤_; _≤?_)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import CSHRL.Probability.Finite using (Dist)
open import CSHRL.Probability.SD using (_SD[_]≤_; SD-refl)
open import CSHRL.Probability.FOSD using (_FOSD≤_; fosd?-sound)
open import CSHRL.Core.Compose using (VerifiedRanking)
open import CSHRL.Core.Abstraction using (StateAbstraction; abstract-lift)

------------------------------------------------------------------------
-- Zone: 3 abstract states
------------------------------------------------------------------------

data Zone : Set where
  Low    : Zone
  Medium : Zone
  High   : Zone

------------------------------------------------------------------------
-- Actions
------------------------------------------------------------------------

data Action : Set where
  Invest   : Action
  Conserve : Action

------------------------------------------------------------------------
-- Zone classification
--
-- Low:    n ≤ 5
-- Medium: 6 ≤ n ≤ 10
-- High:   n > 10
------------------------------------------------------------------------

zone : ℕ → Zone
zone n with n ≤? 5
... | yes _ = Low
... | no  _ with n ≤? 10
...   | yes _ = Medium
...   | no  _ = High

------------------------------------------------------------------------
-- Marginal rewards by zone
--
-- Low:    Invest dominates (5,3 vs 2,2)
-- Medium: Both similar (3,2 vs 3,2) — tie
-- High:   Conserve dominates (4,3 vs 1,0)
------------------------------------------------------------------------

marginal-by-zone : Zone → Action → ℕ → Dist ℕ
marginal-by-zone Low    Invest   _ = (5 , 1) ∷ (3 , 1) ∷ []
marginal-by-zone Low    Conserve _ = (2 , 1) ∷ (2 , 1) ∷ []
marginal-by-zone Medium Invest   _ = (3 , 1) ∷ (2 , 1) ∷ []
marginal-by-zone Medium Conserve _ = (3 , 1) ∷ (2 , 1) ∷ []
marginal-by-zone High   Invest   _ = (1 , 1) ∷ (0 , 1) ∷ []
marginal-by-zone High   Conserve _ = (4 , 1) ∷ (3 , 1) ∷ []

------------------------------------------------------------------------
-- Full marginal
------------------------------------------------------------------------

marginal : ℕ → Action → ℕ → Dist ℕ
marginal n = marginal-by-zone (zone n)

------------------------------------------------------------------------
-- State Abstraction: ℕ → Zone
------------------------------------------------------------------------

zone-abstraction : StateAbstraction ℕ Zone
zone-abstraction = record
  { project = zone
  ; embed   = λ { Low → 0 ; Medium → 6 ; High → 11 }
  ; section = λ { Low → refl ; Medium → refl ; High → refl }
  }

------------------------------------------------------------------------
-- Marginal invariance
------------------------------------------------------------------------

marginal-invariant : ∀ n₁ n₂ → zone n₁ ≡ zone n₂ →
  ∀ a t → marginal n₁ a t ≡ marginal n₂ a t
marginal-invariant n₁ n₂ eq a t = cong (λ z → marginal-by-zone z a t) eq

------------------------------------------------------------------------
-- Abstract ordering
--
-- Low:    Conserve ≤ Invest
-- Medium: both directions (tie)
-- High:   Invest ≤ Conserve
------------------------------------------------------------------------

order : Zone → Action → Action → Set
order Low    Invest   Invest   = ⊤
order Low    Conserve Invest   = ⊤
order Low    Conserve Conserve = ⊤
order Low    Invest   Conserve = ⊥
order Medium Invest   Invest   = ⊤
order Medium Invest   Conserve = ⊤
order Medium Conserve Invest   = ⊤
order Medium Conserve Conserve = ⊤
order High   Invest   Invest   = ⊤
order High   Invest   Conserve = ⊤
order High   Conserve Conserve = ⊤
order High   Conserve Invest   = ⊥

------------------------------------------------------------------------
-- FOSD proofs
------------------------------------------------------------------------

private
  low-conserve low-invest med-invest high-invest high-conserve : Dist ℕ
  low-conserve  = (2 , 1) ∷ (2 , 1) ∷ []
  low-invest    = (5 , 1) ∷ (3 , 1) ∷ []
  med-invest    = (3 , 1) ∷ (2 , 1) ∷ []
  high-invest   = (1 , 1) ∷ (0 , 1) ∷ []
  high-conserve = (4 , 1) ∷ (3 , 1) ∷ []

low-invest-dominates : low-conserve FOSD≤ low-invest
low-invest-dominates = fosd?-sound low-conserve low-invest refl

high-conserve-dominates : high-invest FOSD≤ high-conserve
high-conserve-dominates = fosd?-sound high-invest high-conserve refl

------------------------------------------------------------------------
-- Abstract Verified Ranking (on Zone — 3 states)
------------------------------------------------------------------------

private
  abs-marginal : Zone → Action → ℕ → Dist ℕ
  abs-marginal z = marginal (StateAbstraction.embed zone-abstraction z)

abstract-ranking : VerifiedRanking Zone Action abs-marginal 0
abstract-ranking = record
  { _≤ₐ_ = order
  ; preserves = preserves-abs
  }
  where
    preserves-abs : ∀ a b s → order s a b →
      ∀ n → abs-marginal s a n SD[ 0 ]≤ abs-marginal s b n
    preserves-abs Invest   Invest   Low    _ n = SD-refl 0 low-invest
    preserves-abs Conserve Invest   Low    _ n = low-invest-dominates
    preserves-abs Conserve Conserve Low    _ n = SD-refl 0 low-conserve
    preserves-abs Invest   Invest   Medium _ n = SD-refl 0 med-invest
    preserves-abs Invest   Conserve Medium _ n = SD-refl 0 med-invest
    preserves-abs Conserve Invest   Medium _ n = SD-refl 0 med-invest
    preserves-abs Conserve Conserve Medium _ n = SD-refl 0 med-invest
    preserves-abs Invest   Invest   High   _ n = SD-refl 0 high-invest
    preserves-abs Invest   Conserve High   _ n = high-conserve-dominates
    preserves-abs Conserve Conserve High   _ n = SD-refl 0 high-conserve
    preserves-abs Invest   Conserve Low    () n
    preserves-abs Conserve Invest   High   () n

------------------------------------------------------------------------
-- Lifted ranking on ℕ
------------------------------------------------------------------------

infinite-state-ranking : VerifiedRanking ℕ Action marginal 0
infinite-state-ranking =
  abstract-lift zone-abstraction marginal-invariant abstract-ranking

------------------------------------------------------------------------
-- Spot checks
------------------------------------------------------------------------

open VerifiedRanking infinite-state-ranking

check-low-0   : _≤ₐ_ 0  Conserve Invest
check-low-0   = tt

check-low-5   : _≤ₐ_ 5  Conserve Invest
check-low-5   = tt

check-med-6   : _≤ₐ_ 6  Invest Conserve
check-med-6   = tt

check-med-10  : _≤ₐ_ 10 Invest Conserve
check-med-10  = tt

check-high-11 : _≤ₐ_ 11 Invest Conserve
check-high-11 = tt

check-high-99 : _≤ₐ_ 99 Invest Conserve
check-high-99 = tt
