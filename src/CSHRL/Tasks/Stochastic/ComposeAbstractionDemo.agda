{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Stochastic.ComposeAbstractionDemo
--
-- Two-level abstraction: ℕ → Zone → Bool
--
-- Demonstrates compose-abstraction: abstract in two stages, then lift
-- in one.  Concrete state = ℕ.  First level: Zone (Low, Medium, High).
-- Second level: Bool (collapse Low+Medium → false, High → true).
--
-- The composed abstraction ℕ → Bool is equivalent to "is High?", but
-- we obtain it by composing two simpler abstractions.  Marginal is
-- defined so Low and Medium agree (both sparse-like: Invest better),
-- enabling marginal-invariance for the composed projection.
--
-- All --safe, no postulates.
------------------------------------------------------------------------

module CSHRL.Tasks.Stochastic.ComposeAbstractionDemo where

open import Data.Nat using (ℕ; zero; suc; _≤_; _≤?_)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)

open import CSHRL.Probability.Finite using (Dist)
open import CSHRL.Probability.SD using (_SD[_]≤_; SD-refl)
open import CSHRL.Probability.FOSD using (_FOSD≤_; fosd?-sound)
open import CSHRL.Core.Compose using (VerifiedRanking)
open import CSHRL.Core.Abstraction using (StateAbstraction; abstract-lift; compose-abstraction)

------------------------------------------------------------------------
-- Level 1: Zone (3 states)
------------------------------------------------------------------------

data Zone : Set where
  Low    : Zone
  Medium : Zone
  High   : Zone

------------------------------------------------------------------------
-- Level 2: Bool (2 states) — coarse view
------------------------------------------------------------------------

data Action : Set where
  Invest   : Action
  Conserve : Action

------------------------------------------------------------------------
-- First abstraction: ℕ → Zone
------------------------------------------------------------------------

zone : ℕ → Zone
zone n with n ≤? 5
... | yes _ = Low
... | no  _ with n ≤? 10
...   | yes _ = Medium
...   | no  _ = High

ℕ→Zone : StateAbstraction ℕ Zone
ℕ→Zone = record
  { project = zone
  ; embed   = λ { Low → 0 ; Medium → 6 ; High → 11 }
  ; section = λ { Low → refl ; Medium → refl ; High → refl }
  }

------------------------------------------------------------------------
-- Second abstraction: Zone → Bool (collapse Low+Medium)
--
-- Low, Medium → false  (sparse/cold)
-- High → true          (dense/hot)
------------------------------------------------------------------------

zone-to-bool : Zone → Bool
zone-to-bool Low    = false
zone-to-bool Medium = false
zone-to-bool High   = true

bool-to-zone : Bool → Zone
bool-to-zone false = Low
bool-to-zone true  = High

Zone→Bool : StateAbstraction Zone Bool
Zone→Bool = record
  { project = zone-to-bool
  ; embed   = bool-to-zone
  ; section = λ { false → refl ; true → refl }
  }

------------------------------------------------------------------------
-- Composed abstraction: ℕ → Bool
------------------------------------------------------------------------

composed : StateAbstraction ℕ Bool
composed = compose-abstraction ℕ→Zone Zone→Bool

------------------------------------------------------------------------
-- Marginal: Low and Medium must agree (for composed marginal-invariance)
--
-- Both use sparse marginal (Invest better).  High uses dense (Conserve better).
------------------------------------------------------------------------

marginal-by-zone : Zone → Action → ℕ → Dist ℕ
marginal-by-zone Low    Invest   _ = (5 , 1) ∷ (3 , 1) ∷ []
marginal-by-zone Low    Conserve _ = (2 , 1) ∷ (2 , 1) ∷ []
marginal-by-zone Medium Invest   _ = (5 , 1) ∷ (3 , 1) ∷ []
marginal-by-zone Medium Conserve _ = (2 , 1) ∷ (2 , 1) ∷ []
marginal-by-zone High   Invest   _ = (1 , 1) ∷ (0 , 1) ∷ []
marginal-by-zone High   Conserve _ = (4 , 1) ∷ (3 , 1) ∷ []

marginal : ℕ → Action → ℕ → Dist ℕ
marginal n = marginal-by-zone (zone n)

------------------------------------------------------------------------
-- Marginal invariance for composed abstraction
--
-- (zone-to-bool ∘ zone) n₁ ≡ (zone-to-bool ∘ zone) n₂  ⇒  marginal n₁ ≡ marginal n₂
-- Both Low and Medium map to false and have identical marginals.
------------------------------------------------------------------------

low≡medium-marginal : ∀ a t → marginal-by-zone Low a t ≡ marginal-by-zone Medium a t
low≡medium-marginal Invest   t = refl
low≡medium-marginal Conserve t = refl

marginal-invariant : ∀ n₁ n₂ → zone-to-bool (zone n₁) ≡ zone-to-bool (zone n₂) →
  ∀ a t → marginal n₁ a t ≡ marginal n₂ a t
marginal-invariant n₁ n₂ eq a t with zone n₁ | zone n₂ | eq
... | Low    | Low    | _ = refl
... | Low    | Medium | _ = low≡medium-marginal a t
... | Low    | High   | ()
... | Medium | Low    | _ = sym (low≡medium-marginal a t)
... | Medium | Medium | _ = refl
... | Medium | High   | ()
... | High   | Low    | ()
... | High   | Medium | ()
... | High   | High   | _ = refl

------------------------------------------------------------------------
-- Abstract ordering (on Bool — same as Regional Policy)
------------------------------------------------------------------------

order : Bool → Action → Action → Set
order false Invest   Invest   = ⊤
order false Invest   Conserve = ⊥
order false Conserve Invest   = ⊤
order false Conserve Conserve = ⊤
order true  Invest   Invest   = ⊤
order true  Invest   Conserve = ⊤
order true  Conserve Invest   = ⊥
order true  Conserve Conserve = ⊤

------------------------------------------------------------------------
-- FOSD proofs
------------------------------------------------------------------------

private
  sparse-conserve sparse-invest dense-invest dense-conserve : Dist ℕ
  sparse-conserve = (2 , 1) ∷ (2 , 1) ∷ []
  sparse-invest   = (5 , 1) ∷ (3 , 1) ∷ []
  dense-invest    = (1 , 1) ∷ (0 , 1) ∷ []
  dense-conserve  = (4 , 1) ∷ (3 , 1) ∷ []

sparse-invest-dominates : sparse-conserve FOSD≤ sparse-invest
sparse-invest-dominates = fosd?-sound sparse-conserve sparse-invest refl

dense-conserve-dominates : dense-invest FOSD≤ dense-conserve
dense-conserve-dominates = fosd?-sound dense-invest dense-conserve refl

------------------------------------------------------------------------
-- Abstract Verified Ranking (on Bool via composed embed)
------------------------------------------------------------------------

private
  abs-marginal : Bool → Action → ℕ → Dist ℕ
  abs-marginal b = marginal (StateAbstraction.embed composed b)

abstract-ranking : VerifiedRanking Bool Action abs-marginal 0
abstract-ranking = record
  { _≤ₐ_ = order
  ; preserves = preserves-abs
  }
  where
    preserves-abs : ∀ a b s → order s a b →
      ∀ n → abs-marginal s a n SD[ 0 ]≤ abs-marginal s b n
    preserves-abs Invest   Invest   false _ n = SD-refl 0 sparse-invest
    preserves-abs Conserve Invest   false _ n = sparse-invest-dominates
    preserves-abs Conserve Conserve false _ n = SD-refl 0 sparse-conserve
    preserves-abs Invest   Invest   true  _ n = SD-refl 0 dense-invest
    preserves-abs Invest   Conserve true  _ n = dense-conserve-dominates
    preserves-abs Conserve Conserve true  _ n = SD-refl 0 dense-conserve
    preserves-abs Invest   Conserve false () n
    preserves-abs Conserve Invest   true  () n

------------------------------------------------------------------------
-- Lifted ranking via composed abstraction
------------------------------------------------------------------------

infinite-state-ranking : VerifiedRanking ℕ Action marginal 0
infinite-state-ranking =
  abstract-lift composed marginal-invariant abstract-ranking

------------------------------------------------------------------------
-- Spot checks
------------------------------------------------------------------------

open VerifiedRanking infinite-state-ranking

check-low   : _≤ₐ_ 0  Conserve Invest
check-low   = tt

check-medium : _≤ₐ_ 6  Conserve Invest
check-medium = tt

check-high  : _≤ₐ_ 11 Invest Conserve
check-high  = tt
