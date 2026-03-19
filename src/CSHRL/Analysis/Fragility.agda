{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- CSHRL.Analysis.Fragility
--
-- General-purpose fragility analysis for finite MDPs.
--
-- Fragility = minimax distance to the terminal set.
-- Computed by Bellman-style fixed-point iteration on a finite
-- state table.  Converges in at most |S| iterations.
--
-- Parameterized by:
--   S, A        — state and action types
--   _≟_         — decidable equality on S
--   next        — transition function
--   terminal?   — terminal predicate
--   all-states  — enumeration of all states
--   all-actions — enumeration of all actions
--
-- Provides:
--   fragility   : S → ℕ
--   frag-reward : S → A → ℕ  (= fragility ∘ next)
------------------------------------------------------------------------

module CSHRL.Analysis.Fragility where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _⊓_)
open import Data.List using (List; []; _∷_; map; length; foldr)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (Dec; yes; no)

module ComputeFragility
  (S : Set)
  (_≟_ : (s₁ s₂ : S) → Dec (s₁ ≡ s₂))
  (A : Set)
  (next : S → A → S)
  (terminal? : S → Bool)
  (all-states : List S)
  (all-actions : List A)
  where

  private
    Table : Set
    Table = List ℕ

    lookup : List S → Table → S → ℕ
    lookup [] _ _ = 0
    lookup (_ ∷ _) [] _ = 0
    lookup (s' ∷ ss) (v ∷ vs) s with s ≟ s'
    ... | yes _ = v
    ... | no  _ = lookup ss vs s

    min-actions : Table → S → ℕ
    min-actions tbl s =
      foldr _⊓_ (length all-states)
        (map (λ a → lookup all-states tbl (next s a)) all-actions)

    frag-one : Table → S → ℕ
    frag-one tbl s with terminal? s
    ... | true  = 0
    ... | false = suc (min-actions tbl s)

    step : Table → Table
    step tbl = map (frag-one tbl) all-states

    iterate : ℕ → Table → Table
    iterate zero    tbl = tbl
    iterate (suc k) tbl = iterate k (step tbl)

    init : Table
    init = map (λ _ → 0) all-states

    frag-table : Table
    frag-table = iterate (length all-states) init

  fragility : S → ℕ
  fragility s = lookup all-states frag-table s

  frag-reward : S → A → ℕ
  frag-reward s a = fragility (next s a)
