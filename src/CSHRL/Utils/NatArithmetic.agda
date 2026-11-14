{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- CSHRL.Utils.NatArithmetic
--
-- Canonical definitions for div, mod, and range used across the
-- codebase. Delegates to stdlib _/_ and _%_ (GMP-accelerated).
-- Single source of truth — no duplication.
------------------------------------------------------------------------

module CSHRL.Utils.NatArithmetic where

open import Data.Nat  using (ℕ; zero; suc; _/_; _%_)
open import Data.List using (List; []; _∷_)

------------------------------------------------------------------------
-- Integer division and modulo
------------------------------------------------------------------------

divℕ : ℕ → ℕ → ℕ
divℕ _ 0       = 0
divℕ m (suc d) = m / suc d

modℕ : ℕ → ℕ → ℕ
modℕ _ 0       = 0
modℕ m (suc d) = m % suc d

------------------------------------------------------------------------
-- Range enumeration
------------------------------------------------------------------------

range-go : ℕ → ℕ → List ℕ
range-go _ zero    = []
range-go k (suc n) = k ∷ range-go (suc k) n

range : ℕ → List ℕ
range = range-go 0
