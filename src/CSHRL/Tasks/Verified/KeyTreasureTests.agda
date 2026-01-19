{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- KeyTreasureTests: Machine-verified test assertions for KeyTreasure10x10
--
-- Each test compiles only if the asserted ranking equals the computed one.
-- This provides concrete evidence of:
--   1. Ranking evolution with depth (flip at depth 3)
--   2. Convergence (stable ranking at depth 3+)
--   3. Unavailability adaptation (correct restricted rankings)
------------------------------------------------------------------------

module CSHRL.Tasks.Verified.KeyTreasureTests where

open import CSHRL.Tasks.Verified.KeyTreasure10x10
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- =============================================================================
-- ORIGIN STATE (0,0) - need key at (2,2), then treasure at (9,9)
-- Optimal direction: Right or Up toward key
-- =============================================================================

-- Depth 0-2: Arbitrary ranking (no reward signal yet)
test-origin-d0 : find-ranking s-origin 0 ≡ Up ∷ Down ∷ Left ∷ Right ∷ []
test-origin-d0 = refl

test-origin-d1 : find-ranking s-origin 1 ≡ Up ∷ Down ∷ Left ∷ Right ∷ []
test-origin-d1 = refl

test-origin-d2 : find-ranking s-origin 2 ≡ Up ∷ Down ∷ Left ∷ Right ∷ []
test-origin-d2 = refl

-- Depth 3: THE FLIP - Right moves up as key reward becomes visible
test-origin-d3 : find-ranking s-origin 3 ≡ Up ∷ Right ∷ Down ∷ Left ∷ []
test-origin-d3 = refl

-- Depth 4+: Stable ranking (key reachable in 4 steps)
test-origin-d4 : find-ranking s-origin 4 ≡ Up ∷ Right ∷ Down ∷ Left ∷ []
test-origin-d4 = refl

test-origin-d5 : find-ranking s-origin 5 ≡ Up ∷ Right ∷ Down ∷ Left ∷ []
test-origin-d5 = refl

test-origin-d8 : find-ranking s-origin 8 ≡ Up ∷ Right ∷ Down ∷ Left ∷ []
test-origin-d8 = refl

test-origin-d10 : find-ranking s-origin 10 ≡ Up ∷ Right ∷ Down ∷ Left ∷ []
test-origin-d10 = refl

-- =============================================================================
-- HAS-KEY STATE (2,2) with key - need treasure at (9,9)
-- Optimal direction: Right and Up toward treasure
-- =============================================================================

test-haskey-d0 : find-ranking s-has-key 0 ≡ Up ∷ Down ∷ Left ∷ Right ∷ []
test-haskey-d0 = refl

test-haskey-d5 : find-ranking s-has-key 5 ≡ Up ∷ Down ∷ Left ∷ Right ∷ []
test-haskey-d5 = refl

test-haskey-d6 : find-ranking s-has-key 6 ≡ Up ∷ Down ∷ Left ∷ Right ∷ []
test-haskey-d6 = refl

-- =============================================================================
-- UNAVAILABILITY TESTS - Origin State Depth 5
-- Demonstrates O(1) adaptation when actions become unavailable
-- =============================================================================

-- Up unavailable: Down becomes best
test-origin-no-up : find-ranking-restricted avail-no-up s-origin 5 ≡ Down ∷ Left ∷ Right ∷ []
test-origin-no-up = refl

-- Right unavailable: ranking preserves relative order
test-origin-no-right : find-ranking-restricted avail-no-right s-origin 5 ≡ Up ∷ Down ∷ Left ∷ []
test-origin-no-right = refl

-- Minimal (only Right and Down available)
test-origin-minimal : find-ranking-restricted avail-minimal s-origin 5 ≡ Down ∷ Right ∷ []
test-origin-minimal = refl

-- =============================================================================
-- UNAVAILABILITY TESTS - HasKey State Depth 5
-- =============================================================================

test-haskey-no-up : find-ranking-restricted avail-no-up s-has-key 5 ≡ Down ∷ Left ∷ Right ∷ []
test-haskey-no-up = refl

test-haskey-no-right : find-ranking-restricted avail-no-right s-has-key 5 ≡ Up ∷ Down ∷ Left ∷ []
test-haskey-no-right = refl

test-haskey-minimal : find-ranking-restricted avail-minimal s-has-key 5 ≡ Down ∷ Right ∷ []
test-haskey-minimal = refl
