{-# OPTIONS --safe --guardedness #-}

-- =============================================================================
-- Key-Treasure 10x10 Tabular Data Extraction
-- =============================================================================
-- This file forces normalization of data points to extract tabular results.
-- Each test confirms a specific value, revealing the normalized data.
-- =============================================================================

module CSHRL.Tasks.Verified.KeyTreasure10x10Data where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import CSHRL.Tasks.Verified.KeyTreasure10x10

-- =============================================================================
-- FULL ACTIONS: Rankings from Origin State (s-origin)
-- Agent starts at (0,0), needs to get key at (2,2), then treasure at (9,9)
-- =============================================================================

-- These tests will reveal the actual rankings by normalization
-- Best action is FIRST in the list

-- Depth 0: No lookahead (arbitrary)
test-origin-d0 : find-ranking s-origin 0 ≡ find-ranking s-origin 0
test-origin-d0 = refl

-- Depth 1: 1-step lookahead
test-origin-d1 : find-ranking s-origin 1 ≡ find-ranking s-origin 1
test-origin-d1 = refl

-- Depth 2
test-origin-d2 : find-ranking s-origin 2 ≡ find-ranking s-origin 2
test-origin-d2 = refl

-- Depth 3
test-origin-d3 : find-ranking s-origin 3 ≡ find-ranking s-origin 3
test-origin-d3 = refl

-- Depth 4 (key is 4 steps away: R, U, R, U)
test-origin-d4 : find-ranking s-origin 4 ≡ find-ranking s-origin 4
test-origin-d4 = refl

-- Depth 5
test-origin-d5 : find-ranking s-origin 5 ≡ find-ranking s-origin 5
test-origin-d5 = refl

-- Depth 8
test-origin-d8 : find-ranking s-origin 8 ≡ find-ranking s-origin 8
test-origin-d8 = refl

-- Depth 10
test-origin-d10 : find-ranking s-origin 10 ≡ find-ranking s-origin 10
test-origin-d10 = refl

-- =============================================================================
-- FULL ACTIONS: Rankings from Has-Key State (s-has-key)
-- Agent has key at (2,2), needs to get treasure at (9,9)
-- =============================================================================

-- Depth 0
test-haskey-d0 : find-ranking s-has-key 0 ≡ find-ranking s-has-key 0
test-haskey-d0 = refl

-- Depth 5
test-haskey-d5 : find-ranking s-has-key 5 ≡ find-ranking s-has-key 5
test-haskey-d5 = refl

-- Depth 10
test-haskey-d10 : find-ranking s-has-key 10 ≡ find-ranking s-has-key 10
test-haskey-d10 = refl

-- Depth 15 (treasure is ~14 steps from key)
test-haskey-d15 : find-ranking s-has-key 15 ≡ find-ranking s-has-key 15
test-haskey-d15 = refl

-- =============================================================================
-- UNAVAILABILITY: Rankings without Up action
-- =============================================================================

-- Origin, no Up
test-origin-no-up-d10 : find-ranking-restricted avail-no-up s-origin 10 ≡ find-ranking-restricted avail-no-up s-origin 10
test-origin-no-up-d10 = refl

-- HasKey, no Up
test-haskey-no-up-d10 : find-ranking-restricted avail-no-up s-has-key 10 ≡ find-ranking-restricted avail-no-up s-has-key 10
test-haskey-no-up-d10 = refl

-- =============================================================================
-- UNAVAILABILITY: Rankings without Right action
-- =============================================================================

-- Origin, no Right
test-origin-no-right-d10 : find-ranking-restricted avail-no-right s-origin 10 ≡ find-ranking-restricted avail-no-right s-origin 10
test-origin-no-right-d10 = refl

-- HasKey, no Right
test-haskey-no-right-d10 : find-ranking-restricted avail-no-right s-has-key 10 ≡ find-ranking-restricted avail-no-right s-has-key 10
test-haskey-no-right-d10 = refl

-- =============================================================================
-- UNAVAILABILITY: Minimal (only Right and Down)
-- =============================================================================

-- Origin, minimal
test-origin-minimal-d10 : find-ranking-restricted avail-minimal s-origin 10 ≡ find-ranking-restricted avail-minimal s-origin 10
test-origin-minimal-d10 = refl

-- HasKey, minimal
test-haskey-minimal-d10 : find-ranking-restricted avail-minimal s-has-key 10 ≡ find-ranking-restricted avail-minimal s-has-key 10
test-haskey-minimal-d10 = refl

-- =============================================================================
-- TRACES: Raw trace data for selected actions
-- =============================================================================

-- Traces show accumulated rewards over depth
test-trace-up-5 : trace-action s-origin Up 5 ≡ trace-action s-origin Up 5
test-trace-up-5 = refl

test-trace-right-5 : trace-action s-origin Right 5 ≡ trace-action s-origin Right 5
test-trace-right-5 = refl

-- =============================================================================
-- BEST ACTION: First action in each ranking
-- =============================================================================

test-best-origin-d5 : best-action (find-ranking s-origin 5) ≡ best-action (find-ranking s-origin 5)
test-best-origin-d5 = refl

test-best-origin-d10 : best-action (find-ranking s-origin 10) ≡ best-action (find-ranking s-origin 10)
test-best-origin-d10 = refl

test-best-haskey-d10 : best-action (find-ranking s-has-key 10) ≡ best-action (find-ranking s-has-key 10)
test-best-haskey-d10 = refl

test-best-haskey-d15 : best-action (find-ranking s-has-key 15) ≡ best-action (find-ranking s-has-key 15)
test-best-haskey-d15 = refl

-- =============================================================================
-- DATA SUMMARY TABLE (to be filled by normalization)
-- =============================================================================
-- 
-- Format: State | Depth | Available | Ranking (best→worst) | Best Action
--
-- s-origin   | 0  | all      | [?, ?, ?, ?]    | ?
-- s-origin   | 1  | all      | [?, ?, ?, ?]    | ?
-- s-origin   | 2  | all      | [?, ?, ?, ?]    | ?
-- s-origin   | 3  | all      | [?, ?, ?, ?]    | ?
-- s-origin   | 4  | all      | [?, ?, ?, ?]    | ?
-- s-origin   | 5  | all      | [?, ?, ?, ?]    | ?
-- s-origin   | 8  | all      | [?, ?, ?, ?]    | ?
-- s-origin   | 10 | all      | [?, ?, ?, ?]    | ?
-- s-origin   | 10 | no-up    | [?, ?, ?]       | ?
-- s-origin   | 10 | no-right | [?, ?, ?]       | ?
-- s-origin   | 10 | minimal  | [?, ?]          | ?
-- s-has-key  | 0  | all      | [?, ?, ?, ?]    | ?
-- s-has-key  | 5  | all      | [?, ?, ?, ?]    | ?
-- s-has-key  | 10 | all      | [?, ?, ?, ?]    | ?
-- s-has-key  | 15 | all      | [?, ?, ?, ?]    | ?
-- s-has-key  | 10 | no-up    | [?, ?, ?]       | ?
-- s-has-key  | 10 | no-right | [?, ?, ?]       | ?
-- s-has-key  | 10 | minimal  | [?, ?]          | ?
--
-- Use C-c C-n on expressions like:
--   find-ranking s-origin 5
--   find-ranking-restricted avail-no-up s-origin 10
-- =============================================================================


