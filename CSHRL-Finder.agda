{-# OPTIONS --guardedness #-}

module CSHRL-Finder where

open import Data.List using (List; []; _∷_; map; foldr)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Bool using (Bool; true; false; if_then_else_)

module Finder
  (State Action Reward : Set)
  (step                : State → Action → State × Reward)
  (_≤?_                : Reward → Reward → Bool) -- Decidable comparison
  (actions             : Action)                 -- Default action (fallback)
  (all-actions         : List Action)            -- List of all available actions
  where

  -- 1. Ordinal Value
  Trace : Set
  Trace = List Reward

  -- Lexicographic comparison: t1 ≤ₜ t2 means t1 is WORSE or EQUAL to t2
  -- (Standard <=). We want descending sort, so we'll flip it later or use >=.
  _≤ₜ_ : Trace → Trace → Bool
  []       ≤ₜ []       = true
  []       ≤ₜ (_ ∷ _)  = true
  (_ ∷ _)  ≤ₜ []       = false
  (r1 ∷ t1) ≤ₜ (r2 ∷ t2) = 
    if r1 ≤? r2 then
      if r2 ≤? r1 then (t1 ≤ₜ t2) -- r1 == r2
      else true                   -- r1 < r2
    else false                    -- r1 > r2

  -- 2. Evaluation

  mutual
    best-trace : State → ℕ → Trace
    best-trace s zero    = []
    best-trace s (suc k) = 
      let outcomes = map (λ a → trace-action s a k) all-actions
      in max-trace outcomes

    trace-action : State → Action → ℕ → Trace
    trace-action s a k = 
      let (s' , r) = step s a
          future   = best-trace s' k
      in r ∷ future

    max-trace : List Trace → Trace
    max-trace []       = []
    max-trace (t ∷ ts) = max-helper t ts

    max-helper : Trace → List Trace → Trace
    max-helper current [] = current
    max-helper current (t ∷ ts) = 
      if current ≤ₜ t 
      then max-helper t ts 
      else max-helper current ts

  -- 3. The Ranking Finder (Full Permutation)
  -- Returns actions sorted by their trace value (Descending)

  -- Simple Insertion Sort for (Action, Trace) pairs
  insert : (Action × Trace) → List (Action × Trace) → List (Action × Trace)
  insert x [] = x ∷ []
  insert (a1 , t1) ((a2 , t2) ∷ xs) = 
    -- If t1 is better than t2, put a1 first
    if t2 ≤ₜ t1 -- t2 <= t1 means t1 >= t2. 
    then (a1 , t1) ∷ (a2 , t2) ∷ xs
    else (a2 , t2) ∷ insert (a1 , t1) xs

  sort-scored : List (Action × Trace) → List (Action × Trace)
  sort-scored [] = []
  sort-scored (x ∷ xs) = insert x (sort-scored xs)

  find-ranking : State → ℕ → List Action
  find-ranking s k = 
    let scored = map (λ a → (a , trace-action s a k)) all-actions
        sorted = sort-scored scored
    in map proj₁ sorted

  -- 4. The Policy Finder (Single Best Action)
  find-policy : State → ℕ → Action
  find-policy s k = 
    let ranking = find-ranking s k
    in head-default ranking
    where
      head-default : List Action → Action
      head-default []      = actions
      head-default (x ∷ _) = x
