{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Synthesis.CSHRLLoop
--
-- Generic CSHRL CoindHomo search with adaptive features.
--
-- The loop is parameterized by four environment-interaction functions:
--
--   score-of  : PredProg → ℕ            (evaluate ranking's policy)
--   oracle-of : PredProg → State → Bool  (oracle under ranking's policy)
--   traj-of   : PredProg → List State    (trajectory under ranking's policy)
--   feats-of  : List State → List Feature (derive features from states)
--
-- A ranking R is a CoindHomo iff it is self-consistent:
--   ∀ s ∈ traj-of R.  eval R s ≡ oracle-of R s
--
-- That is, the ranking agrees with its own oracle (computed under its
-- own derived policy) at every representative state in its trajectory.
-- This is exactly the coinductive homomorphism condition.
--
-- The search:
--   1. Derive features from dual-seed trajectories (truep + falsep)
--   2. Enumerate all PredProg candidates at depth d
--   3. Check each candidate for self-consistency (CoindHomo)
--   4. Return the highest-scoring self-consistent candidate
--   5. If none: CEGAR needed → increase depth and retry
------------------------------------------------------------------------

module CSHRL.Synthesis.CSHRLLoop where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Nat  using (ℕ; zero; suc; _≤ᵇ_)
open import Data.List using (List; []; _∷_; map; _++_; concatMap)
open import Data.Product using (_×_; _,_; proj₁)

open import CSHRL.Synthesis.Core

module Loop
  (State   : Set)
  (Feature : Set)
  (eval-feat : Feature → State → Bool)
  where

  module DSL = PredicateDSL State Feature eval-feat

  open DSL public using (PredProg; eval; truep; falsep; feat;
                          _∧p_; _∨p_; ¬p_)

  --------------------------------------------------------------------
  -- Enumeration
  --------------------------------------------------------------------

  private
    atoms-of : List Feature → List PredProg
    atoms-of fs = truep ∷ falsep ∷ map feat fs

    extend : List PredProg → List PredProg
    extend prev =
      let neg = map ¬p_ prev
      in prev
      ++ neg
      ++ concatMap (λ p → map (p ∧p_) prev) prev
      ++ concatMap (λ p → map (p ∨p_) prev) prev
      ++ concatMap (λ p → map (p ∧p_) neg)  prev
      ++ concatMap (λ p → map (p ∨p_) neg)  prev

  enumerate : List Feature → ℕ → List PredProg
  enumerate fs zero    = atoms-of fs
  enumerate fs (suc d) = extend (enumerate fs d)

  --------------------------------------------------------------------
  -- Boolean helpers
  --------------------------------------------------------------------

  private
    beq : Bool → Bool → Bool
    beq true  true  = true
    beq false false = true
    beq _     _     = false

    bfilter : {A : Set} → (A → Bool) → List A → List A
    bfilter _ [] = []
    bfilter f (x ∷ xs) with f x
    ... | true  = x ∷ bfilter f xs
    ... | false = bfilter f xs

  --------------------------------------------------------------------
  -- Result type
  --------------------------------------------------------------------

  data Result : Set where
    converged    : PredProg → Result
    cegar-needed : PredProg → Result

  rank-of : Result → PredProg
  rank-of (converged    r) = r
  rank-of (cegar-needed r) = r

  --------------------------------------------------------------------
  -- The search, parameterized by environment interaction
  --------------------------------------------------------------------

  module Iterate
    (score-of  : PredProg → ℕ)
    (oracle-of : PredProg → State → Bool)
    (traj-of   : PredProg → List State)
    (feats-of  : List State → List Feature)
    where

    best-of : List PredProg → PredProg × ℕ
    best-of []       = (truep , 0)
    best-of (p ∷ []) = (p , score-of p)
    best-of (p ∷ ps) with best-of ps | score-of p
    ... | (q , sq) | sp with sq ≤ᵇ sp
    ...   | true  = (p , sp)
    ...   | false = (q , sq)

    ----------------------------------------------------------------
    -- Self-consistency (CoindHomo check):
    -- does the ranking agree with its own oracle at every rep?
    ----------------------------------------------------------------

    private
      is-coind-homo : PredProg → Bool
      is-coind-homo p =
        let obs = map (λ s → (s , oracle-of p s)) (traj-of p)
        in go obs
        where
          go : List (State × Bool) → Bool
          go []              = true
          go ((s , b) ∷ rest) = beq (eval p s) b ∧ go rest

    ----------------------------------------------------------------
    -- Core: find the best self-consistent ranking among candidates.
    -- Candidates must also have a positive score to exclude trivially
    -- self-consistent but non-performing rankings (e.g. truep when
    -- both actions are equally bad within the oracle's horizon).
    ----------------------------------------------------------------

    private
      viable : PredProg → Bool
      viable p with score-of p
      ... | zero  = false
      ... | suc _ = is-coind-homo p

      solve : List PredProg → Result
      solve cands with bfilter viable cands
      ... | []        = cegar-needed (proj₁ (best-of cands))
      ... | c₁ ∷ rest = converged (proj₁ (best-of (c₁ ∷ rest)))

    ----------------------------------------------------------------
    -- Entry point: derive features from dual seeds, enumerate, solve
    ----------------------------------------------------------------

    run-from : PredProg → ℕ → Result
    run-from seed depth =
      solve (enumerate (feats-of (traj-of truep ++ traj-of falsep
                                  ++ traj-of seed))
                       depth)

    run : ℕ → Result
    run = run-from truep

    ----------------------------------------------------------------
    -- CEGAR wrapper: on failure, increase depth and retry
    ----------------------------------------------------------------

    private
      cegar-iter : ℕ → ℕ → PredProg → Result
      cegar-iter zero        d seed = run-from seed d
      cegar-iter (suc budget) d seed with run-from seed d
      ... | converged    r = converged r
      ... | cegar-needed r = cegar-iter budget (suc d) r

    cegar : ℕ → ℕ → Result
    cegar budget d with run d
    ... | converged    r = converged r
    ... | cegar-needed r = cegar-iter budget (suc d) r
