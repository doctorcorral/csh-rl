{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- 4x4 Sudoku: Verified constraint-propagation puzzle solving
--
-- Uses CombinatorialPlacementMDP Environment Class.
-- Postulate-free, --safe.
--
-- The puzzle (a uniquely solvable 4x4 Sudoku, 8 givens):
--
--     1 . | . 4          1 2 | 3 4
--     . 4 | 1 .          3 4 | 1 2
--     ----+----   ==>    ----+----
--     2 . | . 3          2 1 | 4 3
--     . 3 | 2 .          4 3 | 2 1
--
-- Model: the agent fills the 8 empty cells in row-major order; the
-- action is the digit (D1..D4) to write.  A placement violating a
-- row/column/box constraint (against givens or earlier placements)
-- kills the episode; completing the grid consistently solves it.
--
-- Verified results:
--   1. solve Dead n ≡ 0 and solve (Solved c) n ≡ solved-reward
--   2. solve-horizon-suf: game termination sufficiency (fuel induction
--      on remaining empty cells)
--   3. CoindHomo: the Finder's trace ranking is a Coinductive
--      Homomorphism (via WithTraceBridge)
--   4. Policy extraction: rolling out find-policy for 8 steps fills
--      the grid with [2,3,3,2,1,4,4,1] — the unique solution — and
--      the completed board passes the constraint check by refl.
------------------------------------------------------------------------

module CSHRL.Tasks.Verified.Sudoku4 where

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; pred; _+_; _∸_; _≡ᵇ_; _≤_; _<_; _⊔_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n; +-comm; m∸n≤m; m∸n≡0⇒m≤n)
open import Data.List using (List; _∷_; []; length; map; _++_; foldr)
open import Data.List.Properties using (length-++)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Codata.Guarded.Stream using (Stream; head; tail; tabulate)
open import Function using (_∘_)

------------------------------------------------------------------------
-- Cell geometry: positions 0..15 in row-major order
------------------------------------------------------------------------

div4 : ℕ → ℕ
div4 (suc (suc (suc (suc n)))) = suc (div4 n)
div4 _ = 0

mod4 : ℕ → ℕ
mod4 (suc (suc (suc (suc n)))) = mod4 n
mod4 n = n

div2 : ℕ → ℕ
div2 (suc (suc n)) = suc (div2 n)
div2 _ = 0

-- Two positions see each other when they share a row, column, or 2x2 box.
sees : ℕ → ℕ → Bool
sees p q =
  (div4 p ≡ᵇ div4 q) ∨
  (mod4 p ≡ᵇ mod4 q) ∨
  ((div2 (div4 p) ≡ᵇ div2 (div4 q)) ∧ (div2 (mod4 p) ≡ᵇ div2 (mod4 q)))

------------------------------------------------------------------------
-- The puzzle template: just d = given digit, nothing = empty cell
------------------------------------------------------------------------

Cell : Set
Cell = Maybe ℕ

template : List Cell
template =
  just 1  ∷ nothing ∷ nothing ∷ just 4  ∷
  nothing ∷ just 4  ∷ just 1  ∷ nothing ∷
  just 2  ∷ nothing ∷ nothing ∷ just 3  ∷
  nothing ∷ just 3  ∷ just 2  ∷ nothing ∷ []

-- Number of empty cells: the episode horizon.
num-empty : ℕ
num-empty = 8

------------------------------------------------------------------------
-- Configuration: digits assigned to the empty cells so far, in order
------------------------------------------------------------------------

Config : Set
Config = List ℕ

-- Merge the assignment into the template: full 16-cell partial board.
merge : List Cell → Config → List Cell
merge [] _ = []
merge (just d  ∷ t) cfg = just d ∷ merge t cfg
merge (nothing ∷ t) [] = nothing ∷ merge t []
merge (nothing ∷ t) (d ∷ cfg) = just d ∷ merge t cfg

board-of : Config → List Cell
board-of = merge template

------------------------------------------------------------------------
-- Constraint checking on a partial board
------------------------------------------------------------------------

-- Does the digit d at position p conflict with any later filled cell?
check-one : ℕ → ℕ → ℕ → List Cell → Bool
check-one _ _ _ [] = true
check-one p d q (nothing ∷ rest) = check-one p d (suc q) rest
check-one p d q (just e ∷ rest) =
  not (sees p q ∧ (d ≡ᵇ e)) ∧ check-one p d (suc q) rest

ok-board : List Cell → Bool
ok-board = go 0
  where
  go : ℕ → List Cell → Bool
  go _ [] = true
  go p (nothing ∷ rest) = go (suc p) rest
  go p (just d ∷ rest) = check-one p d (suc p) rest ∧ go (suc p) rest

is-dead-config : Config → Bool
is-dead-config cfg = not (ok-board (board-of cfg))

is-solved-config : Config → Bool
is-solved-config cfg = length cfg ≡ᵇ num-empty

------------------------------------------------------------------------
-- Actions: the four digits
------------------------------------------------------------------------

data Action : Set where
  D1 D2 D3 D4 : Action

digit : Action → ℕ
digit D1 = 1
digit D2 = 2
digit D3 = 3
digit D4 = 4

all-actions : List Action
all-actions = D1 ∷ D2 ∷ D3 ∷ D4 ∷ []

default-action : Action
default-action = D1

------------------------------------------------------------------------
-- Placement: write the digit into the next empty cell
------------------------------------------------------------------------

place : Config → Action → Config
place cfg a = cfg ++ (digit a ∷ [])

------------------------------------------------------------------------
-- Environment Class
------------------------------------------------------------------------

open import CSHRL.EnvironmentClass.CombinatorialPlacementMDP

solved-reward : ℕ
solved-reward = 100

horizon : ℕ
horizon = num-empty

open CombinatorialPlacementMDP
  Config Action
  is-dead-config is-solved-config
  place
  solved-reward
  all-actions default-action
  horizon

------------------------------------------------------------------------
-- Absorbing State Proofs
------------------------------------------------------------------------

solve-Dead-0 : ∀ n → solve Dead n ≡ 0
solve-Dead-0 zero = refl
solve-Dead-0 (suc n) rewrite solve-Dead-0 n = refl

solve-Solved-R : ∀ c n → solve (Solved c) n ≡ solved-reward
solve-Solved-R c zero = refl
solve-Solved-R c (suc n) rewrite solve-Solved-R c n = refl

open WithAbsorbingLemmas solve-Dead-0 solve-Solved-R public

0<R : 0 < solved-reward
0<R = s≤s z≤n

open WithBinaryStructure solve-Dead-0 solve-Solved-R 0<R

------------------------------------------------------------------------
-- Domain-specific proof: game termination implies solve sufficiency
--
-- Identical in structure to Queens8: each placement grows the config
-- by one; is-solved checks length = num-empty; so after num-empty
-- placements every path is terminal.  Fuel induction on the number of
-- remaining empty cells.
------------------------------------------------------------------------

private
  true≢false : true ≡ false → ⊥
  true≢false ()

  place-length : ∀ c a → length (place c a) ≡ suc (length c)
  place-length c a = trans (length-++ c) (+-comm (length c) 1)

  ∸-suc-pred : ∀ m n → m ∸ suc n ≡ pred (m ∸ n)
  ∸-suc-pred zero    zero    = refl
  ∸-suc-pred zero    (suc _) = refl
  ∸-suc-pred (suc m) zero    = refl
  ∸-suc-pred (suc m) (suc n) = ∸-suc-pred m n

  gt-≡ᵇ-false : ∀ m n → n < m → (m ≡ᵇ n) ≡ false
  gt-≡ᵇ-false (suc _) zero    _         = refl
  gt-≡ᵇ-false (suc m) (suc n) (s≤s n<m) = gt-≡ᵇ-false m n n<m

  not-solved-long : ∀ c a → num-empty ≤ length c →
    is-solved-config (place c a) ≡ false
  not-solved-long c a E≤len =
    subst (λ x → (x ≡ᵇ num-empty) ≡ false) (sym (place-length c a))
          (gt-≡ᵇ-false (suc (length c)) num-empty (s≤s E≤len))

  step-info-long : ∀ c a → num-empty ≤ length c →
    (proj₁ (step (Ongoing c) a) ≡ Dead)
    ⊎ (proj₁ (step (Ongoing c) a) ≡ Ongoing (place c a)
       × num-empty ≤ length (place c a))
  step-info-long c a E≤len with is-dead-config (place c a)
  ... | true  = inj₁ refl
  ... | false with is-solved-config (place c a) in eq
  ...   | true  = ⊥-elim (true≢false (trans (sym eq) (not-solved-long c a E≤len)))
  ...   | false = inj₂ (refl ,
      subst (num-empty ≤_) (sym (place-length c a)) (≤-trans E≤len (n≤1+n (length c))))

-- When all empty cells are used up, solve is always 0.
len≥E⇒solve0 : ∀ c → num-empty ≤ length c → ∀ n → solve (Ongoing c) n ≡ 0
len≥E⇒solve0 c E≤len zero =
  max-list-all-0 (λ a → proj₂ (step (Ongoing c) a)) all-actions
    (λ a → rew-0 a (step-info-long c a E≤len))
  where
    rew-0 : ∀ a →
      (proj₁ (step (Ongoing c) a) ≡ Dead) ⊎
      (proj₁ (step (Ongoing c) a) ≡ Ongoing (place c a) × num-empty ≤ length (place c a)) →
      proj₂ (step (Ongoing c) a) ≡ 0
    rew-0 a _ with is-dead-config (place c a)
    ... | true  = refl
    ... | false with is-solved-config (place c a) in eq
    ...   | true  = ⊥-elim (true≢false (trans (sym eq) (not-solved-long c a E≤len)))
    ...   | false = refl
len≥E⇒solve0 c E≤len (suc n) =
  max-list-all-0
    (λ a → solve (proj₁ (step (Ongoing c) a)) n) all-actions
    (λ a → succ-0 a (step-info-long c a E≤len))
  where
    succ-0 : ∀ a →
      (proj₁ (step (Ongoing c) a) ≡ Dead) ⊎
      (proj₁ (step (Ongoing c) a) ≡ Ongoing (place c a) × num-empty ≤ length (place c a)) →
      solve (proj₁ (step (Ongoing c) a)) n ≡ 0
    succ-0 a (inj₁ eq) = subst (λ s → solve s n ≡ 0) (sym eq) (solve-Dead-0 n)
    succ-0 a (inj₂ (eq , E≤len')) =
      subst (λ s → solve s n ≡ 0) (sym eq) (len≥E⇒solve0 (place c a) E≤len' n)

private
  fuel-succ : ∀ fuel c a → suc fuel ≡ num-empty ∸ length c →
    fuel ≡ num-empty ∸ length (place c a)
  fuel-succ fuel c a eq =
    trans (cong pred eq)
          (trans (sym (∸-suc-pred num-empty (length c)))
                 (sym (cong (num-empty ∸_) (place-length c a))))

  actions-witness : ∀ {f : Action → ℕ} (a : Action) →
    f a ≡ solved-reward → AnyElem (λ x → f x ≡ solved-reward) all-actions
  actions-witness D1 p = here p
  actions-witness D2 p = there (here p)
  actions-witness D3 p = there (there (here p))
  actions-witness D4 p = there (there (there (here p)))

  solve-component-0 : ∀ s m →
    solve s (suc m) ≡ 0 →
    ∀ a → solve (proj₁ (step s a)) m ≡ 0
  solve-component-0 s m p a with solve-binary (proj₁ (step s a)) m
  ... | inj₁ eq0 = eq0
  ... | inj₂ eqR = ⊥-elim (0≢R (trans (sym p)
    (any-R⇒max-R
      (λ a' → solve (proj₁ (step s a')) m)
      all-actions
      (λ a' → solve-binary (proj₁ (step s a')) m)
      (actions-witness a eqR))))

private
  mutual
    shs-induct : ∀ fuel c → fuel ≡ num-empty ∸ length c →
         solve (Ongoing c) fuel ≡ 0 → ∀ n → solve (Ongoing c) n ≡ 0
    shs-induct zero c feq q n = len≥E⇒solve0 c (m∸n≡0⇒m≤n (sym feq)) n
    shs-induct (suc fuel') c feq q = all-n
      where
      all-n : ∀ n → solve (Ongoing c) n ≡ 0
      all-n zero = solve-0-backward* (Ongoing c) (suc fuel') zero z≤n q
      all-n (suc n') =
        max-list-all-0
          (λ a → solve (proj₁ (step (Ongoing c) a)) n')
          all-actions
          (λ a → shs-succ c fuel' feq a
                   (solve-component-0 (Ongoing c) fuel' q a) n')

    shs-succ : ∀ c fuel' →
      (feq : suc fuel' ≡ num-empty ∸ length c) →
      (a : Action) →
      (comp0-a : solve (proj₁ (step (Ongoing c) a)) fuel' ≡ 0) →
      ∀ n' → solve (proj₁ (step (Ongoing c) a)) n' ≡ 0
    shs-succ c fuel' feq a comp0-a n'
      with is-dead-config (place c a)
    ... | true  = solve-Dead-0 n'
    ... | false with is-solved-config (place c a)
    ...   | true  =
            ⊥-elim (0≢R (trans (sym comp0-a) (solve-Solved-R (place c a) fuel')))
    ...   | false =
            shs-induct fuel' (place c a) (fuel-succ fuel' c a feq) comp0-a n'

solve-horizon-suf : ∀ c → solve (Ongoing c) horizon ≡ 0 →
                    ∀ n → solve (Ongoing c) n ≡ 0
solve-horizon-suf c p n =
  shs-induct (num-empty ∸ length c) c refl
     (solve-0-backward* (Ongoing c) horizon (num-empty ∸ length c)
                        (m∸n≤m num-empty (length c)) p)
     n

------------------------------------------------------------------------
-- The verified CoindHomo: the Finder's ranking preserves the full
-- action-value streams.
------------------------------------------------------------------------

open WithTraceBridge solve-Dead-0 solve-Solved-R 0<R solve-horizon-suf public

test-preserves : ∀ a b s →
  s ranks a ≤ b →
  action-value s a ≤ₛ action-value s b
test-preserves = preserves

------------------------------------------------------------------------
-- Policy extraction: the Finder solves the puzzle
------------------------------------------------------------------------

-- The first move: the unique digit for the first empty cell (row 0,
-- col 1) is 2.
test-first-move : find-policy (Ongoing []) horizon ≡ D2
test-first-move = refl

-- Roll out the Finder's policy for n steps from state s
run-policy : State → ℕ → ℕ → List Action
run-policy _ _ zero = []
run-policy s depth (suc n) =
  let a = find-policy s depth
  in a ∷ run-policy (proj₁ (step s a)) depth n

-- The Finder fills all 8 empty cells with the unique solution.
test-solution : run-policy (Ongoing []) horizon num-empty
              ≡ D2 ∷ D3 ∷ D3 ∷ D2 ∷ D1 ∷ D4 ∷ D4 ∷ D1 ∷ []
test-solution = refl

-- The completed board satisfies every row/column/box constraint.
test-valid : ok-board (board-of (2 ∷ 3 ∷ 3 ∷ 2 ∷ 1 ∷ 4 ∷ 4 ∷ 1 ∷ [])) ≡ true
test-valid = refl

-- And it is indeed complete.
test-complete : is-solved-config (2 ∷ 3 ∷ 3 ∷ 2 ∷ 1 ∷ 4 ∷ 4 ∷ 1 ∷ []) ≡ true
test-complete = refl
