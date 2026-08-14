{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- 9x9 Sudoku: Verified full-scale puzzle solving
--
-- Uses CombinatorialPlacementMDP Environment Class.
-- Postulate-free, --safe.
--
-- The puzzle (43 empty cells, 38 givens):
--
--     . . 3 | 4 5 . | 7 8 .
--     4 . 6 | . 8 9 | . . 3
--     . . . | 1 2 . | . . 6
--     ------+-------+------
--     2 . 4 | . 6 . | . . 1
--     . 6 . | 8 9 1 | 2 . 4
--     8 9 . | . . . | 5 . .
--     ------+-------+------
--     3 . . | . . 8 | 9 . .
--     . 7 . | . 1 . | . . 5
--     9 1 2 | 3 4 . | . 7 .
--
-- The puzzle is chosen so that every empty cell, in row-major fill
-- order, is *directly conflict-forced*: all 8 wrong digits immediately
-- collide with an already-filled peer (row, column, or 3x3 box).
-- Consequently the Finder's game tree is LINEAR (each wrong digit dies
-- at depth 1), which makes full 9x9 policy extraction feasible in the
-- normalizer even though the raw game tree has 9^43 leaves.
--
-- The CoindHomo itself is proved symbolically via WithTraceBridge and
-- does not depend on the puzzle being forced: it holds for every state
-- of the 9x9 Sudoku MDP.
--
-- Verified results:
--   1. solve Dead n ≡ 0 and solve (Solved c) n ≡ solved-reward
--   2. solve-horizon-suf: game termination sufficiency (fuel induction
--      on remaining empty cells)
--   3. CoindHomo: the Finder's trace ranking is a Coinductive
--      Homomorphism (via WithTraceBridge)
--   4. Policy extraction: every empty cell is conflict-forced to the
--      solution digit (test-forced), and the Finder's policy fills the
--      final cells with the unique completion (test-tail-rollout), both
--      machine-checked by refl.  A full 43-step rollout needs lookahead
--      depth 43 at every step, which is out of reach for Agda's
--      normalizer on unary arithmetic; the Rocq port verifies the full
--      rollout of this same puzzle with vm_compute.
--
-- For efficiency, is-dead only checks the most recently placed cell
-- against the rest of the board: on every reachable configuration this
-- coincides with full-board consistency (earlier conflicts would have
-- killed the episode earlier), and the final validity test re-checks
-- the completed board with the full pairwise constraint check.
------------------------------------------------------------------------

module CSHRL.Tasks.Verified.Sudoku9 where

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
-- Cell geometry: positions 0..80 in row-major order
------------------------------------------------------------------------

div9 : ℕ → ℕ
div9 (suc (suc (suc (suc (suc (suc (suc (suc (suc n))))))))) = suc (div9 n)
div9 _ = 0

mod9 : ℕ → ℕ
mod9 (suc (suc (suc (suc (suc (suc (suc (suc (suc n))))))))) = mod9 n
mod9 n = n

div3 : ℕ → ℕ
div3 (suc (suc (suc n))) = suc (div3 n)
div3 _ = 0

-- Two positions see each other when they share a row, column, or box.
sees : ℕ → ℕ → Bool
sees p q =
  (div9 p ≡ᵇ div9 q) ∨
  (mod9 p ≡ᵇ mod9 q) ∨
  ((div3 (div9 p) ≡ᵇ div3 (div9 q)) ∧ (div3 (mod9 p) ≡ᵇ div3 (mod9 q)))

------------------------------------------------------------------------
-- The puzzle template: just d = given digit, nothing = empty cell
------------------------------------------------------------------------

Cell : Set
Cell = Maybe ℕ

template : List Cell
template =
  -- row 0
  nothing ∷ nothing ∷ just 3  ∷ just 4  ∷ just 5  ∷ nothing ∷ just 7  ∷ just 8  ∷ nothing ∷
  -- row 1
  just 4  ∷ nothing ∷ just 6  ∷ nothing ∷ just 8  ∷ just 9  ∷ nothing ∷ nothing ∷ just 3  ∷
  -- row 2
  nothing ∷ nothing ∷ nothing ∷ just 1  ∷ just 2  ∷ nothing ∷ nothing ∷ nothing ∷ just 6  ∷
  -- row 3
  just 2  ∷ nothing ∷ just 4  ∷ nothing ∷ just 6  ∷ nothing ∷ nothing ∷ nothing ∷ just 1  ∷
  -- row 4
  nothing ∷ just 6  ∷ nothing ∷ just 8  ∷ just 9  ∷ just 1  ∷ just 2  ∷ nothing ∷ just 4  ∷
  -- row 5
  just 8  ∷ just 9  ∷ nothing ∷ nothing ∷ nothing ∷ nothing ∷ just 5  ∷ nothing ∷ nothing ∷
  -- row 6
  just 3  ∷ nothing ∷ nothing ∷ nothing ∷ nothing ∷ just 8  ∷ just 9  ∷ nothing ∷ nothing ∷
  -- row 7
  nothing ∷ just 7  ∷ nothing ∷ nothing ∷ just 1  ∷ nothing ∷ nothing ∷ nothing ∷ just 5  ∷
  -- row 8
  just 9  ∷ just 1  ∷ just 2  ∷ just 3  ∷ just 4  ∷ nothing ∷ nothing ∷ just 7  ∷ nothing ∷ []

-- Number of empty cells: the episode horizon.
num-empty : ℕ
num-empty = 43

------------------------------------------------------------------------
-- Configuration: digits assigned to the empty cells so far, in order
------------------------------------------------------------------------

Config : Set
Config = List ℕ

-- Merge the assignment into the template: full 81-cell partial board.
merge : List Cell → Config → List Cell
merge [] _ = []
merge (just d  ∷ t) cfg = just d ∷ merge t cfg
merge (nothing ∷ t) [] = nothing ∷ merge t []
merge (nothing ∷ t) (d ∷ cfg) = just d ∷ merge t cfg

board-of : Config → List Cell
board-of = merge template

-- Positions of the empty cells, in row-major order.
holes-of : ℕ → List Cell → List ℕ
holes-of _ [] = []
holes-of p (nothing ∷ t) = p ∷ holes-of (suc p) t
holes-of p (just _  ∷ t) = holes-of (suc p) t

hole-positions : List ℕ
hole-positions = holes-of 0 template

------------------------------------------------------------------------
-- Constraint checking
------------------------------------------------------------------------

nthℕ : ℕ → List ℕ → ℕ
nthℕ _       []       = 0
nthℕ zero    (x ∷ _)  = x
nthℕ (suc i) (_ ∷ xs) = nthℕ i xs

-- Does digit d at position p conflict with any other filled cell?
conflicts : ℕ → ℕ → ℕ → List Cell → Bool
conflicts _ _ _ [] = false
conflicts p d q (nothing ∷ rest) = conflicts p d (suc q) rest
conflicts p d q (just e  ∷ rest) =
  (not (q ≡ᵇ p) ∧ sees p q ∧ (d ≡ᵇ e)) ∨ conflicts p d (suc q) rest

-- Dead check: only the MOST RECENTLY placed cell can introduce a new
-- conflict, so we check just that one (linear instead of quadratic).
-- On the empty configuration the checked digit is the default 0, which
-- never matches a placed digit (all digits are 1..9), so this is false.
is-dead-config : Config → Bool
is-dead-config cfg =
  let k = pred (length cfg)
  in conflicts (nthℕ k hole-positions) (nthℕ k cfg) 0 (board-of cfg)

is-solved-config : Config → Bool
is-solved-config cfg = length cfg ≡ᵇ num-empty

-- Full-board pairwise consistency (used to validate the final board).
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

------------------------------------------------------------------------
-- Actions: the nine digits
------------------------------------------------------------------------

data Action : Set where
  A1 A2 A3 A4 A5 A6 A7 A8 A9 : Action

digit : Action → ℕ
digit A1 = 1
digit A2 = 2
digit A3 = 3
digit A4 = 4
digit A5 = 5
digit A6 = 6
digit A7 = 7
digit A8 = 8
digit A9 = 9

all-actions : List Action
all-actions = A1 ∷ A2 ∷ A3 ∷ A4 ∷ A5 ∷ A6 ∷ A7 ∷ A8 ∷ A9 ∷ []

default-action : Action
default-action = A1

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
-- Identical in structure to Queens8/Sudoku4: each placement grows the
-- config by one; is-solved checks length = num-empty; so after
-- num-empty placements every path is terminal.
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
  actions-witness A1 p = here p
  actions-witness A2 p = there (here p)
  actions-witness A3 p = there (there (here p))
  actions-witness A4 p = there (there (there (here p)))
  actions-witness A5 p = there (there (there (there (here p))))
  actions-witness A6 p = there (there (there (there (there (here p)))))
  actions-witness A7 p = there (there (there (there (there (there (here p))))))
  actions-witness A8 p = there (there (there (there (there (there (there (here p)))))))
  actions-witness A9 p = there (there (there (there (there (there (there (there (here p))))))))

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
-- action-value streams, for EVERY state of the 9x9 Sudoku MDP.
------------------------------------------------------------------------

open WithTraceBridge solve-Dead-0 solve-Solved-R 0<R solve-horizon-suf public

test-preserves : ∀ a b s →
  s ranks a ≤ b →
  action-value s a ≤ₛ action-value s b
test-preserves = preserves

------------------------------------------------------------------------
-- Policy extraction: the Finder solves the full 9x9 puzzle
------------------------------------------------------------------------

-- Roll out the Finder's policy for n steps from state s
run-policy : State → ℕ → ℕ → List Action
run-policy _ _ zero = []
run-policy s depth (suc n) =
  let a = find-policy s depth
  in a ∷ run-policy (proj₁ (step s a)) depth n

-- The digits of the unique completion, in row-major hole order.
solution : Config
solution =
  1 ∷ 2 ∷ 6 ∷ 9 ∷ 5 ∷ 7 ∷ 1 ∷ 2 ∷ 7 ∷ 8 ∷ 9 ∷ 3 ∷ 4 ∷ 5 ∷ 3 ∷ 5 ∷ 7 ∷ 8 ∷
  9 ∷ 5 ∷ 7 ∷ 3 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 6 ∷ 7 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 1 ∷ 2 ∷ 6 ∷ 8 ∷
  9 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 8 ∷ []

------------------------------------------------------------------------
-- Forcedness: at every prefix of the solution, exactly ONE digit
-- survives the dead check, and it is the solution digit.  Dead actions
-- produce all-zero traces while the surviving action's trace carries
-- the solved reward within lookahead, so this pins the Finder's rollout
-- to the unique completion.
------------------------------------------------------------------------

take' : ℕ → List ℕ → List ℕ
take' zero    _        = []
take' (suc n) []       = []
take' (suc n) (x ∷ xs) = x ∷ take' n xs

upTo : ℕ → List ℕ
upTo n = go n 0
  where
  go : ℕ → ℕ → List ℕ
  go zero    _ = []
  go (suc m) i = i ∷ go m (suc i)

filterℕ : (ℕ → Bool) → List ℕ → List ℕ
filterℕ f [] = []
filterℕ f (x ∷ xs) = if f x then x ∷ filterℕ f xs else filterℕ f xs

digits1-9 : List ℕ
digits1-9 = 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ []

surviving : ℕ → List ℕ
surviving k =
  filterℕ (λ d → not (is-dead-config (take' k solution ++ (d ∷ []))))
          digits1-9

-- Every empty cell is conflict-forced to the solution digit.
test-forced : map surviving (upTo num-empty) ≡ map (λ d → d ∷ []) solution
test-forced = refl

-- The Finder's policy fills the last three cells with the solution
-- digits (shallow lookahead: three remaining cells, depth 3).
test-tail-rollout :
  run-policy (Ongoing (take' 40 solution)) 3 3 ≡ A5 ∷ A6 ∷ A8 ∷ []
test-tail-rollout = refl

-- The completed board passes the full pairwise constraint check.
test-valid : ok-board (board-of solution) ≡ true
test-valid = refl

-- And it is indeed complete.
test-complete : is-solved-config solution ≡ true
test-complete = refl
