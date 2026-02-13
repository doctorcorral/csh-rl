{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- 8-Queens: Verified N-Queens for N = 8
--
-- Uses CombinatorialPlacementMDP Environment Class.
-- Postulate-free, --safe.
--
-- Verified results:
--   1. solve Dead n ≡ 0 (Dead is absorbing with zero reward)
--   2. solve (Solved c) n ≡ solved-reward (Solved is absorbing with R)
--   3. find-policy (Ongoing []) N ≡ C0 (Finder computes optimal policy)
--   4. solve-horizon-suf: if solve (Ongoing c) horizon ≡ 0 then
--      solve (Ongoing c) n ≡ 0 for ALL n (game termination sufficiency)
--   5. CoindHomo: the Finder's trace ranking _ranks_≤_ forms a
--      Coinductive Homomorphism (via WithTraceBridge)
--   6. Full policy extraction: rolling out find-policy for 8 steps
--      yields solution [C0,C4,C7,C5,C2,C6,C1,C3] = [0,4,7,5,2,6,1,3],
--      one of the 92 solutions, verified as all-safe by refl.
--
-- The absorbing-state short-circuit in CombinatorialPlacementMDP
-- makes find-policy feasible in the normalizer (~4 seconds).
------------------------------------------------------------------------

module CSHRL.Tasks.Verified.Queens8 where

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_; not; T)
open import Data.Bool.Properties using (T?)
open import Data.Nat using (ℕ; zero; suc; pred; _+_; _∸_; _≡ᵇ_; _≤_; _<_; _⊔_; z≤n; s≤s; _≤′_; ≤′-refl; ≤′-step)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n; +-comm; ≤⇒≤′; m∸n≤m; m∸n≡0⇒m≤n)
open import Data.List using (List; _∷_; []; length; map; _++_; foldr)
open import Data.List.Properties using (length-++)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Codata.Guarded.Stream using (Stream; head; tail; tabulate)
open import Function using (_∘_)

------------------------------------------------------------------------
-- Configuration: 8-Queens on 8×8 board
------------------------------------------------------------------------

N : ℕ
N = 8

Config : Set
Config = List ℕ

------------------------------------------------------------------------
-- Actions: 8 columns
------------------------------------------------------------------------

data Action : Set where
  C0 C1 C2 C3 C4 C5 C6 C7 : Action

action-to-ℕ : Action → ℕ
action-to-ℕ C0 = 0
action-to-ℕ C1 = 1
action-to-ℕ C2 = 2
action-to-ℕ C3 = 3
action-to-ℕ C4 = 4
action-to-ℕ C5 = 5
action-to-ℕ C6 = 6
action-to-ℕ C7 = 7

all-actions : List Action
all-actions = C0 ∷ C1 ∷ C2 ∷ C3 ∷ C4 ∷ C5 ∷ C6 ∷ C7 ∷ []

default-action : Action
default-action = C0

------------------------------------------------------------------------
-- Placement
------------------------------------------------------------------------

place : Config → Action → Config
place xs a = xs ++ (action-to-ℕ a ∷ [])

------------------------------------------------------------------------
-- Constraint Checking
------------------------------------------------------------------------

abs-diff : ℕ → ℕ → ℕ
abs-diff x y = (x ∸ y) + (y ∸ x)

-- Check if all queens are mutually non-attacking
all-safe : Config → Bool
all-safe = go 0
  where
    -- Does queen at (r1, c1) attack any queen in the remaining list?
    check-one : ℕ → ℕ → ℕ → Config → Bool
    check-one _ _ _ [] = true
    check-one r1 c1 r2 (c2 ∷ rest) =
      not ((c1 ≡ᵇ c2) ∨ (abs-diff r1 r2 ≡ᵇ abs-diff c1 c2))
      ∧ check-one r1 c1 (suc r2) rest

    go : ℕ → Config → Bool
    go _ [] = true
    go row (c ∷ rest) = check-one row c (suc row) rest ∧ go (suc row) rest

is-dead-config : Config → Bool
is-dead-config xs = not (all-safe xs)

is-solved-config : Config → Bool
is-solved-config xs = length xs ≡ᵇ N

------------------------------------------------------------------------
-- Environment Class
------------------------------------------------------------------------

open import CSHRL.EnvironmentClass.CombinatorialPlacementMDP

solved-reward : ℕ
solved-reward = 100

horizon : ℕ
horizon = N

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

------------------------------------------------------------------------
-- Absorbing Lemmas (Dead ≤ₛ any, etc.)
------------------------------------------------------------------------

open WithAbsorbingLemmas solve-Dead-0 solve-Solved-R public

------------------------------------------------------------------------
-- Finder: verified policy computation
--
-- The Finder explores the full 8-Queens game tree and computes
-- the optimal first column. The absorbing-state short-circuit
-- makes this feasible (~4 seconds in the normalizer).
------------------------------------------------------------------------

test-queens : find-policy (Ongoing []) N ≡ C0
test-queens = refl

------------------------------------------------------------------------
-- Trace Bridge: verified CoindHomo
--
-- The Finder's trace-based ranking forms a genuine Coinductive
-- Homomorphism, proving that the Finder preserves value ordering.
------------------------------------------------------------------------

-- Domain property: 0 < solved-reward
0<R : 0 < solved-reward
0<R = s≤s z≤n

-- Open WithBinaryStructure for solve-binary, solve-mono, etc.
-- (These don't depend on solve-horizon-suf, avoiding circularity.)
open WithBinaryStructure solve-Dead-0 solve-Solved-R 0<R

------------------------------------------------------------------------
-- Domain-specific proof: game termination implies solve sufficiency
--
-- The 8-Queens game terminates within N moves because placing a queen
-- always increases config length by 1, and is-solved checks length = N.
-- After N steps from any Ongoing config, all paths are terminal.
------------------------------------------------------------------------

private
  true≢false : true ≡ false → ⊥
  true≢false ()

  -- place always increases config length by 1
  place-length : ∀ c a → length (place c a) ≡ suc (length c)
  place-length c a = trans (length-++ c) (+-comm (length c) 1)

  -- Arithmetic helper: m ∸ suc n ≡ pred (m ∸ n)
  ∸-suc-pred : ∀ m n → m ∸ suc n ≡ pred (m ∸ n)
  ∸-suc-pred zero    zero    = refl
  ∸-suc-pred zero    (suc _) = refl
  ∸-suc-pred (suc m) zero    = refl
  ∸-suc-pred (suc m) (suc n) = ∸-suc-pred m n

  -- m ≡ᵇ n is false when n < m
  gt-≡ᵇ-false : ∀ m n → n < m → (m ≡ᵇ n) ≡ false
  gt-≡ᵇ-false (suc _) zero    _         = refl
  gt-≡ᵇ-false (suc m) (suc n) (s≤s n<m) = gt-≡ᵇ-false m n n<m

  -- When config length ≥ N, is-solved is false for any placement
  not-solved-long : ∀ c a → N ≤ length c →
    is-solved-config (place c a) ≡ false
  not-solved-long c a N≤len =
    subst (λ x → (x ≡ᵇ N) ≡ false) (sym (place-length c a))
          (gt-≡ᵇ-false (suc (length c)) N (s≤s N≤len))

  -- Successor state info: for any Ongoing c, step gives Dead/Solved/Ongoing
  step-case : ∀ c a →
    (proj₁ (step (Ongoing c) a) ≡ Dead)
    ⊎ (proj₁ (step (Ongoing c) a) ≡ Solved (place c a))
    ⊎ (proj₁ (step (Ongoing c) a) ≡ Ongoing (place c a))
  step-case c a with is-dead-config (place c a)
  ... | true  = inj₁ refl
  ... | false with is-solved-config (place c a)
  ...   | true  = inj₂ (inj₁ refl)
  ...   | false = inj₂ (inj₂ refl)

  -- For long configs: step never gives Solved
  step-info-long : ∀ c a → N ≤ length c →
    (proj₁ (step (Ongoing c) a) ≡ Dead)
    ⊎ (proj₁ (step (Ongoing c) a) ≡ Ongoing (place c a)
       × N ≤ length (place c a))
  step-info-long c a N≤len with is-dead-config (place c a)
  ... | true  = inj₁ refl
  ... | false with is-solved-config (place c a) in eq
  ...   | true  = ⊥-elim (true≢false (trans (sym eq) (not-solved-long c a N≤len)))
  ...   | false = inj₂ (refl ,
      subst (N ≤_) (sym (place-length c a)) (≤-trans N≤len (n≤1+n (length c))))

-- KEY LEMMA: when config length ≥ N, solve is always 0
len≥N⇒solve0 : ∀ c → N ≤ length c → ∀ n → solve (Ongoing c) n ≡ 0
len≥N⇒solve0 c N≤len zero =
  max-list-all-0 (λ a → proj₂ (step (Ongoing c) a)) all-actions
    (λ a → rew-0 a (step-info-long c a N≤len))
  where
    rew-0 : ∀ a →
      (proj₁ (step (Ongoing c) a) ≡ Dead) ⊎
      (proj₁ (step (Ongoing c) a) ≡ Ongoing (place c a) × N ≤ length (place c a)) →
      proj₂ (step (Ongoing c) a) ≡ 0
    rew-0 a _ with is-dead-config (place c a)
    ... | true  = refl
    ... | false with is-solved-config (place c a) in eq
    ...   | true  = ⊥-elim (true≢false (trans (sym eq) (not-solved-long c a N≤len)))
    ...   | false = refl
len≥N⇒solve0 c N≤len (suc n) =
  max-list-all-0
    (λ a → solve (proj₁ (step (Ongoing c) a)) n) all-actions
    (λ a → succ-0 a (step-info-long c a N≤len))
  where
    succ-0 : ∀ a →
      (proj₁ (step (Ongoing c) a) ≡ Dead) ⊎
      (proj₁ (step (Ongoing c) a) ≡ Ongoing (place c a) × N ≤ length (place c a)) →
      solve (proj₁ (step (Ongoing c) a)) n ≡ 0
    succ-0 a (inj₁ eq) = subst (λ s → solve s n ≡ 0) (sym eq) (solve-Dead-0 n)
    succ-0 a (inj₂ (eq , N≤len')) =
      subst (λ s → solve s n ≡ 0) (sym eq) (len≥N⇒solve0 (place c a) N≤len' n)

-- Helpers for the solve-horizon-suf proof
private
  -- Fuel equation: suc fuel ≡ N ∸ length c → fuel ≡ N ∸ length (place c a)
  fuel-succ : ∀ fuel c a → suc fuel ≡ N ∸ length c → fuel ≡ N ∸ length (place c a)
  fuel-succ fuel c a eq =
    trans (cong pred eq)
          (trans (sym (∸-suc-pred N (length c)))
                 (sym (cong (N ∸_) (place-length c a))))

  -- Witness that action a appears in all-actions (for AnyElem proofs)
  actions-witness : ∀ {f : Action → ℕ} (a : Action) →
    f a ≡ solved-reward → AnyElem (λ x → f x ≡ solved-reward) all-actions
  actions-witness C0 p = here p
  actions-witness C1 p = there (here p)
  actions-witness C2 p = there (there (here p))
  actions-witness C3 p = there (there (there (here p)))
  actions-witness C4 p = there (there (there (there (here p))))
  actions-witness C5 p = there (there (there (there (there (here p)))))
  actions-witness C6 p = there (there (there (there (there (there (here p))))))
  actions-witness C7 p = there (there (there (there (there (there (there (here p)))))))

  -- Decompose: if solve s (suc m) ≡ 0, each successor's solve at m is 0.
  -- Uses solve-binary (symbolic, no ℕ-level pattern matching) and any-R⇒max-R
  -- to avoid stuck-term issues that caused hangs with the ⊔-based approach.
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

-- Main proof: solve sufficiency for the Queens horizon
--
-- By well-founded induction on fuel = N ∸ length c:
-- - Base (fuel = 0, i.e. length c ≥ N): use len≥N⇒solve0
-- - Step (fuel = suc fuel'):
--     1. solve-component-0 extracts: all successor solves at depth fuel' are 0
--     2. For Dead successors: solve is always 0
--     3. For Solved successors: contradiction (solve = R ≠ 0)
--     4. For Ongoing successors: IH with reduced fuel
--     5. Reassemble: solve (Ongoing c) n = 0 for all n
--
-- IMPORTANT: succ-all-0 is mutually recursive with go but defined
-- separately (not in go's where-clause). This prevents Agda's `with`
-- from trying to abstract over q's type (which would trigger
-- exponential normalization of the solve tree).
private
  mutual
    shs-induct : ∀ fuel c → fuel ≡ N ∸ length c →
         solve (Ongoing c) fuel ≡ 0 → ∀ n → solve (Ongoing c) n ≡ 0
    shs-induct zero c feq q n = len≥N⇒solve0 c (m∸n≡0⇒m≤n (sym feq)) n
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

    -- Each successor's solve at ALL depths is 0.
    -- Takes comp0-a (already instantiated for specific a); q is NOT in scope,
    -- so `with is-dead-config` doesn't trigger exponential normalization.
    -- Using instantiated comp0-a (not universal comp0) ensures the `with`
    -- abstracts is-dead-config in comp0-a's type (no bound variable mismatch).
    shs-succ : ∀ c fuel' →
      (feq : suc fuel' ≡ N ∸ length c) →
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
  shs-induct (N ∸ length c) c refl
     (solve-0-backward* (Ongoing c) horizon (N ∸ length c)
                        (m∸n≤m N (length c)) p)
     n

open WithTraceBridge solve-Dead-0 solve-Solved-R 0<R solve-horizon-suf public

------------------------------------------------------------------------
-- Tests
------------------------------------------------------------------------

-- The Finder's ranking preserves action-value ordering (CoindHomo).
-- This is the key result: for any state s and actions a, b,
-- if the Finder ranks a ≤ b then action-value s a ≤ₛ action-value s b.
test-preserves : ∀ a b s →
  s ranks a ≤ b →
  action-value s a ≤ₛ action-value s b
test-preserves = preserves

------------------------------------------------------------------------
-- Policy extraction: a complete 8-Queens solution
--
-- The Finder's verified policy, when rolled out from the empty board,
-- produces a concrete valid 8-Queens solution.  This is the payoff
-- of the RL framework: not just an abstract correctness proof, but
-- an actual sequence of decisions.
------------------------------------------------------------------------

-- Roll out the Finder's policy for n steps from state s
run-policy : State → ℕ → ℕ → List Action
run-policy _ _ zero = []
run-policy s depth (suc n) =
  let a = find-policy s depth
  in a ∷ run-policy (proj₁ (step s a)) depth n

-- The Finder extracts a complete 8-Queens solution:
-- columns [0, 4, 7, 5, 2, 6, 1, 3] — one of the 92 solutions.
test-solution : run-policy (Ongoing []) N N
              ≡ C0 ∷ C4 ∷ C7 ∷ C5 ∷ C2 ∷ C6 ∷ C1 ∷ C3 ∷ []
test-solution = refl

-- The extracted placement is a valid non-attacking configuration.
test-valid : all-safe (0 ∷ 4 ∷ 7 ∷ 5 ∷ 2 ∷ 6 ∷ 1 ∷ 3 ∷ []) ≡ true
test-valid = refl
