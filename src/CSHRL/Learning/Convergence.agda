{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Learning.Convergence: Closed Convergence of Swap-Based Learning
--
-- This module CLOSES the statement that CSHRL.Learning.Base leaves as an
-- assumption record (ViolationMonotonicityTheorem): each violation
-- repair strictly decreases the violation count, so the learner reaches
-- a ranking that realizes the oracle on EVERY ordered pair within
-- C(n,2) repairs.
--
-- Setting: an explicit ranking is a list of actions, best first, at one
-- state.  The oracle is the ground-truth comparator (oracle a b = true
-- means a ≤ b).  A pair (x before y) is violated when the oracle denies
-- y ≤ x.  The repair is an ADJACENT transposition — the generator set
-- of the symmetric group, matching the paper's narrative (learning
-- walks S_n by transpositions).
--
-- Results, all closed (no assumption records, --safe):
--   swap-adjacent-decreases : an adjacent repair decreases the
--     violation count by EXACTLY one (needs only totality);
--   fix-first-progress : the first-violation repair either certifies
--     zero violations or strictly decreases them (needs transitivity);
--   swap-convergence / swap-convergence-bound : iterating the repair
--     reaches zero violations within violations xs ≤ C(length xs, 2)
--     steps;
--   violations-zero→correct / correct→violations-zero : zero violations
--     means the ranking realizes the oracle on every ordered pair —
--     the homomorphism property at this state;
--   learn-realizes-oracle : the headline corollary.
--
-- For multiple states, instantiate the module once per state with that
-- state's oracle slice: the per-state bounds add up to the global
-- |S| · C(|A|,2) bound.
--
-- This is the Agda back-port of ports/rocq/theories/Convergence.v and
-- ports/lean/CSHRL/Convergence.lean, which were proved first; with this
-- module all three systems carry the theorem in closed form.
------------------------------------------------------------------------

module CSHRL.Learning.Convergence where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; +-mono-≤; +-comm; +-assoc; +-suc;
         n≤0⇒n≡0; m+n≡0⇒m≡0; m+n≡0⇒n≡0; n≤1+n)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

module SwapConvergence
  (Action : Set)
  (oracle : Action → Action → Bool)
  (oracle-total : ∀ a b → oracle a b ≡ true ⊎ oracle b a ≡ true)
  (oracle-trans : ∀ a b c →
    oracle a b ≡ true → oracle b c ≡ true → oracle a c ≡ true)
  where

  private
    -- a + (b + c) ≡ b + (a + c): the shuffle that commutes violation
    -- counts past each other.
    +-shuffle : ∀ a b c → a + (b + c) ≡ b + (a + c)
    +-shuffle a b c =
      trans (sym (+-assoc a b c))
            (trans (cong (_+ c) (+-comm a b)) (+-assoc b a c))

    suc≢0 : ∀ {n} → suc n ≡ 0 → ⊥
    suc≢0 ()

    true≢false : true ≡ false → ⊥
    true≢false ()

    ≤-pred′ : ∀ {m n} → suc m ≤ suc n → m ≤ n
    ≤-pred′ (s≤s p) = p

  ----------------------------------------------------------------------
  -- Violation counting
  ----------------------------------------------------------------------

  -- Violations of x against the actions ranked after it.
  viol-with : Action → List Action → ℕ
  viol-with x [] = 0
  viol-with x (y ∷ ys) = (if oracle y x then 0 else 1) + viol-with x ys

  -- Total violations of a ranking list (sum over all ordered pairs).
  violations : List Action → ℕ
  violations [] = 0
  violations (x ∷ xs) = viol-with x xs + violations xs

  -- viol-with only sees the multiset of later actions.
  viol-with-swap : ∀ p x y pre post →
    viol-with p (pre ++ x ∷ y ∷ post) ≡ viol-with p (pre ++ y ∷ x ∷ post)
  viol-with-swap p x y [] post =
    +-shuffle (if oracle x p then 0 else 1) (if oracle y p then 0 else 1)
              (viol-with p post)
  viol-with-swap p x y (a ∷ pre) post =
    cong ((if oracle a p then 0 else 1) +_) (viol-with-swap p x y pre post)

  ----------------------------------------------------------------------
  -- T7a: an adjacent repair decreases violations by exactly one.
  -- (This is the strict-decrease statement that Base.agda assumes.)
  ----------------------------------------------------------------------

  swap-adjacent-decreases : ∀ pre x y post →
    oracle y x ≡ false → oracle x y ≡ true →
    violations (pre ++ x ∷ y ∷ post) ≡ suc (violations (pre ++ y ∷ x ∷ post))
  swap-adjacent-decreases [] x y post hyx hxy rewrite hyx | hxy =
    cong suc (+-shuffle (viol-with x post) (viol-with y post) (violations post))
  swap-adjacent-decreases (a ∷ pre) x y post hyx hxy =
    trans (cong₂ _+_ (viol-with-swap a x y pre post)
                     (swap-adjacent-decreases pre x y post hyx hxy))
          (+-suc (viol-with a (pre ++ y ∷ x ∷ post))
                 (violations (pre ++ y ∷ x ∷ post)))

  ----------------------------------------------------------------------
  -- Transitivity propagates zero-violation certificates down the list.
  ----------------------------------------------------------------------

  viol-with-mono : ∀ x y rest →
    oracle y x ≡ true → viol-with y rest ≡ 0 → viol-with x rest ≡ 0
  viol-with-mono x y [] hyx h = refl
  viol-with-mono x y (z ∷ r) hyx h = go (oracle z y) refl
    where
    go : (b : Bool) → oracle z y ≡ b → viol-with x (z ∷ r) ≡ 0
    go false e =
      ⊥-elim (suc≢0 (subst (λ b → (if b then 0 else 1) + viol-with y r ≡ 0) e h))
    go true e rewrite oracle-trans z y x e hyx =
      viol-with-mono x y r hyx
        (subst (λ b → (if b then 0 else 1) + viol-with y r ≡ 0) e h)

  ----------------------------------------------------------------------
  -- The repair function: fix the first adjacent violation.
  ----------------------------------------------------------------------

  fix-first : List Action → List Action
  fix-first [] = []
  fix-first (x ∷ []) = x ∷ []
  fix-first (x ∷ y ∷ rest) =
    if oracle y x then x ∷ fix-first (y ∷ rest) else y ∷ x ∷ rest

  -- viol-with is invariant under the repair (it permutes the list).
  viol-with-fix-first : ∀ p t → viol-with p (fix-first t) ≡ viol-with p t
  viol-with-fix-first p [] = refl
  viol-with-fix-first p (x ∷ []) = refl
  viol-with-fix-first p (x ∷ y ∷ rest) =
    go (oracle y x) refl (viol-with-fix-first p (y ∷ rest))
    where
    go : (b : Bool) → oracle y x ≡ b →
      viol-with p (fix-first (y ∷ rest)) ≡ viol-with p (y ∷ rest) →
      viol-with p (fix-first (x ∷ y ∷ rest)) ≡ viol-with p (x ∷ y ∷ rest)
    go true e rec rewrite e =
      cong ((if oracle x p then 0 else 1) +_) rec
    go false e rec rewrite e =
      +-shuffle (if oracle y p then 0 else 1) (if oracle x p then 0 else 1)
                (viol-with p rest)

  ----------------------------------------------------------------------
  -- T7b: the repair either certifies zero violations or strictly
  -- decreases the count.
  ----------------------------------------------------------------------

  fix-first-progress : ∀ xs →
    violations xs ≡ suc (violations (fix-first xs)) ⊎
    (fix-first xs ≡ xs × violations xs ≡ 0)
  fix-first-progress [] = inj₂ (refl , refl)
  fix-first-progress (x ∷ []) = inj₂ (refl , refl)
  fix-first-progress (x ∷ y ∷ rest) =
    go (oracle y x) refl (fix-first-progress (y ∷ rest))
    where
    -- Adjacent violation found: the swap removes exactly one violation.
    dec-case : oracle y x ≡ false → oracle x y ≡ true →
      violations (x ∷ y ∷ rest) ≡ suc (violations (fix-first (x ∷ y ∷ rest)))
    dec-case e h rewrite e | h =
      cong suc (+-shuffle (viol-with x rest) (viol-with y rest) (violations rest))

    -- Adjacent pair fine, recursion found a deeper violation.
    keep-dec : oracle y x ≡ true →
      violations (y ∷ rest) ≡ suc (violations (fix-first (y ∷ rest))) →
      violations (x ∷ y ∷ rest) ≡ suc (violations (fix-first (x ∷ y ∷ rest)))
    keep-dec e hdec rewrite e =
      trans (cong (viol-with x rest +_) hdec)
        (trans (+-suc (viol-with x rest) (violations (fix-first (y ∷ rest))))
          (cong suc (cong (_+ violations (fix-first (y ∷ rest))) (sym W=))))
      where
      W= : viol-with x (fix-first (y ∷ rest)) ≡ viol-with x rest
      W= = trans (viol-with-fix-first x (y ∷ rest))
                 (cong (λ b → (if b then 0 else 1) + viol-with x rest) e)

    -- Adjacent pair fine, recursion certifies zero: propagate the
    -- certificate through transitivity.
    keep-fix : oracle y x ≡ true → fix-first (y ∷ rest) ≡ y ∷ rest →
      fix-first (x ∷ y ∷ rest) ≡ x ∷ y ∷ rest
    keep-fix e hfix rewrite e = cong (x ∷_) hfix

    keep-zero : oracle y x ≡ true → violations (y ∷ rest) ≡ 0 →
      violations (x ∷ y ∷ rest) ≡ 0
    keep-zero e hzero rewrite e =
      cong₂ _+_
        (viol-with-mono x y rest e (m+n≡0⇒m≡0 (viol-with y rest) hzero))
        hzero

    go : (b : Bool) → oracle y x ≡ b →
      (violations (y ∷ rest) ≡ suc (violations (fix-first (y ∷ rest))) ⊎
       (fix-first (y ∷ rest) ≡ y ∷ rest × violations (y ∷ rest) ≡ 0)) →
      violations (x ∷ y ∷ rest) ≡ suc (violations (fix-first (x ∷ y ∷ rest))) ⊎
      (fix-first (x ∷ y ∷ rest) ≡ x ∷ y ∷ rest × violations (x ∷ y ∷ rest) ≡ 0)
    go true e (inj₁ hdec)           = inj₁ (keep-dec e hdec)
    go true e (inj₂ (hfix , hzero)) = inj₂ (keep-fix e hfix , keep-zero e hzero)
    go false e _ with oracle-total x y
    ... | inj₁ hxy = inj₁ (dec-case e hxy)
    ... | inj₂ hyx = ⊥-elim (true≢false (trans (sym hyx) e))

  ----------------------------------------------------------------------
  -- The learner: iterate the repair.
  ----------------------------------------------------------------------

  learn : ℕ → List Action → List Action
  learn zero xs = xs
  learn (suc k) xs = learn k (fix-first xs)

  learn-fuel : ∀ n xs → violations xs ≤ n → violations (learn n xs) ≡ 0
  learn-fuel zero xs h = n≤0⇒n≡0 h
  learn-fuel (suc k) xs h with fix-first-progress xs
  ... | inj₁ hdec =
    learn-fuel k (fix-first xs) (≤-pred′ (subst (_≤ suc k) hdec h))
  ... | inj₂ (hfix , hzero) rewrite hfix =
    learn-fuel k xs (subst (_≤ k) (sym hzero) z≤n)

  -- T7c: convergence within the initial violation count.
  swap-convergence : ∀ xs → violations (learn (violations xs) xs) ≡ 0
  swap-convergence xs = learn-fuel (violations xs) xs ≤-refl

  ----------------------------------------------------------------------
  -- The combinatorial bound C(n, 2).
  ----------------------------------------------------------------------

  pairs : ℕ → ℕ
  pairs zero = 0
  pairs (suc k) = k + pairs k

  viol-with-bound : ∀ x ys → viol-with x ys ≤ length ys
  viol-with-bound x [] = z≤n
  viol-with-bound x (z ∷ r) with oracle z x
  ... | true  = ≤-trans (viol-with-bound x r) (n≤1+n (length r))
  ... | false = s≤s (viol-with-bound x r)

  violations-bound : ∀ xs → violations xs ≤ pairs (length xs)
  violations-bound [] = z≤n
  violations-bound (x ∷ xs) =
    +-mono-≤ (viol-with-bound x xs) (violations-bound xs)

  -- T7d: C(n,2) repairs always suffice.
  swap-convergence-bound : ∀ xs →
    violations (learn (pairs (length xs)) xs) ≡ 0
  swap-convergence-bound xs =
    learn-fuel (pairs (length xs)) xs (violations-bound xs)

  ----------------------------------------------------------------------
  -- Semantics of zero violations: the ranking realizes the oracle on
  -- every ordered pair — the homomorphism property at this state.
  ----------------------------------------------------------------------

  Mem : Action → List Action → Set
  Mem a [] = ⊥
  Mem a (x ∷ xs) = x ≡ a ⊎ Mem a xs

  AllPairsCorrect : List Action → Set
  AllPairsCorrect [] = ⊤
  AllPairsCorrect (x ∷ xs) =
    (∀ y → Mem y xs → oracle y x ≡ true) × AllPairsCorrect xs

  viol-with-zero→correct : ∀ x ys → viol-with x ys ≡ 0 →
    ∀ y → Mem y ys → oracle y x ≡ true
  viol-with-zero→correct x [] h y ()
  viol-with-zero→correct x (z ∷ r) h y m = go (oracle z x) refl m
    where
    go : (b : Bool) → oracle z x ≡ b → z ≡ y ⊎ Mem y r → oracle y x ≡ true
    go false e _ =
      ⊥-elim (suc≢0 (subst (λ b → (if b then 0 else 1) + viol-with x r ≡ 0) e h))
    go true e (inj₁ z≡y) = subst (λ w → oracle w x ≡ true) z≡y e
    go true e (inj₂ m′) =
      viol-with-zero→correct x r
        (subst (λ b → (if b then 0 else 1) + viol-with x r ≡ 0) e h) y m′

  correct→viol-with-zero : ∀ x ys →
    (∀ y → Mem y ys → oracle y x ≡ true) → viol-with x ys ≡ 0
  correct→viol-with-zero x [] h = refl
  correct→viol-with-zero x (z ∷ r) h rewrite h z (inj₁ refl) =
    correct→viol-with-zero x r (λ y m → h y (inj₂ m))

  -- T7e: zero violations = full pairwise realization of the oracle.
  violations-zero→correct : ∀ xs → violations xs ≡ 0 → AllPairsCorrect xs
  violations-zero→correct [] h = tt
  violations-zero→correct (x ∷ xs) h =
    viol-with-zero→correct x xs (m+n≡0⇒m≡0 (viol-with x xs) h) ,
    violations-zero→correct xs (m+n≡0⇒n≡0 (viol-with x xs) h)

  correct→violations-zero : ∀ xs → AllPairsCorrect xs → violations xs ≡ 0
  correct→violations-zero [] _ = refl
  correct→violations-zero (x ∷ xs) (hall , hrest)
    rewrite correct→viol-with-zero x xs hall
          | correct→violations-zero xs hrest = refl

  ----------------------------------------------------------------------
  -- The headline corollary: the learner reaches a ranking that realizes
  -- the oracle on every pair, within C(n,2) repairs.
  ----------------------------------------------------------------------

  learn-realizes-oracle : ∀ xs →
    AllPairsCorrect (learn (pairs (length xs)) xs)
  learn-realizes-oracle xs =
    violations-zero→correct (learn (pairs (length xs)) xs)
      (swap-convergence-bound xs)
