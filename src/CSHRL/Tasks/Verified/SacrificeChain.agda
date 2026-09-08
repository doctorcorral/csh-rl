{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Tasks.Verified.SacrificeChain
--
-- The witness family that makes the sacrifice hierarchy STRICT at
-- every level.  Chain n is a two-armed environment with arm length
-- ℓ = suc n:
--
--   start ──delay (r=0)──▸ pst n ─r=0─▸ ... ─r=0─▸ pst 0 ⟳ (r=1)
--         ╲─bribe (r=1)──▸ tst n ─r=1─▸ ... ─r=1─▸ tst 0 ⟳ (r=0)
--
-- The action-value streams at start are
--
--   av(start, delay) = 0 … 0 1 1 1 …   (ℓ+1 zeros, then ones forever)
--   av(start, bribe) = 1 … 1 0 0 0 …   (ℓ+1 ones,  then zeros forever)
--
-- so the two streams cross exactly once, ℓ+1 entries in.  Certified
-- consequences, parametric in n:
--
--   * sacrifice-silent-below: for every k ≤ n, NO ShiftedHomomorphism k
--     can rank bribe below delay at start — every rung up to the arm
--     length is provably silent on the decision that matters.
--     (k = 0: no CoindHomo; k = 1: no CoinductiveHomomorphism — the
--     n = 0 instance recovers exactly BinarySacrifice's theorems.)
--
--   * greed-never-ranked: at NO rung k does any ShiftedHomomorphism
--     rank delay below bribe — deeper shifts only reveal the true
--     ordering, they never invert it.  The hierarchy is conservative.
--
--   * ranks-at-depth: ShiftedHomomorphism (suc n) ranking bribe
--     strictly below delay at start.
--
-- Together: the SACRIFICE DEPTH of Chain n is exactly suc n — a
-- machine-checked invariant measuring how many entries an observation
-- oracle must skip before the optimal action becomes teachable.
------------------------------------------------------------------------

module CSHRL.Tasks.Verified.SacrificeChain where

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _⊔_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties
  using (⊔-idem; ⊔-identityʳ; m+[n∸m]≡n; m≤m+n; ≤-refl; ≤-total)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst₂)
open import Codata.Guarded.Stream using (tail; tabulate)

open import CSHRL.Core
open import CSHRL.Core.ShiftedHomomorphism

module Chain (n : ℕ) where

  ----------------------------------------------------------------------
  -- The environment (arm length ℓ = suc n)
  ----------------------------------------------------------------------

  data State : Set where
    start : State
    pst   : ℕ → State     -- paradise arm: countdown to the r=1 loop
    tst   : ℕ → State     -- bribe arm: countdown to the r=0 loop

  data Action : Set where
    delay bribe : Action

  step : State → Action → State × ℕ
  step start       delay = pst n , 0
  step start       bribe = tst n , 1
  step (pst zero)    _   = pst zero , 1
  step (pst (suc m)) _   = pst m , 0
  step (tst zero)    _   = tst zero , 0
  step (tst (suc m)) _   = tst m , 1

  all-actions : List Action
  all-actions = delay ∷ bribe ∷ []

  open Core State Action ℕ step _≤_ _⊔_ 0 all-actions
  open ShiftedCore State Action ℕ step _≤_ _⊔_ 0 all-actions

  ----------------------------------------------------------------------
  -- Value streams along the arms
  ----------------------------------------------------------------------

  private
    max-self : ∀ x → x ⊔ (x ⊔ 0) ≡ x
    max-self x rewrite ⊔-identityʳ x = ⊔-idem x

  solve-pst0 : ∀ d → solve (pst zero) d ≡ 1
  solve-pst0 zero = refl
  solve-pst0 (suc d) rewrite solve-pst0 d = refl

  solve-tst0 : ∀ d → solve (tst zero) d ≡ 0
  solve-tst0 zero = refl
  solve-tst0 (suc d) rewrite solve-tst0 d = refl

  solve-pst-suc : ∀ m d → solve (pst (suc m)) (suc d) ≡ solve (pst m) d
  solve-pst-suc m d = max-self (solve (pst m) d)

  solve-tst-suc : ∀ m d → solve (tst (suc m)) (suc d) ≡ solve (tst m) d
  solve-tst-suc m d = max-self (solve (tst m) d)

  -- paradise arm: 0 while approaching, 1 from arrival on
  solve-pst-lt : ∀ m d → d < m → solve (pst m) d ≡ 0
  solve-pst-lt (suc m) zero    _       = refl
  solve-pst-lt (suc m) (suc d) (s≤s p) =
    trans (solve-pst-suc m d) (solve-pst-lt m d p)

  solve-pst-ge : ∀ m d → m ≤ d → solve (pst m) d ≡ 1
  solve-pst-ge zero    d       _       = solve-pst0 d
  solve-pst-ge (suc m) (suc d) (s≤s p) =
    trans (solve-pst-suc m d) (solve-pst-ge m d p)

  -- bribe arm: 1 while the bribes last, 0 forever after
  solve-tst-lt : ∀ m d → d < m → solve (tst m) d ≡ 1
  solve-tst-lt (suc m) zero    _       = refl
  solve-tst-lt (suc m) (suc d) (s≤s p) =
    trans (solve-tst-suc m d) (solve-tst-lt m d p)

  solve-tst-ge : ∀ m d → m ≤ d → solve (tst m) d ≡ 0
  solve-tst-ge zero    d       _       = solve-tst0 d
  solve-tst-ge (suc m) (suc d) (s≤s p) =
    trans (solve-tst-suc m d) (solve-tst-ge m d p)

  ----------------------------------------------------------------------
  -- Entries of the action-value streams at start
  --
  --   entry j av(delay) = 0 for j ≤ n,  1 for j ≥ suc n
  --   entry j av(bribe) = 1 for j ≤ n,  0 for j ≥ suc n
  ----------------------------------------------------------------------

  private
    entry-tab : ∀ j (f : ℕ → ℕ) → entry j (tabulate f) ≡ f j
    entry-tab zero    f = refl
    entry-tab (suc j) f = entry-tab j (λ i → f (suc i))

  entry-av : ∀ j s a → entry (suc j) (action-value s a) ≡ solve (proj₁ (step s a)) j
  entry-av j s a = entry-tab j (solve (proj₁ (step s a)))

  delay-early : ∀ k → k ≤ n → entry k (action-value start delay) ≡ 0
  delay-early zero    _   = refl
  delay-early (suc j) j<n = trans (entry-av j start delay) (solve-pst-lt n j j<n)

  bribe-early : ∀ k → k ≤ n → entry k (action-value start bribe) ≡ 1
  bribe-early zero    _   = refl
  bribe-early (suc j) j<n = trans (entry-av j start bribe) (solve-tst-lt n j j<n)

  delay-late : ∀ j → n ≤ j → entry (suc j) (action-value start delay) ≡ 1
  delay-late j n≤j = trans (entry-av j start delay) (solve-pst-ge n j n≤j)

  bribe-late : ∀ j → n ≤ j → entry (suc j) (action-value start bribe) ≡ 0
  bribe-late j n≤j = trans (entry-av j start bribe) (solve-tst-ge n j n≤j)

  ----------------------------------------------------------------------
  -- Silence below the sacrifice depth: for every k ≤ n, no rung-k
  -- homomorphism can rank the sacrifice.  The refutation reads the
  -- FIRST entry of the shifted streams: with k ≤ n entries dropped,
  -- both streams are still in the bribed region, where the bribe arm
  -- pays 1 and the paradise arm pays 0.
  ----------------------------------------------------------------------

  private
    1≰0 : 1 ≤ 0 → ⊥
    1≰0 ()

    ≤-up : ∀ {a b} → a ≤ b → a ≤ suc b
    ≤-up z≤n     = z≤n
    ≤-up (s≤s p) = s≤s (≤-up p)

    +0 : ∀ m → m + 0 ≡ m
    +0 zero    = refl
    +0 (suc m) = cong suc (+0 m)

  sacrifice-silent-below : ∀ k → k ≤ n →
    (h : ShiftedHomomorphism k) →
    ShiftedHomomorphism._≤ₐ_ h start bribe delay → ⊥
  sacrifice-silent-below k k≤n h prf = 1≰0 (subst₂ _≤_ eb ed le)
    where
    dom : dropₛ k (action-value start bribe) ≤ₛ dropₛ k (action-value start delay)
    dom = ShiftedHomomorphism.preserves h bribe delay start prf

    le : entry 0 (dropₛ k (action-value start bribe)) ≤
         entry 0 (dropₛ k (action-value start delay))
    le = entry-mono dom 0

    at-k : ∀ a → entry 0 (dropₛ k (action-value start a)) ≡
                 entry k (action-value start a)
    at-k a = trans (dropₛ-entry k 0 (action-value start a))
                   (cong (λ i → entry i (action-value start a)) (+0 k))

    eb : entry 0 (dropₛ k (action-value start bribe)) ≡ 1
    eb = trans (at-k bribe) (bribe-early k k≤n)

    ed : entry 0 (dropₛ k (action-value start delay)) ≡ 0
    ed = trans (at-k delay) (delay-early k k≤n)

  ----------------------------------------------------------------------
  -- Conservativity: NO rung, however deep, ever ranks the bribe above
  -- the delayed arm.  For shallow shifts (k ≤ suc n) the refutation
  -- reads the crossing entry suc n; for deep shifts (suc n ≤ k) it
  -- reads the first entry, already past the crossing.
  ----------------------------------------------------------------------

  greed-never-ranked : ∀ k (h : ShiftedHomomorphism k) →
    ShiftedHomomorphism._≤ₐ_ h start delay bribe → ⊥
  greed-never-ranked k h prf with ≤-total k (suc n)
  ... | inj₁ k≤sn = 1≰0 (subst₂ _≤_ ed eb (entry-mono dom (suc n ∸ k)))
    where
    dom : dropₛ k (action-value start delay) ≤ₛ dropₛ k (action-value start bribe)
    dom = ShiftedHomomorphism.preserves h delay bribe start prf

    at-cross : ∀ a → entry (suc n ∸ k) (dropₛ k (action-value start a)) ≡
                     entry (suc n) (action-value start a)
    at-cross a = trans (dropₛ-entry k (suc n ∸ k) (action-value start a))
                       (cong (λ i → entry i (action-value start a))
                             (m+[n∸m]≡n k≤sn))

    ed : entry (suc n ∸ k) (dropₛ k (action-value start delay)) ≡ 1
    ed = trans (at-cross delay) (delay-late n ≤-refl)

    eb : entry (suc n ∸ k) (dropₛ k (action-value start bribe)) ≡ 0
    eb = trans (at-cross bribe) (bribe-late n ≤-refl)
  ... | inj₂ (s≤s n≤j) = 1≰0 (subst₂ _≤_ ed eb (entry-mono dom 0))
    where
    dom : dropₛ k (action-value start delay) ≤ₛ dropₛ k (action-value start bribe)
    dom = ShiftedHomomorphism.preserves h delay bribe start prf

    at-k : ∀ a → entry 0 (dropₛ k (action-value start a)) ≡
                 entry k (action-value start a)
    at-k a = trans (dropₛ-entry k 0 (action-value start a))
                   (cong (λ i → entry i (action-value start a)) (+0 k))

    ed : entry 0 (dropₛ k (action-value start delay)) ≡ 1
    ed = trans (at-k delay) (delay-late _ n≤j)

    eb : entry 0 (dropₛ k (action-value start bribe)) ≡ 0
    eb = trans (at-k bribe) (bribe-late _ n≤j)

  ----------------------------------------------------------------------
  -- At the sacrifice depth suc n, the ranking exists: the canonical
  -- relation holding exactly at (start, bribe ≤ delay) is a verified
  -- ShiftedHomomorphism (suc n).
  ----------------------------------------------------------------------

  Rank : State → Action → Action → Set
  Rank start bribe delay = ⊤
  Rank _     _     _     = ⊥

  bribe-dominates :
    dropₛ (suc n) (action-value start bribe) ≤ₛ
    dropₛ (suc n) (action-value start delay)
  bribe-dominates = pointwise→≤ₛ pw
    where
    pw : ∀ j → entry j (dropₛ (suc n) (action-value start bribe)) ≤
               entry j (dropₛ (suc n) (action-value start delay))
    pw j = subst₂ _≤_ (sym eb) (sym ed) z≤n
      where
      eb : entry j (dropₛ (suc n) (action-value start bribe)) ≡ 0
      eb = trans (dropₛ-entry (suc n) j (action-value start bribe))
                 (bribe-late (n + j) (m≤m+n n j))

      ed : entry j (dropₛ (suc n) (action-value start delay)) ≡ 1
      ed = trans (dropₛ-entry (suc n) j (action-value start delay))
                 (delay-late (n + j) (m≤m+n n j))

  ranks-at-depth : ShiftedHomomorphism (suc n)
  ranks-at-depth = record { _≤ₐ_ = Rank ; preserves = pres }
    where
    ≤ₛ-refl : ∀ x → x ≤ₛ x
    head≤ (≤ₛ-refl x) = ≤-refl
    tail≤ (≤ₛ-refl x) = ≤ₛ-refl (tail x)

    pres : ∀ a b s → Rank s a b →
           dropₛ (suc n) (action-value s a) ≤ₛ dropₛ (suc n) (action-value s b)
    pres delay _     start   ()
    pres bribe bribe start   ()
    pres bribe delay start   _  = bribe-dominates
    pres _     _     (pst m) ()
    pres _     _     (tst m) ()

  ranks-the-sacrifice : Rank start bribe delay
  ranks-the-sacrifice = tt
