{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Core.ShiftedHomomorphism
--
-- The sacrifice hierarchy: a family of optimality conditions indexed
-- by how many stream entries the comparison is allowed to skip.
--
--   ShiftedHomomorphism k:
--     a ≤ₐ b  →  dropₛ k (action-value s a) ≤ₛ dropₛ k (action-value s b)
--
-- The two conditions of the base theory are the first two rungs,
-- definitionally:
--
--   ShiftedHomomorphism 0 = CoindHomo                  (head-first)
--   ShiftedHomomorphism 1 = CoinductiveHomomorphism    (successor)
--
-- Structure of the hierarchy (all proved here):
--
--   * shift-weaken: ShiftedHomomorphism k → ShiftedHomomorphism (suc k)
--     — each rung is at least as permissive as the one before, so the
--     conditions form a chain ordered by how much immediate reward a
--     ranking is allowed to sacrifice.
--
--   * shifted-upgrade: ShiftedHomomorphism (suc k) + entry-k
--     compatibility → ShiftedHomomorphism k — the exact generalization
--     of CoinductiveHomomorphism+Head→CoindHomo: each rung differs
--     from the previous by one head constraint, nothing more.
--
--   * full-upgrade: ShiftedHomomorphism k + compatibility at all
--     entries below k → CoindHomo — folding the ladder back down.
--
-- The hierarchy is STRICT: for every k there is an environment whose
-- critical decision is silent at every rung ≤ k and ranked at rung
-- k+1.  The witness family (delay k rewards to escape a k-step bribe)
-- is Tasks.Verified.SacrificeChain; its arm length is the environment's
-- "sacrifice depth", a machine-checkable invariant measuring how far
-- ahead an observation oracle must look before the optimal action
-- becomes teachable.
------------------------------------------------------------------------

module CSHRL.Core.ShiftedHomomorphism where

open import Data.List using (List)
open import Codata.Guarded.Stream using (Stream; head; tail)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (+-suc)
open import Data.Product using (_×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

open import CSHRL.Core
open import CSHRL.Core.CoinductiveHomomorphism

module ShiftedCore
  (State Action Reward : Set)
  (step                : State → Action → State × Reward)
  (_≤ᵣ_                : Reward → Reward → Set)
  (max                 : Reward → Reward → Reward)
  (bottom              : Reward)
  (all-actions         : List Action)
  where

  open Core State Action Reward step _≤ᵣ_ max bottom all-actions
  open SuccessorCore State Action Reward step _≤ᵣ_ max bottom all-actions
    using (successor-value; CoinductiveHomomorphism)

  --------------------------------------------------------------------
  -- Stream shifting and entry access
  --------------------------------------------------------------------

  dropₛ : ℕ → StreamR → StreamR
  dropₛ zero    xs = xs
  dropₛ (suc k) xs = tail (dropₛ k xs)

  -- the action-value stream with its first k entries discarded
  shifted-value : ℕ → State → Action → StreamR
  shifted-value k s a = dropₛ k (action-value s a)

  entry : ℕ → StreamR → Reward
  entry zero    xs = head xs
  entry (suc j) xs = entry j (tail xs)

  entry-mono : ∀ {x y} → x ≤ₛ y → ∀ j → entry j x ≤ᵣ entry j y
  entry-mono p zero    = head≤ p
  entry-mono p (suc j) = entry-mono (tail≤ p) j

  pointwise→≤ₛ : ∀ {x y} → (∀ j → entry j x ≤ᵣ entry j y) → x ≤ₛ y
  head≤ (pointwise→≤ₛ pw) = pw zero
  tail≤ (pointwise→≤ₛ pw) = pointwise→≤ₛ (λ j → pw (suc j))

  -- reading through a shift: entry j of the k-dropped stream is
  -- entry (k + j) of the original
  dropₛ-entry : ∀ k j (x : StreamR) → entry j (dropₛ k x) ≡ entry (k + j) x
  dropₛ-entry zero    j x = refl
  dropₛ-entry (suc k) j x =
    trans (dropₛ-entry k (suc j) x) (cong (λ i → entry i x) (+-suc k j))

  --------------------------------------------------------------------
  -- The k-shifted condition
  --------------------------------------------------------------------

  record ShiftedHomomorphism (k : ℕ) : Set₁ where
    field
      _≤ₐ_      : State → Action → Action → Set
      preserves : ∀ a b s → _≤ₐ_ s a b →
                  shifted-value k s a ≤ₛ shifted-value k s b

  --------------------------------------------------------------------
  -- Subsumption: each rung is weaker than the previous
  --------------------------------------------------------------------

  shift-weaken : ∀ {k} → ShiftedHomomorphism k → ShiftedHomomorphism (suc k)
  shift-weaken sh = record
    { _≤ₐ_      = ShiftedHomomorphism._≤ₐ_ sh
    ; preserves = λ a b s prf → tail≤ (ShiftedHomomorphism.preserves sh a b s prf)
    }

  shift-weaken-by : ∀ {k} j → ShiftedHomomorphism k → ShiftedHomomorphism (j + k)
  shift-weaken-by zero    sh = sh
  shift-weaken-by (suc j) sh = shift-weaken (shift-weaken-by j sh)

  --------------------------------------------------------------------
  -- Coincidences: the base theory's two conditions are rungs 0 and 1
  -- (both directions are definitional record repackaging)
  --------------------------------------------------------------------

  CoindHomo→Shifted0 : CoindHomo → ShiftedHomomorphism 0
  CoindHomo→Shifted0 h = record
    { _≤ₐ_ = CoindHomo._≤ₐ_ h ; preserves = CoindHomo.preserves h }

  Shifted0→CoindHomo : ShiftedHomomorphism 0 → CoindHomo
  Shifted0→CoindHomo sh = record
    { _≤ₐ_      = ShiftedHomomorphism._≤ₐ_ sh
    ; preserves = ShiftedHomomorphism.preserves sh }

  CoinductiveHomomorphism→Shifted1 :
    CoinductiveHomomorphism → ShiftedHomomorphism 1
  CoinductiveHomomorphism→Shifted1 ch = record
    { _≤ₐ_      = CoinductiveHomomorphism._≤ₐ_ ch
    ; preserves = CoinductiveHomomorphism.preserves ch }

  Shifted1→CoinductiveHomomorphism :
    ShiftedHomomorphism 1 → CoinductiveHomomorphism
  Shifted1→CoinductiveHomomorphism sh = record
    { _≤ₐ_      = ShiftedHomomorphism._≤ₐ_ sh
    ; preserves = ShiftedHomomorphism.preserves sh }

  --------------------------------------------------------------------
  -- Upgrade: one head constraint per rung
  --------------------------------------------------------------------

  private
    glue : ∀ {x y : StreamR} →
           head x ≤ᵣ head y → tail x ≤ₛ tail y → x ≤ₛ y
    head≤ (glue h _) = h
    tail≤ (glue _ t) = t

  shifted-upgrade : ∀ {k} (sh : ShiftedHomomorphism (suc k)) →
    (∀ a b s → ShiftedHomomorphism._≤ₐ_ sh s a b →
       head (shifted-value k s a) ≤ᵣ head (shifted-value k s b)) →
    ShiftedHomomorphism k
  shifted-upgrade sh compat = record
    { _≤ₐ_      = ShiftedHomomorphism._≤ₐ_ sh
    ; preserves = λ a b s prf →
        glue (compat a b s prf) (ShiftedHomomorphism.preserves sh a b s prf)
    }

  -- folding the ladder all the way down: a rung-k homomorphism whose
  -- ranking respects every skipped entry is a CoindHomo
  private
    ≤-up : ∀ {m n} → m ≤ n → m ≤ suc n
    ≤-up z≤n     = z≤n
    ≤-up (s≤s p) = s≤s (≤-up p)

    ≤-id : ∀ {n} → n ≤ n
    ≤-id {zero}  = z≤n
    ≤-id {suc n} = s≤s ≤-id

  full-upgrade : ∀ k (sh : ShiftedHomomorphism k) →
    (∀ j → j < k → ∀ a b s → ShiftedHomomorphism._≤ₐ_ sh s a b →
       head (shifted-value j s a) ≤ᵣ head (shifted-value j s b)) →
    CoindHomo
  full-upgrade zero    sh _      = Shifted0→CoindHomo sh
  full-upgrade (suc k) sh compat =
    full-upgrade k (shifted-upgrade sh (compat k ≤-id))
                   (λ j j<k → compat j (≤-up j<k))
