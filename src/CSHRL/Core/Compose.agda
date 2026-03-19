{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Core.Compose
--
-- Compositional Algebra for Verified Rankings.
--
-- Defines a modular framework for composing independently-verified
-- action rankings into rankings on composite environments.
--
-- The central abstraction is VerifiedRanking: a record bundling an
-- action ordering with a proof that it preserves SD[k] at every
-- timestep.  The algebra provides:
--
--   1. Hierarchy subsumption: verified at level k ⟹ verified at k+1
--   2. Product composition: independent components, coordinated ranking
--   3. Concatenation product: reward streams merge via list concat (++)
--   4. Scaling: reward amplification preserves verification
--   5. Scaled product: compose then scale (demonstrating composability)
--   6. Sum composition: disjoint environments, dispatched ranking
--
-- The key practical insight: verify each component in isolation,
-- then compose the proofs automatically.  No re-verification needed.
--
-- All --safe, no postulates.
------------------------------------------------------------------------

module CSHRL.Core.Compose where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import CSHRL.Probability.Finite using (Dist; scale; total-weight)
open import CSHRL.Probability.SD using (_SD[_]≤_; SD-subsumes)
open import CSHRL.Probability.Compose using (SD-++; SD-scale)
open import CSHRL.Probability.FOSD using (_FOSD≤_)
open import CSHRL.Probability.Convolution using (conv; FOSD-conv; FOSD→SD-conv)

------------------------------------------------------------------------
-- Verified Ranking
--
-- Bundles an action ordering with a proof that it preserves SD[k]
-- on a given marginal-reward function at every timestep.
--
-- This is the abstract counterpart of SDCoindHomo: it captures the
-- same preservation property without committing to a specific MDP.
------------------------------------------------------------------------

record VerifiedRanking
  (State Action : Set)
  (marginal : State → Action → ℕ → Dist ℕ)
  (k : ℕ) : Set₁ where
  field
    _≤ₐ_ : State → Action → Action → Set
    preserves : ∀ a b s →
      _≤ₐ_ s a b →
      ∀ n → marginal s a n SD[ k ]≤ marginal s b n

------------------------------------------------------------------------
-- Hierarchy Subsumption on Rankings
--
-- A ranking verified at SD level k is automatically verified at
-- the weaker level k+1.  Free upgrade via SD-subsumes.
------------------------------------------------------------------------

ranking-subsumes : ∀ {S A : Set} {m : S → A → ℕ → Dist ℕ} {k : ℕ} →
  VerifiedRanking S A m k → VerifiedRanking S A m (suc k)
ranking-subsumes {k = k} vr = record
  { _≤ₐ_ = VerifiedRanking._≤ₐ_ vr
  ; preserves = λ a b s p n →
      SD-subsumes k (VerifiedRanking.preserves vr a b s p n)
  }

------------------------------------------------------------------------
-- Product Composition (Abstract)
--
-- Given:
--   • Two component rankings, each verified at SD[k]
--   • A composition operation ⊕ on distributions
--   • A proof that ⊕ preserves SD[k]
--
-- Produces a verified ranking on the product environment where
-- the combined ranking requires BOTH components to rank favorably.
--
-- Marginal rewards compose: marginal(s₁,s₂)(a₁,a₂)(n) =
--   compose(marginal₁(s₁)(a₁)(n), marginal₂(s₂)(a₂)(n))
------------------------------------------------------------------------

product-ranking : ∀ {S₁ A₁ S₂ A₂ : Set}
  {m₁ : S₁ → A₁ → ℕ → Dist ℕ}
  {m₂ : S₂ → A₂ → ℕ → Dist ℕ}
  {k : ℕ}
  (compose : Dist ℕ → Dist ℕ → Dist ℕ)
  (compose-preserves : ∀ {μ₁ ν₁ μ₂ ν₂ : Dist ℕ} →
    μ₁ SD[ k ]≤ ν₁ → μ₂ SD[ k ]≤ ν₂ →
    compose μ₁ μ₂ SD[ k ]≤ compose ν₁ ν₂) →
  VerifiedRanking S₁ A₁ m₁ k →
  VerifiedRanking S₂ A₂ m₂ k →
  VerifiedRanking (S₁ × S₂) (A₁ × A₂)
    (λ { (s₁ , s₂) (a₁ , a₂) n →
      compose (m₁ s₁ a₁ n) (m₂ s₂ a₂ n) }) k
product-ranking compose compose-preserves vr₁ vr₂ = record
  { _≤ₐ_ = λ { (s₁ , s₂) (a₁ , a₂) (b₁ , b₂) →
      VerifiedRanking._≤ₐ_ vr₁ s₁ a₁ b₁ ×
      VerifiedRanking._≤ₐ_ vr₂ s₂ a₂ b₂ }
  ; preserves = λ { (a₁ , a₂) (b₁ , b₂) (s₁ , s₂) (p₁ , p₂) n →
      compose-preserves
        (VerifiedRanking.preserves vr₁ a₁ b₁ s₁ p₁ n)
        (VerifiedRanking.preserves vr₂ a₂ b₂ s₂ p₂ n) }
  }

------------------------------------------------------------------------
-- Concatenation Product (Concrete Instance)
--
-- Instantiates the abstract product with list concatenation (++).
-- Marginal rewards merge as mixtures.  SD[k] preservation comes
-- from SD-++ (proved in Probability.Compose).
------------------------------------------------------------------------

++-product : ∀ {S₁ A₁ S₂ A₂ : Set}
  {m₁ : S₁ → A₁ → ℕ → Dist ℕ}
  {m₂ : S₂ → A₂ → ℕ → Dist ℕ}
  {k : ℕ} →
  VerifiedRanking S₁ A₁ m₁ k →
  VerifiedRanking S₂ A₂ m₂ k →
  VerifiedRanking (S₁ × S₂) (A₁ × A₂)
    (λ { (s₁ , s₂) (a₁ , a₂) n → m₁ s₁ a₁ n ++ m₂ s₂ a₂ n }) k
++-product {k = k} = product-ranking _++_ (SD-++ k)

------------------------------------------------------------------------
-- Convolution Product (Concrete Instance)
--
-- Instantiates the abstract product with convolution (independent sum).
-- Marginal rewards combine by summing independent draws.
-- Requires FOSD-level ranking (the strongest in the hierarchy),
-- then lifts to any SD[k] via FOSD→SD-conv.
--
-- The equal-total-weight condition is an intrinsic requirement of the
-- convolution FOSD theorem (the Abel induction in the base direction
-- needs the weight equality to cancel terms).
------------------------------------------------------------------------

conv-product : ∀ {S₁ A₁ S₂ A₂ : Set}
  {m₁ : S₁ → A₁ → ℕ → Dist ℕ}
  {m₂ : S₂ → A₂ → ℕ → Dist ℕ}
  {k : ℕ} →
  (tw : ∀ s a b n → total-weight (m₁ s a n) ≡ total-weight (m₁ s b n)) →
  VerifiedRanking S₁ A₁ m₁ 0 →
  VerifiedRanking S₂ A₂ m₂ 0 →
  VerifiedRanking (S₁ × S₂) (A₁ × A₂)
    (λ { (s₁ , s₂) (a₁ , a₂) n → conv (m₁ s₁ a₁ n) (m₂ s₂ a₂ n) }) k
conv-product {m₁ = m₁} {m₂ = m₂} {k = k} tw vr₁ vr₂ = record
  { _≤ₐ_ = λ { (s₁ , s₂) (a₁ , a₂) (b₁ , b₂) →
      VerifiedRanking._≤ₐ_ vr₁ s₁ a₁ b₁ ×
      VerifiedRanking._≤ₐ_ vr₂ s₂ a₂ b₂ }
  ; preserves = λ { (a₁ , a₂) (b₁ , b₂) (s₁ , s₂) (p₁ , p₂) n →
      FOSD→SD-conv k
        {m₁ s₁ a₁ n} {m₁ s₁ b₁ n} {m₂ s₂ a₂ n} {m₂ s₂ b₂ n}
        (tw s₁ a₁ b₁ n)
        (VerifiedRanking.preserves vr₁ a₁ b₁ s₁ p₁ n)
        (VerifiedRanking.preserves vr₂ a₂ b₂ s₂ p₂ n) }
  }

------------------------------------------------------------------------
-- Scaling: Reward Amplification
--
-- Multiplying all rewards by a constant c preserves verification.
-- Proved via SD-scale from Probability.Compose.
------------------------------------------------------------------------

scale-ranking : ∀ {S A : Set}
  {m : S → A → ℕ → Dist ℕ}
  {k : ℕ} →
  (c : ℕ) →
  VerifiedRanking S A m k →
  VerifiedRanking S A (λ s a n → scale c (m s a n)) k
scale-ranking {k = k} c vr = record
  { _≤ₐ_ = VerifiedRanking._≤ₐ_ vr
  ; preserves = λ a b s p n →
      SD-scale k c (VerifiedRanking.preserves vr a b s p n)
  }

------------------------------------------------------------------------
-- Scaled Product: Composability Demonstration
--
-- Compose two components via concatenation, then scale rewards.
-- Demonstrates that the algebra composes: scale ∘ ++-product.
------------------------------------------------------------------------

scaled-product : ∀ {S₁ A₁ S₂ A₂ : Set}
  {m₁ : S₁ → A₁ → ℕ → Dist ℕ}
  {m₂ : S₂ → A₂ → ℕ → Dist ℕ}
  {k : ℕ} →
  (c : ℕ) →
  VerifiedRanking S₁ A₁ m₁ k →
  VerifiedRanking S₂ A₂ m₂ k →
  VerifiedRanking (S₁ × S₂) (A₁ × A₂)
    (λ { (s₁ , s₂) (a₁ , a₂) n →
      scale c (m₁ s₁ a₁ n ++ m₂ s₂ a₂ n) }) k
scaled-product c vr₁ vr₂ = scale-ranking c (++-product vr₁ vr₂)

------------------------------------------------------------------------
-- Sum Composition: Disjoint Environments
--
-- Two environments with disjoint state spaces (S₁ ⊎ S₂).
-- The combined ranking dispatches to the appropriate component.
-- Mismatched state/action pairs are excluded by ⊥ (impossible
-- to prove, so never encountered in practice).
--
-- This captures the modularity principle: verifying component 1
-- and component 2 independently suffices for the whole system.
------------------------------------------------------------------------

module SumCompose
  {S₁ A₁ S₂ A₂ : Set}
  {m₁ : S₁ → A₁ → ℕ → Dist ℕ}
  {m₂ : S₂ → A₂ → ℕ → Dist ℕ}
  {k : ℕ}
  where

  sum-marginal : (S₁ ⊎ S₂) → (A₁ ⊎ A₂) → ℕ → Dist ℕ
  sum-marginal (inj₁ s₁) (inj₁ a₁) = m₁ s₁ a₁
  sum-marginal (inj₂ s₂) (inj₂ a₂) = m₂ s₂ a₂
  sum-marginal _          _          = λ _ → []

  sum-ranking :
    VerifiedRanking S₁ A₁ m₁ k →
    VerifiedRanking S₂ A₂ m₂ k →
    VerifiedRanking (S₁ ⊎ S₂) (A₁ ⊎ A₂) sum-marginal k
  sum-ranking vr₁ vr₂ = record
    { _≤ₐ_ = r
    ; preserves = pf
    }
    where
      r : (S₁ ⊎ S₂) → (A₁ ⊎ A₂) → (A₁ ⊎ A₂) → Set
      r (inj₁ s₁) (inj₁ a₁) (inj₁ b₁) = VerifiedRanking._≤ₐ_ vr₁ s₁ a₁ b₁
      r (inj₂ s₂) (inj₂ a₂) (inj₂ b₂) = VerifiedRanking._≤ₐ_ vr₂ s₂ a₂ b₂
      r _          _          _          = ⊥

      pf : ∀ a b s → r s a b →
        ∀ n → sum-marginal s a n SD[ k ]≤ sum-marginal s b n
      pf (inj₁ a₁) (inj₁ b₁) (inj₁ s₁) p =
        VerifiedRanking.preserves vr₁ a₁ b₁ s₁ p
      pf (inj₂ a₂) (inj₂ b₂) (inj₂ s₂) p =
        VerifiedRanking.preserves vr₂ a₂ b₂ s₂ p
      pf (inj₁ _)  (inj₁ _)  (inj₂ _)  ()
      pf (inj₁ _)  (inj₂ _)  (inj₁ _)  ()
      pf (inj₁ _)  (inj₂ _)  (inj₂ _)  ()
      pf (inj₂ _)  (inj₁ _)  (inj₁ _)  ()
      pf (inj₂ _)  (inj₁ _)  (inj₂ _)  ()
      pf (inj₂ _)  (inj₂ _)  (inj₁ _)  ()
