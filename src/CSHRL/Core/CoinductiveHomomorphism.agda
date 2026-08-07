{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Core.CoinductiveHomomorphism
--
-- A coinductive optimality condition based on successor state quality.
--
-- An action ranking preserves a CoinductiveHomomorphism when the
-- ranking mirrors the pointwise ordering on optimal value streams
-- from successor states:
--
--   a ≤ₐ b  →  value(next(s,a)) ≤ₛ value(next(s,b))
--
-- This decouples the ranking from immediate transition rewards.
-- An action is ranked higher because it leads to a better state,
-- where "better" unfolds coinductively: a state is better when
-- acting optimally from it yields higher rewards at every future
-- depth, which depends on the quality of reachable states, and so on.
--
-- CoindHomo bundles this condition with an additional constraint
-- on immediate transition rewards (head≤). The decomposition is:
--
--   CoindHomo ⟹ CoinductiveHomomorphism    (strictly more general)
--   CoinductiveHomomorphism + head≤ ⟹ CoindHomo  (exact characterization)
--   Successor partial sums subsumed           (successor return dominance)
------------------------------------------------------------------------

module CSHRL.Core.CoinductiveHomomorphism where

open import Data.List using (List; map; foldr)
open import Codata.Guarded.Stream using (Stream; head; tail; tabulate)
open import Data.Product using (proj₁; proj₂; _×_; _,_)
open import Data.Nat using (ℕ; zero; suc)

open import CSHRL.Core

------------------------------------------------------------------------
-- SuccessorCore: Coinductive condition on successor state quality
------------------------------------------------------------------------

module SuccessorCore
  (State Action Reward : Set)
  (step                : State → Action → State × Reward)
  (_≤ᵣ_                : Reward → Reward → Set)
  (max                 : Reward → Reward → Reward)
  (bottom              : Reward)
  (all-actions         : List Action)
  where

  open Core State Action Reward step _≤ᵣ_ max bottom all-actions

  next : State → Action → State
  next s a = proj₁ (step s a)

  -- Optimal value stream from action a's successor state.
  -- Definitionally equal to tail (action-value s a).
  -- Strips the immediate transition reward, keeping only
  -- the optimal future from where the action leads.
  successor-value : State → Action → StreamR
  successor-value s a = value (next s a)

  ------------------------------------------------------------------------
  -- CoinductiveHomomorphism
  --
  -- The ranking preserves successor state quality:
  -- a ≤ₐ b at s implies the state reached from b has a pointwise-better
  -- optimal value stream than the state reached from a.
  --
  -- The ≤ₛ comparison on value streams unfolds through solve:
  --   depth 0: max immediate reward from next(s,b) ≥ from next(s,a)
  --   depth n: max n-step reward from next(s,b) ≥ from next(s,a)
  --
  -- Each depth comparison depends recursively on deeper successors,
  -- making the coinductive "because" structure explicit:
  -- state(b) is better because its successors' futures dominate,
  -- which holds because their successors' futures dominate, ...
  ------------------------------------------------------------------------

  record CoinductiveHomomorphism : Set₁ where
    field
      _≤ₐ_      : State → Action → Action → Set
      preserves : ∀ a b s → _≤ₐ_ s a b →
                  successor-value s a ≤ₛ successor-value s b

  open CoinductiveHomomorphism {{...}} public

  ------------------------------------------------------------------------
  -- CoindHomo ⟹ CoinductiveHomomorphism
  --
  -- CoindHomo implies CoinductiveHomomorphism: project the tail of
  -- the action-value stream dominance. The converse does NOT hold:
  -- CoinductiveHomomorphism can rank actions where the immediate
  -- reward contradicts successor state quality (sacrifice now, gain later).
  ------------------------------------------------------------------------

  CoindHomo→CoinductiveHomomorphism : CoindHomo → CoinductiveHomomorphism
  CoindHomo→CoinductiveHomomorphism homo = record
    { _≤ₐ_ = CoindHomo._≤ₐ_ homo
    ; preserves = λ a b s prf → tail≤ (CoindHomo.preserves homo a b s prf)
    }

  ------------------------------------------------------------------------
  -- CoinductiveHomomorphism + head condition ⟹ CoindHomo
  --
  -- When immediate transition rewards also respect the ranking,
  -- CoinductiveHomomorphism specializes to CoindHomo. This characterizes
  -- exactly what CoindHomo adds: the head≤ constraint on transition
  -- rewards, which is orthogonal to state quality.
  --
  -- Environments with uniform step costs (all transitions from a
  -- state yield the same immediate reward regardless of action)
  -- satisfy the head condition trivially—the two conditions coincide.
  ------------------------------------------------------------------------

  private
    combine-≤ₛ : ∀ {s a b} →
      proj₂ (step s a) ≤ᵣ proj₂ (step s b) →
      successor-value s a ≤ₛ successor-value s b →
      action-value s a ≤ₛ action-value s b
    head≤ (combine-≤ₛ h _) = h
    tail≤ (combine-≤ₛ _ t) = t

  CoinductiveHomomorphism+Head→CoindHomo :
    (ch : CoinductiveHomomorphism) →
    (∀ a b s → CoinductiveHomomorphism._≤ₐ_ ch s a b →
      proj₂ (step s a) ≤ᵣ proj₂ (step s b)) →
    CoindHomo
  CoinductiveHomomorphism+Head→CoindHomo ch head-compat = record
    { _≤ₐ_ = CoinductiveHomomorphism._≤ₐ_ ch
    ; preserves = λ a b s prf →
        combine-≤ₛ (head-compat a b s prf) (CoinductiveHomomorphism.preserves ch a b s prf)
    }


------------------------------------------------------------------------
-- SuccessorCoreWithArithmetic: Subsumption theorems
------------------------------------------------------------------------

module SuccessorCoreWithArithmetic
  (State Action Reward : Set)
  (step                : State → Action → State × Reward)
  (_≤ᵣ_                : Reward → Reward → Set)
  (max                 : Reward → Reward → Reward)
  (bottom              : Reward)
  (all-actions         : List Action)
  (_+ᵣ_                : Reward → Reward → Reward)
  (≤ᵣ-refl             : ∀ {r} → r ≤ᵣ r)
  (+ᵣ-mono-≤           : ∀ {a b c d} → a ≤ᵣ b → c ≤ᵣ d → (a +ᵣ c) ≤ᵣ (b +ᵣ d))
  where

  open Core State Action Reward step _≤ᵣ_ max bottom all-actions
  open SuccessorCore State Action Reward step _≤ᵣ_ max bottom all-actions

  iter-head : ℕ → StreamR → Reward
  iter-head zero    s = head s
  iter-head (suc n) s = iter-head n (tail s)

  PointwiseDominance : StreamR → StreamR → Set
  PointwiseDominance x y = ∀ n → iter-head n x ≤ᵣ iter-head n y

  ≤ₛ-to-pointwise : ∀ {x y} → x ≤ₛ y → PointwiseDominance x y
  ≤ₛ-to-pointwise p zero    = head≤ p
  ≤ₛ-to-pointwise p (suc n) = ≤ₛ-to-pointwise (tail≤ p) n

  partial-sum : ℕ → StreamR → Reward
  partial-sum zero    _ = bottom
  partial-sum (suc n) s = head s +ᵣ partial-sum n (tail s)

  private
    pointwise-tail : ∀ {x y} → PointwiseDominance x y →
                     PointwiseDominance (tail x) (tail y)
    pointwise-tail pw n = pw (suc n)

  partial-sum-mono : ∀ N x y → PointwiseDominance x y →
                     partial-sum N x ≤ᵣ partial-sum N y
  partial-sum-mono zero _ _ _ = ≤ᵣ-refl
  partial-sum-mono (suc n) x y pw =
    +ᵣ-mono-≤ (pw zero) (partial-sum-mono n (tail x) (tail y) (pointwise-tail pw))

  ------------------------------------------------------------------------
  -- Successor Return Subsumption
  --
  -- If CoinductiveHomomorphism holds and a ≤ₐ b, the cumulative
  -- optimal return from b's successor dominates from a's successor
  -- at every horizon.
  --
  -- This covers the successor component of the total return:
  --   total_return(a, N+1) = reward(s,a) + successor_return(a, N)
  --
  -- We guarantee: successor_return(b, N) ≥ successor_return(a, N)
  -- for all N. The immediate reward is decoupled by design.
  --
  -- For long enough horizons, the growing successor advantage
  -- overwhelms any constant immediate reward deficit.
  ------------------------------------------------------------------------

  SubsumesSuccessorReturn : CoinductiveHomomorphism → Set
  SubsumesSuccessorReturn ch = ∀ s a b N →
    CoinductiveHomomorphism._≤ₐ_ ch s a b →
    partial-sum N (successor-value s a) ≤ᵣ
    partial-sum N (successor-value s b)

  subsumes-successor-return : (ch : CoinductiveHomomorphism) → SubsumesSuccessorReturn ch
  subsumes-successor-return ch s a b N ranking-says =
    partial-sum-mono N (successor-value s a) (successor-value s b) pointwise
    where
      stream-dom : successor-value s a ≤ₛ successor-value s b
      stream-dom = CoinductiveHomomorphism.preserves ch a b s ranking-says
      pointwise : PointwiseDominance (successor-value s a) (successor-value s b)
      pointwise = ≤ₛ-to-pointwise stream-dom

  SuccessorArgmaxSubsumed : CoinductiveHomomorphism → Set
  SuccessorArgmaxSubsumed ch = ∀ s b →
    (∀ a → CoinductiveHomomorphism._≤ₐ_ ch s a b) →
    ∀ a N → partial-sum N (successor-value s a) ≤ᵣ
            partial-sum N (successor-value s b)

  successor-argmax-subsumed : (ch : CoinductiveHomomorphism) → SuccessorArgmaxSubsumed ch
  successor-argmax-subsumed ch s b b-is-top a N =
    subsumes-successor-return ch s a b N (b-is-top a)
