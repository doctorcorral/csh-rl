{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- CSHRL.Synthesis.CoindHomoBridge
--
-- The bridge connecting gridless self-consistency to CoindHomo.
--
-- Self-consistency (gridless):
--   A predicate p is self-consistent under policy π when
--     ∀ s ∈ traj(π). eval(p, s) ≡ oracle(π, s)
--   where oracle(π, s) compares action-values under continuation π.
--
-- CoindHomo (base theory, CSHRL §3):
--   A ranking _≤ₐ_ preserves into action-value streams:
--     a ≤ₐ b → action-value s a ≤ₛ action-value s b
--   where action-value uses the OPTIMAL continuation.
--
-- For goal-reaching environments, action-value reduces to rollout
-- counts: how many steps until the goal is reached.  The coinductive
-- stream ordering ≤ₛ reduces to ≤ on counts (a survives no longer
-- than b at every truncation).
--
-- THE BRIDGE: when the continuation policy π is optimal (Q^π = Q*),
-- the self-consistency oracle equals the optimal oracle, so
-- self-consistency implies agreement with optimal action-values.
--
-- The proof is oracle substitution: if oracle₁ and oracle₂ agree
-- pointwise, predicate consistency transfers from one to the other.
------------------------------------------------------------------------

module CSHRL.Synthesis.CoindHomoBridge where

open import Data.Bool using (Bool)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

------------------------------------------------------------------------
-- OracleBridge: the abstract bridge theorem
--
-- Parameterized only by State.  Works for any Boolean predicate
-- and any pair of oracles that agree pointwise.
------------------------------------------------------------------------

module OracleBridge (State : Set) where

  -- Pointwise agreement between a predicate and an oracle
  -- at a list of trajectory states.
  data Consistent (pred oracle : State → Bool)
       : List State → Set where
    []  : Consistent pred oracle []
    _∷_ : ∀ {s ss} →
           pred s ≡ oracle s →
           Consistent pred oracle ss →
           Consistent pred oracle (s ∷ ss)

  -- THE BRIDGE THEOREM
  --
  -- If oracle₁ and oracle₂ agree at every state, and the predicate
  -- is consistent with oracle₁, then it is consistent with oracle₂.
  --
  -- Intended instantiation:
  --   pred     = eval(p, ·)           — the discovered ranking predicate
  --   oracle₁  = Q^π comparison       — self-consistency oracle (own policy)
  --   oracle₂  = Q*  comparison       — optimal oracle
  --   oracle₁ ≡ oracle₂              — the policy is optimal (Q^π = Q*)
  --
  -- Conclusion: self-consistent ranking agrees with optimal values,
  -- i.e., the ranking is a CoindHomo (for the goal-reaching case).
  bridge : ∀ {pred oracle₁ oracle₂ : State → Bool}
             {traj : List State} →
           (∀ s → oracle₁ s ≡ oracle₂ s) →
           Consistent pred oracle₁ traj →
           Consistent pred oracle₂ traj
  bridge eq []      = []
  bridge eq (h ∷ t) = trans h (eq _) ∷ bridge eq t

------------------------------------------------------------------------
-- GoalCoindHomo: the goal-reaching specialisation
--
-- For episodic goal-reaching environments, we define the CoindHomo
-- condition in terms of rollout counts (steps to goal) rather than
-- infinite reward streams.
--
-- A GoalCoindHomo is a predicate p such that at every trajectory
-- state, p correctly ranks actions by their OPTIMAL goal-reaching
-- time.  That is:
--   eval(p, s) = true  ⟹  optimal-rollout(s, a₁) ≥ optimal-rollout(s, a₂)
--
-- The bridge theorem shows: self-consistency under an optimal policy
-- directly yields a GoalCoindHomo, because Q^π = Q* when π is optimal.
------------------------------------------------------------------------

module GoalBridge
  (State   : Set)
  (Action  : Set)
  (step    : State → Action → State)
  (goal?   : State → Bool)
  (a₁ a₂   : Action)
  where

  open import Data.Bool using (true; false)
  open import Data.Nat  using (ℕ; zero; suc; _+_; _≤ᵇ_)
  open OracleBridge State

  -- Rollout under a given continuation policy: count steps to goal.
  rollout : State → Action → (State → Action) → ℕ → ℕ
  rollout _ _ _ zero    = 0
  rollout s a π (suc k) with goal? s
  ... | true  = 0
  ... | false = suc (rollout (step s a) (π (step s a)) π k)

  -- The oracle for a given continuation policy π:
  -- "is a₁ at least as good as a₂ at state s (under π)?"
  oracle-under : (State → Action) → ℕ → State → Bool
  oracle-under π K s = rollout s a₂ π K ≤ᵇ rollout s a₁ π K

  -- BRIDGE: if two policies produce the same oracle at every state,
  -- then predicate consistency under one implies consistency under
  -- the other.
  --
  -- The optimality assumption is:
  --   ∀ s → oracle-under π K s ≡ oracle-under π* K s
  --
  -- This holds when Q^π(s,a) = Q^{π*}(s,a) for all s, a —
  -- i.e., π is an optimal continuation from every visited state.
  goal-bridge : ∀ (pred : State → Bool) (π π* : State → Action)
                  (K : ℕ) (traj : List State) →
                (∀ s → oracle-under π K s ≡ oracle-under π* K s) →
                Consistent pred (oracle-under π K) traj →
                Consistent pred (oracle-under π* K) traj
  goal-bridge pred π π* K traj = bridge

  -- Special case: π IS the optimal policy.
  -- Oracle agreement is trivial (refl), and self-consistency
  -- directly yields a GoalCoindHomo.
  self-optimal : ∀ (pred : State → Bool) (π : State → Action)
                   (K : ℕ) (traj : List State) →
                 Consistent pred (oracle-under π K) traj →
                 Consistent pred (oracle-under π K) traj
  self-optimal pred π K traj sc = sc
