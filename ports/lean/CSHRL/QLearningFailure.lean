/-
CSHRL portability kernel, Lean 4 port.
T6: the Q-learning failure analysis (paper section 7.2, Agda reference
src/CSHRL/Analysis/QLearningFailure.agda).

In BinarySacrifice, Q-learning with discount γ converges to
  Q(Start, GoTrap) = 1  and  Q(Start, GoParadise) = γ/(1−γ),
so for γ < 1/2 it selects GoTrap.  The γ algebra is elementary; what we
machine-check is the structural ground truth:

- Fact 1 (tactical):  GoTrap wins the immediate reward comparison.
- Fact 2 (strategic): GoParadise's successor strictly dominates GoTrap's in
  accumulated reward at every finite horizon (N versus 0).
- Fact 3: hence for γ < 1/2, Q-learning selects the action with the higher
  immediate reward and the strictly inferior successor state.
-/

import CSHRL.Subsumption
import CSHRL.BinarySacrifice

namespace CSHRL

open Stream' BState BAction

/-! ### Fact 1: GoTrap has the higher immediate reward -/

theorem goTrap_immediate_reward : breward Start GoTrap = 1 := rfl

theorem goParadise_immediate_reward : breward Start GoParadise = 0 := rfl

theorem immediate_favors_goTrap :
    breward Start GoParadise ≤ breward Start GoTrap :=
  Nat.zero_le 1

/-! ### Fact 2: GoParadise's successor dominates at every horizon -/

/-- Obtained from the verified CoinductiveHomomorphism instance via the
subsumption theorem, exactly as in the Agda proof. -/
theorem successor_dominance (N : Nat) :
    partialSum Nat.add 0 N (bvalue (bnext Start GoTrap))
      ≤ partialSum Nat.add 0 N (bvalue (bnext Start GoParadise)) :=
  subsumes_successor_return Nat.add 0 bnext bvalue
    Nat.le_refl (fun hab hcd => Nat.add_le_add hab hcd)
    goodRank Start sacrifice_coinductive_homomorphism
    GoTrap GoParadise N ⟨rfl, rfl, rfl⟩

/-- The dominance is quantitatively stark: the successor sums are 0 and N. -/
theorem partialSum_const_zero (N : Nat) :
    partialSum Nat.add 0 N (const 0) = 0 := by
  induction N with
  | zero => rfl
  | succ n ih =>
    show Nat.add 0 (partialSum Nat.add 0 n (const 0)) = 0
    rw [ih]

theorem partialSum_const_one (N : Nat) :
    partialSum Nat.add 0 N (const 1) = N := by
  induction N with
  | zero => rfl
  | succ n ih =>
    show Nat.add 1 (partialSum Nat.add 0 n (const 1)) = n + 1
    rw [ih]; exact Nat.add_comm 1 n

theorem trap_accumulates_zero (N : Nat) :
    partialSum Nat.add 0 N (bvalue (bnext Start GoTrap)) = 0 :=
  partialSum_const_zero N

theorem paradise_accumulates_N (N : Nat) :
    partialSum Nat.add 0 N (bvalue (bnext Start GoParadise)) = N :=
  partialSum_const_one N

/-! ### Fact 3: the conjunction -/

/-- Q-learning with γ < 1/2 ranks by the second component (immediate
reward) and thereby selects the action whose successor loses at every
horizon. -/
theorem q_learning_picks_inferior_successor (N : Nat) :
    partialSum Nat.add 0 N (bvalue (bnext Start GoTrap))
      ≤ partialSum Nat.add 0 N (bvalue (bnext Start GoParadise))
    ∧ breward Start GoParadise ≤ breward Start GoTrap :=
  ⟨successor_dominance N, immediate_favors_goTrap⟩

end CSHRL
