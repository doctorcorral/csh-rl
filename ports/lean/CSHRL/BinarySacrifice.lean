/-
CSHRL portability kernel, Lean 4 port.
T3: strict generality via the BinarySacrifice environment (paper section 6).

GoTrap pays 1 now and 0 forever after; GoParadise pays 0 now and 1 forever
after.  The ranking GoTrap ≼ GoParadise satisfies the successor condition
(CoinductiveHomomorphism), while NO ranking relating the two actions in
either direction satisfies the action-value condition (CoindHomo).
-/

import CSHRL.Core

namespace CSHRL

open Stream'

inductive BState : Type where
  | Start | Trap | Paradise
deriving DecidableEq

inductive BAction : Type where
  | GoTrap | GoParadise
deriving DecidableEq

open BState BAction

def bnext : BState → BAction → BState
  | Start, GoTrap => Trap
  | Start, GoParadise => Paradise
  | s, _ => s

def breward : BState → BAction → Nat
  | Start, GoTrap => 1
  | Start, GoParadise => 0
  | Trap, _ => 0
  | Paradise, _ => 1

/-- Capability profiles: Trap yields 0 forever, Paradise 1 forever. -/
def bvalue : BState → Stream' Nat
  | Trap => const 0
  | Paradise => const 1
  | Start => const 0   -- irrelevant for the theorems below

/-- The correct strategic ranking: GoTrap ≼ GoParadise at Start. -/
def goodRank : Ranking BState BAction :=
  fun s a b => s = Start ∧ a = GoTrap ∧ b = GoParadise

/-- T3a: the successor condition holds for the sacrifice-aware ranking. -/
theorem sacrifice_coinductive_homomorphism :
    CoinductiveHomomorphism Nat.le bnext bvalue goodRank Start := by
  rintro a b ⟨_, rfl, rfl⟩
  exact dominance_const (Nat.zero_le 1)

/-- T3b: no CoindHomo ranking can prefer GoParadise (the correct
preference): the immediate reward comparison 1 ≤ 0 fails at the head. -/
theorem no_coindhomo_forward (rank : Ranking BState BAction)
    (h : CoindHomo Nat.le bnext breward bvalue rank Start)
    (hr : rank Start GoTrap GoParadise) : False :=
  Nat.not_succ_le_zero 0 (h GoTrap GoParadise hr 0)

/-- T3c: nor can it prefer GoTrap (the wrong preference): the successor
streams fail at depth 0 of the tail (index 1 of the action-value stream). -/
theorem no_coindhomo_backward (rank : Ranking BState BAction)
    (h : CoindHomo Nat.le bnext breward bvalue rank Start)
    (hr : rank Start GoParadise GoTrap) : False :=
  Nat.not_succ_le_zero 0 (h GoParadise GoTrap hr 1)

end CSHRL
