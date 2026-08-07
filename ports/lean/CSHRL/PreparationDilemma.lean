/-
CSHRL portability kernel, Lean 4 port.
T3 (third instance): the PreparationDilemma (paper section 6).

Idle —Prepare (0)→ Ready —Rush (3)→ Producing (3 forever);
Idle —Rush (1)→ Idle: the temptation pays 1 now, forever mediocre.

Value streams (verified solve-characterizations of the Agda reference):
Producing 3,3,…  Ready 3,3,…  Idle 1,3,3,…
-/

import CSHRL.Core

namespace CSHRL

open Stream'

inductive PState : Type where
  | Idle | Ready | Producing
deriving DecidableEq

inductive PAction : Type where
  | Rush | Prepare
deriving DecidableEq

open PState PAction

def pnext : PState → PAction → PState
  | Idle, Rush => Idle
  | Idle, Prepare => Ready
  | Ready, Rush => Producing
  | Ready, Prepare => Idle
  | Producing, _ => Producing

def preward : PState → PAction → Nat
  | Idle, Rush => 1
  | Idle, Prepare => 0
  | Ready, Rush => 3
  | Ready, Prepare => 0
  | Producing, _ => 3

def pvalue : PState → Stream' Nat
  | Producing => const 3
  | Ready => const 3
  | Idle => cons 1 (const 3)

/-- The correct strategic ranking at Idle: Rush ≼ Prepare. -/
def prepRank : Ranking PState PAction :=
  fun s a b => s = Idle ∧ a = Rush ∧ b = Prepare

/-- T3a: the successor condition holds: staying Idle is dominated by
getting Ready at every depth. -/
theorem prep_coinductive_homomorphism :
    CoinductiveHomomorphism Nat.le pnext pvalue prepRank Idle := by
  rintro a b ⟨_, rfl, rfl⟩
  intro n
  match n with
  | 0 => exact Nat.le.step (Nat.le.step Nat.le.refl)   -- 1 ≤ 3
  | (k + 1) => exact Nat.le_refl 3

/-- T3b: no CoindHomo ranking can prefer Prepare (the correct preference):
Rush pays 1 now, Prepare pays 0. -/
theorem prep_no_coindhomo_forward (rank : Ranking PState PAction)
    (h : CoindHomo Nat.le pnext preward pvalue rank Idle)
    (hr : rank Idle Rush Prepare) : False :=
  Nat.not_succ_le_zero 0 (h Rush Prepare hr 0)

/-- T3c: nor can it prefer Rush: the successor streams fail at depth 0
(Ready starts at 3, Idle at 1). -/
theorem prep_no_coindhomo_backward (rank : Ranking PState PAction)
    (h : CoindHomo Nat.le pnext preward pvalue rank Idle)
    (hr : rank Idle Prepare Rush) : False :=
  Nat.not_succ_le_zero 1 (Nat.le_of_succ_le_succ (h Prepare Rush hr 1))

end CSHRL
