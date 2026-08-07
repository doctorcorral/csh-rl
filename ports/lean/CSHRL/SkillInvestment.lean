/-
CSHRL portability kernel, Lean 4 port.
T3 (second instance): the SkillInvestment chain (paper section 6).

A four-stage skill chain: Novice → Apprentice → Expert → Master.  Train pays
0 now but advances the chain; Work pays the current wage (1, 2, 3, then 5 at
Master).  Work's immediate reward always beats Train's, yet training strictly
dominates in capability at every depth.

The value streams are the verified solve-characterizations of the Agda
reference:  Master 5,5,…  Expert 3,5,…  Apprentice 2,3,5,…  Novice 1,2,3,5,…
-/

import CSHRL.Core

namespace CSHRL

open Stream'

inductive SState : Type where
  | Novice | Apprentice | Expert | Master
deriving DecidableEq

inductive SAction : Type where
  | Work | Train
deriving DecidableEq

open SState SAction

def snext : SState → SAction → SState
  | Novice, Train => Apprentice
  | Apprentice, Train => Expert
  | Expert, Train => Master
  | Master, Train => Master
  | s, Work => s

def sreward : SState → SAction → Nat
  | Novice, Work => 1
  | Apprentice, Work => 2
  | Expert, Work => 3
  | Master, _ => 5
  | _, Train => 0

def svalue : SState → Stream' Nat
  | Master => const 5
  | Expert => cons 3 (const 5)
  | Apprentice => cons 2 (cons 3 (const 5))
  | Novice => cons 1 (cons 2 (cons 3 (const 5)))

/-- The correct strategic ranking at Novice: Work ≼ Train. -/
def skillRank : Ranking SState SAction :=
  fun s a b => s = Novice ∧ a = Work ∧ b = Train

/-- T3a: the successor condition holds: staying Novice is dominated by
advancing to Apprentice at every depth. -/
theorem skill_coinductive_homomorphism :
    CoinductiveHomomorphism Nat.le snext svalue skillRank Novice := by
  rintro a b ⟨_, rfl, rfl⟩
  intro n
  match n with
  | 0 => exact Nat.le.step Nat.le.refl                 -- 1 ≤ 2
  | 1 => exact Nat.le.step Nat.le.refl                 -- 2 ≤ 3
  | 2 => exact Nat.le.step (Nat.le.step Nat.le.refl)   -- 3 ≤ 5
  | (k + 3) => exact Nat.le_refl 5

/-- T3b: no CoindHomo ranking can prefer Train (the correct preference):
Work pays 1 now, Train pays 0. -/
theorem skill_no_coindhomo_forward (rank : Ranking SState SAction)
    (h : CoindHomo Nat.le snext sreward svalue rank Novice)
    (hr : rank Novice Work Train) : False :=
  Nat.not_succ_le_zero 0 (h Work Train hr 0)

/-- T3c: nor can it prefer Work: the successor streams fail at depth 0
(Apprentice starts at 2, Novice at 1). -/
theorem skill_no_coindhomo_backward (rank : Ranking SState SAction)
    (h : CoindHomo Nat.le snext sreward svalue rank Novice)
    (hr : rank Novice Train Work) : False :=
  Nat.not_succ_le_zero 0 (Nat.le_of_succ_le_succ (h Train Work hr 1))

end CSHRL
