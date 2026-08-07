/-
CSHRL portability kernel, Lean 4 port.
T4: subsumption of classical argmax (paper section 7, Agda reference
src/appendix/Arithmetic.agda).

Pointwise stream dominance implies partial-sum dominance at every finite
horizon N, so a CoindHomo ranking maximizes every partial sum of rewards
(successor form for CoinductiveHomomorphism).
-/

import CSHRL.Core

namespace CSHRL

open Stream'

variable {R State Action : Type}

section Arithmetic

variable (add : R → R → R) (zero : R)

/-- Partial sum of the first N elements of a reward stream. -/
def partialSum : Nat → Stream' R → R
  | 0, _ => zero
  | n + 1, s => add (head s) (partialSum n (tail s))

variable {le : R → R → Prop}

theorem dominance_tail {x y : Stream' R} (h : Dominance le x y) :
    Dominance le (tail x) (tail y) := fun n => h (n + 1)

/-- T4a: partial sums respect dominance (induction on N). -/
theorem partialSum_mono
    (le_refl : ∀ r, le r r)
    (add_mono : ∀ {a b c d}, le a b → le c d → le (add a c) (add b d)) :
    ∀ (N : Nat) (x y : Stream' R), Dominance le x y →
      le (partialSum add zero N x) (partialSum add zero N y) := by
  intro N
  induction N with
  | zero => intro x y _; exact le_refl zero
  | succ n ih =>
    intro x y h
    exact add_mono (h 0) (ih (tail x) (tail y) (dominance_tail h))

variable (next : State → Action → State)
variable (reward : State → Action → R)
variable (value : State → Stream' R)

/-- T4: a CoindHomo ranking dominates every partial sum of the action-value
stream, at every finite horizon. -/
theorem subsumes_partial_sum
    (le_refl : ∀ r, le r r)
    (add_mono : ∀ {a b c d}, le a b → le c d → le (add a c) (add b d))
    (rank : Ranking State Action) (s : State)
    (h : CoindHomo le next reward value rank s) :
    ∀ a b N, rank s a b →
      le (partialSum add zero N (qvalue next reward value s a))
         (partialSum add zero N (qvalue next reward value s b)) :=
  fun a b N hab =>
    partialSum_mono add zero le_refl @add_mono N _ _ (h a b hab)

/-- T4': the successor form, for CoinductiveHomomorphism rankings.  Used by
the Q-learning failure analysis. -/
theorem subsumes_successor_return
    (le_refl : ∀ r, le r r)
    (add_mono : ∀ {a b c d}, le a b → le c d → le (add a c) (add b d))
    (rank : Ranking State Action) (s : State)
    (h : CoinductiveHomomorphism le next value rank s) :
    ∀ a b N, rank s a b →
      le (partialSum add zero N (value (next s a)))
         (partialSum add zero N (value (next s b))) :=
  fun a b N hab =>
    partialSum_mono add zero le_refl @add_mono N _ _ (h a b hab)

end Arithmetic

end CSHRL
