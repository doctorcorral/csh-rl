/-
CSHRL portability kernel, Lean 4 port.
D13, T8: the stochastic extension's comparison order (Agda reference
src/CSHRL/Core/Stochastic.agda).

For stochastic MDPs, pointwise stream dominance on expected-value streams
is too strong; the paper uses LEXICOGRAPHIC coinductive comparison: heads
compare, and tails need only compare when the heads are equal (earlier
rewards break ties).

Functional form: `LexDominance le x y` holds when at every position n, if
the streams agree on all earlier positions then x n ≤ y n.  `lex_unfold`
shows this is exactly the one-step unfolding of the coinductive record
(head inequality, plus lex dominance of the tails when the heads agree).

T8: pointwise dominance implies lexicographic dominance, so every
deterministic verification transfers to the stochastic order for free.
-/

import CSHRL.Streams

namespace CSHRL

open Stream'

variable {R : Type} {le : R → R → Prop}

/-- D13a: lexicographic dominance, functional form. -/
def LexDominance (le : R → R → Prop) (x y : Stream' R) : Prop :=
  ∀ n, (∀ m, m < n → x m = y m) → le (x n) (y n)

theorem lex_refl (le_refl : ∀ r, le r r) (s : Stream' R) :
    LexDominance le s s :=
  fun n _ => le_refl (s n)

/-- The functional form unfolds exactly like the coinductive record. -/
theorem lex_unfold {x y : Stream' R} :
    LexDominance le x y ↔
      le (head x) (head y) ∧
      (head x = head y → LexDominance le (tail x) (tail y)) := by
  constructor
  · intro h
    refine ⟨h 0 (fun m hm => absurd hm (Nat.not_lt_zero m)), ?_⟩
    intro he n hagree
    exact h (n + 1) (fun m hm =>
      match m with
      | 0 => he
      | m + 1 => hagree m (Nat.lt_of_succ_lt_succ hm))
  · rintro ⟨h0, ht⟩ n hagree
    match n with
    | 0 => exact h0
    | n + 1 =>
      exact ht (hagree 0 (Nat.succ_pos n)) n
        (fun m hm => hagree (m + 1) (Nat.succ_lt_succ hm))

/-- T8: pointwise stream dominance implies lexicographic dominance
(the converse fails: a strict head win ends the lex comparison). -/
theorem dominance_lex {x y : Stream' R} (h : Dominance le x y) :
    LexDominance le x y :=
  fun n _ => h n

/-- D13b: the stochastic optimality condition.  The expected action-value
stream is a parameter (instantiations build it from the finite
distribution monad); a ranking is a stochastic coinductive homomorphism
when it preserves lexicographic dominance of expected action-value
streams. -/
def StochasticCoindHomo {State Action : Type}
    (le : R → R → Prop) (eqvalue : State → Action → Stream' R)
    (rank : State → Action → Action → Prop) (s : State) : Prop :=
  ∀ a b, rank s a b → LexDominance le (eqvalue s a) (eqvalue s b)

/-- T8 corollary: a ranking that preserves pointwise dominance of the
expected streams is automatically a stochastic homomorphism. -/
theorem pointwise_homo_stochastic {State Action : Type}
    (eqvalue : State → Action → Stream' R)
    (rank : State → Action → Action → Prop) (s : State)
    (h : ∀ a b, rank s a b → Dominance le (eqvalue s a) (eqvalue s b)) :
    StochasticCoindHomo le eqvalue rank s :=
  fun a b hab => dominance_lex (h a b hab)

end CSHRL
