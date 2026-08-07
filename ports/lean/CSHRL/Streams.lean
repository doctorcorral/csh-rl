/-
CSHRL portability kernel, Lean 4 port.
D2-D4, T1: streams, dominance, and the stream isomorphism.

Lean 4 core has no coinductive types, so per the portability spec the port
takes the functional representation (`Nat → R`) with pointwise dominance as
the primary definition.  The stream isomorphism (T1) then takes the form of
two facts that together carry the same content:

- `dominance_unfold`: pointwise dominance unfolds one step, exactly like the
  coinductive record (head inequality plus dominance of the tails);
- `dominance_coind`: pointwise dominance is the *greatest* relation closed
  under that unfolding, i.e. the coinduction principle.  This is the
  functional counterpart of Rocq's `pointwise_stream_le` (built with cofix)
  and Agda's copattern definition.
-/

namespace CSHRL

/-- D2: a stream is a function from time to rewards. -/
def Stream' (R : Type) : Type := Nat → R

namespace Stream'

variable {R : Type}

def head (s : Stream' R) : R := s 0

def tail (s : Stream' R) : Stream' R := fun n => s (n + 1)

def cons (r : R) (s : Stream' R) : Stream' R := fun n =>
  match n with
  | 0 => r
  | n + 1 => s n

def const (r : R) : Stream' R := fun _ => r

@[simp] theorem head_cons (r : R) (s : Stream' R) : head (cons r s) = r := rfl

@[simp] theorem tail_cons (r : R) (s : Stream' R) : tail (cons r s) = s := rfl

@[simp] theorem const_apply (r : R) (n : Nat) : const r n = r := rfl

end Stream'

open Stream'

/-- D3/D4: stream dominance, in its pointwise formulation. -/
def Dominance {R : Type} (le : R → R → Prop) (x y : Stream' R) : Prop :=
  ∀ n, le (x n) (y n)

variable {R : Type} {le : R → R → Prop}

/-- T1a: dominance unfolds exactly like the coinductive record. -/
theorem dominance_unfold {x y : Stream' R} :
    Dominance le x y ↔ le (head x) (head y) ∧ Dominance le (tail x) (tail y) :=
  ⟨fun h => ⟨h 0, fun n => h (n + 1)⟩,
   fun ⟨h0, ht⟩ n => match n with
     | 0 => h0
     | n + 1 => ht n⟩

/-- T1b: the coinduction principle.  Any relation closed under one-step
unfolding is contained in dominance: dominance is the greatest
dominance-bisimulation. -/
theorem dominance_coind (Rel : Stream' R → Stream' R → Prop)
    (step : ∀ x y, Rel x y → le (head x) (head y) ∧ Rel (tail x) (tail y)) :
    ∀ x y, Rel x y → Dominance le x y := by
  intro x y h n
  induction n generalizing x y with
  | zero => exact (step x y h).1
  | succ n ih => exact ih _ _ (step x y h).2

/-- Dominance between constant streams reduces to one inequality. -/
theorem dominance_const {a b : R} (h : le a b) :
    Dominance le (const a) (const b) := fun _ => h

end CSHRL
