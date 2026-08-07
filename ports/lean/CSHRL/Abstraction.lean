/-
CSHRL portability kernel, Lean 4 port.
D16, T12: verified state abstraction (Agda reference
src/CSHRL/Core/Abstraction.agda).

Verify a ranking on a finite ABSTRACT system, automatically obtain a
ranking on the full CONCRETE system — even when the concrete state space
is infinite.  The key assumption is marginal-invariance: states in the
same abstract class have identical marginal reward distributions.

T12: abstractLift transfers any VerifiedRanking along a state
abstraction; abstractions compose (identity, product, vertical
composition), and combine with the convolution product.
-/

import CSHRL.Ranking

namespace CSHRL

/-- D16: a state abstraction is a projection-embedding pair with the
section law: representatives are consistent. -/
structure StateAbstraction (Concrete Abstract : Type) where
  project : Concrete → Abstract
  embed : Abstract → Concrete
  sec : ∀ a, project (embed a) = a

variable {Concrete Abstract Action : Type}

/-- T12: the lifting theorem. -/
def abstractLift
    {m : Concrete → Action → Nat → Dist Nat} {k : Nat}
    (abs : StateAbstraction Concrete Abstract)
    (invariant : ∀ c1 c2, abs.project c1 = abs.project c2 →
      ∀ a n, m c1 a n = m c2 a n)
    (vr : VerifiedRanking Abstract Action
      (fun s a n => m (abs.embed s) a n) k) :
    VerifiedRanking Concrete Action m k where
  rank := fun s a b => vr.rank (abs.project s) a b
  preserves := fun a b s p n => by
    have eq_s : abs.project s = abs.project (abs.embed (abs.project s)) :=
      (abs.sec (abs.project s)).symm
    rw [invariant s (abs.embed (abs.project s)) eq_s a n,
        invariant s (abs.embed (abs.project s)) eq_s b n]
    exact vr.preserves a b (abs.project s) p n

/-- Identity abstraction: the lifting is trivial. -/
def idAbstraction {S : Type} : StateAbstraction S S where
  project := id
  embed := id
  sec := fun _ => rfl

/-- Product abstraction: independent components compose component-wise. -/
def productAbstraction {C1 A1 C2 A2 : Type}
    (abs1 : StateAbstraction C1 A1) (abs2 : StateAbstraction C2 A2) :
    StateAbstraction (C1 × C2) (A1 × A2) where
  project := fun c => (abs1.project c.1, abs2.project c.2)
  embed := fun a => (abs1.embed a.1, abs2.embed a.2)
  sec := fun a => by simp [abs1.sec, abs2.sec]

/-- Vertical composition: two-stage abstraction in one step. -/
def composeAbstraction {C M A : Type}
    (abs1 : StateAbstraction C M) (abs2 : StateAbstraction M A) :
    StateAbstraction C A where
  project := fun c => abs2.project (abs1.project c)
  embed := fun a => abs1.embed (abs2.embed a)
  sec := fun a => by rw [abs1.sec, abs2.sec]

/-- Abstraction-aware convolution product: abstract two components
independently, verify FOSD rankings on the abstract systems, then lift
the convolution product to the full concrete system. -/
def abstractConvProduct
    {C1 A1 C2 A2 Act1 Act2 : Type}
    {m1 : C1 → Act1 → Nat → Dist Nat} {m2 : C2 → Act2 → Nat → Dist Nat}
    {k : Nat}
    (abs1 : StateAbstraction C1 A1) (abs2 : StateAbstraction C2 A2)
    (inv1 : ∀ c c', abs1.project c = abs1.project c' →
      ∀ a n, m1 c a n = m1 c' a n)
    (inv2 : ∀ c c', abs2.project c = abs2.project c' →
      ∀ a n, m2 c a n = m2 c' a n)
    (tw : ∀ s a b n, totalWeight (m1 (abs1.embed s) a n)
      = totalWeight (m1 (abs1.embed s) b n))
    (vr1 : VerifiedRanking A1 Act1 (fun s a n => m1 (abs1.embed s) a n) 0)
    (vr2 : VerifiedRanking A2 Act2 (fun s a n => m2 (abs2.embed s) a n) 0) :
    VerifiedRanking (C1 × C2) (Act1 × Act2)
      (fun s a n => conv (m1 s.1 a.1 n) (m2 s.2 a.2 n)) k :=
  abstractLift (productAbstraction abs1 abs2)
    (fun c1 c2 heq a n => by
      have h1 : abs1.project c1.1 = abs1.project c2.1 :=
        congrArg Prod.fst heq
      have h2 : abs2.project c1.2 = abs2.project c2.2 :=
        congrArg Prod.snd heq
      rw [inv1 c1.1 c2.1 h1 a.1 n, inv2 c1.2 c2.2 h2 a.2 n])
    (convProduct tw vr1 vr2)

end CSHRL
