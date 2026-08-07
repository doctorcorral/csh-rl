/-
CSHRL portability kernel, Lean 4 port.
D15, T11: the compositional ranking algebra (Agda reference
src/CSHRL/Core/Compose.agda).

VerifiedRanking bundles an action ordering with a proof that it preserves
SD[k] on a marginal-reward function at every timestep.  The algebra:
verify components in isolation, compose the proofs.

T11a: hierarchy subsumption (free upgrade from level k to k+1);
T11b: product composition for any SD[k]-preserving operation, with
      mixture (++), convolution, and scaling as concrete instances;
T11c: sum composition for disjoint environments.
-/

import CSHRL.Convolution

namespace CSHRL

/-- D15: a verified ranking on marginal rewards, at SD level k. -/
structure VerifiedRanking (State Action : Type)
    (marginal : State → Action → Nat → Dist Nat) (k : Nat) where
  rank : State → Action → Action → Prop
  preserves : ∀ a b s, rank s a b →
    ∀ n, SDle k (marginal s a n) (marginal s b n)

variable {S1 A1 S2 A2 State Action : Type}

/-- T11a: verified at level k, verified at level k+1. -/
def rankingSubsumes {m : State → Action → Nat → Dist Nat} {k : Nat}
    (vr : VerifiedRanking State Action m k) :
    VerifiedRanking State Action m (k + 1) where
  rank := vr.rank
  preserves := fun a b s p n => SD_subsumes k (vr.preserves a b s p n)

/-- T11b: abstract product composition.  Any operation on distributions
that preserves SD[k] composes verified rankings component-wise. -/
def productRanking
    {m1 : S1 → A1 → Nat → Dist Nat} {m2 : S2 → A2 → Nat → Dist Nat} {k : Nat}
    (compose : Dist Nat → Dist Nat → Dist Nat)
    (compose_preserves : ∀ {mu1 nu1 mu2 nu2 : Dist Nat},
      SDle k mu1 nu1 → SDle k mu2 nu2 →
      SDle k (compose mu1 mu2) (compose nu1 nu2))
    (vr1 : VerifiedRanking S1 A1 m1 k) (vr2 : VerifiedRanking S2 A2 m2 k) :
    VerifiedRanking (S1 × S2) (A1 × A2)
      (fun s a n => compose (m1 s.1 a.1 n) (m2 s.2 a.2 n)) k where
  rank := fun s a b => vr1.rank s.1 a.1 b.1 ∧ vr2.rank s.2 a.2 b.2
  preserves := fun a b s p n =>
    compose_preserves
      (vr1.preserves a.1 b.1 s.1 p.1 n)
      (vr2.preserves a.2 b.2 s.2 p.2 n)

/-- Concrete instance: mixture product via concatenation. -/
def appProduct
    {m1 : S1 → A1 → Nat → Dist Nat} {m2 : S2 → A2 → Nat → Dist Nat} {k : Nat}
    (vr1 : VerifiedRanking S1 A1 m1 k) (vr2 : VerifiedRanking S2 A2 m2 k) :
    VerifiedRanking (S1 × S2) (A1 × A2)
      (fun s a n => m1 s.1 a.1 n ++ m2 s.2 a.2 n) k :=
  productRanking (· ++ ·) (SD_append k) vr1 vr2

/-- Concrete instance: scaling preserves verification. -/
def scaleRanking {m : State → Action → Nat → Dist Nat} {k : Nat}
    (c : Nat) (vr : VerifiedRanking State Action m k) :
    VerifiedRanking State Action (fun s a n => dscale c (m s a n)) k where
  rank := vr.rank
  preserves := fun a b s p n => SD_scale k c (vr.preserves a b s p n)

/-- Composability demonstration: compose via ++, then scale. -/
def scaledProduct
    {m1 : S1 → A1 → Nat → Dist Nat} {m2 : S2 → A2 → Nat → Dist Nat} {k : Nat}
    (c : Nat)
    (vr1 : VerifiedRanking S1 A1 m1 k) (vr2 : VerifiedRanking S2 A2 m2 k) :
    VerifiedRanking (S1 × S2) (A1 × A2)
      (fun s a n => dscale c (m1 s.1 a.1 n ++ m2 s.2 a.2 n)) k :=
  scaleRanking c (appProduct vr1 vr2)

/-- Concrete instance: convolution product.  Requires FOSD-level component
rankings (level 0) and equal total weights on the first component; yields
verification at EVERY level k via FOSD_SD_conv. -/
def convProduct
    {m1 : S1 → A1 → Nat → Dist Nat} {m2 : S2 → A2 → Nat → Dist Nat} {k : Nat}
    (tw : ∀ s a b n, totalWeight (m1 s a n) = totalWeight (m1 s b n))
    (vr1 : VerifiedRanking S1 A1 m1 0) (vr2 : VerifiedRanking S2 A2 m2 0) :
    VerifiedRanking (S1 × S2) (A1 × A2)
      (fun s a n => conv (m1 s.1 a.1 n) (m2 s.2 a.2 n)) k where
  rank := fun s a b => vr1.rank s.1 a.1 b.1 ∧ vr2.rank s.2 a.2 b.2
  preserves := fun a b s p n =>
    FOSD_SD_conv k
      (tw s.1 a.1 b.1 n)
      (vr1.preserves a.1 b.1 s.1 p.1 n)
      (vr2.preserves a.2 b.2 s.2 p.2 n)

/-! ### T11c: sum composition for disjoint environments -/

section SumCompose

variable {m1 : S1 → A1 → Nat → Dist Nat} {m2 : S2 → A2 → Nat → Dist Nat} {k : Nat}

def sumMarginal (m1 : S1 → A1 → Nat → Dist Nat) (m2 : S2 → A2 → Nat → Dist Nat) :
    S1 ⊕ S2 → A1 ⊕ A2 → Nat → Dist Nat
  | .inl s1, .inl a1, n => m1 s1 a1 n
  | .inr s2, .inr a2, n => m2 s2 a2 n
  | _, _, _ => []

def sumRank (vr1 : VerifiedRanking S1 A1 m1 k) (vr2 : VerifiedRanking S2 A2 m2 k) :
    S1 ⊕ S2 → A1 ⊕ A2 → A1 ⊕ A2 → Prop
  | .inl s1, .inl a1, .inl b1 => vr1.rank s1 a1 b1
  | .inr s2, .inr a2, .inr b2 => vr2.rank s2 a2 b2
  | _, _, _ => False

/-- The combined ranking dispatches to the matching component;
mismatched state/action combinations are impossible. -/
def sumRanking (vr1 : VerifiedRanking S1 A1 m1 k) (vr2 : VerifiedRanking S2 A2 m2 k) :
    VerifiedRanking (S1 ⊕ S2) (A1 ⊕ A2) (sumMarginal m1 m2) k where
  rank := sumRank vr1 vr2
  preserves := fun a b s p n => by
    match s, a, b, p with
    | .inl s1, .inl a1, .inl b1, p => exact vr1.preserves a1 b1 s1 p n
    | .inr s2, .inr a2, .inr b2, p => exact vr2.preserves a2 b2 s2 p n

end SumCompose

end CSHRL
