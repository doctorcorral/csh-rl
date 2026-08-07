(* CSHRL portability kernel, Rocq port.
   D16, T12: verified state abstraction (Agda reference
   src/CSHRL/Core/Abstraction.agda).

   Verify a ranking on a finite ABSTRACT system, automatically obtain a
   ranking on the full CONCRETE system -- even when the concrete state
   space is infinite.  The key assumption is marginal-invariance: states
   in the same abstract class have identical marginal reward
   distributions.

   T12: abstract_lift transfers any VerifiedRanking along a state
   abstraction; abstractions compose (identity, product, vertical
   composition), and combine with the convolution product. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
From CSHRL Require Import Dist SDHierarchy Convolution Ranking.

(* D16: a state abstraction is a projection-embedding pair with the
   section law: representatives are consistent. *)
Record StateAbstraction (Concrete Abstract : Type) : Type := {
  project : Concrete -> Abstract;
  embed : Abstract -> Concrete;
  section : forall a, project (embed a) = a
}.

Arguments project {Concrete Abstract}.
Arguments embed {Concrete Abstract}.
Arguments section {Concrete Abstract}.

(* T12: the lifting theorem. *)
Definition abstract_lift
  {Concrete Abstract Action : Type}
  {m : Concrete -> Action -> nat -> Dist nat}
  {k : nat}
  (abs : StateAbstraction Concrete Abstract)
  (invariant :
    forall c1 c2, project abs c1 = project abs c2 ->
    forall a n, m c1 a n = m c2 a n)
  (vr : VerifiedRanking Abstract Action
          (fun s a n => m (embed abs s) a n) k)
  : VerifiedRanking Concrete Action m k.
Proof.
  refine {| vr_rank := fun s a b => vr_rank vr (project abs s) a b |}.
  intros a b s p n.
  assert (eq_s : project abs s = project abs (embed abs (project abs s))).
  { rewrite (section abs); reflexivity. }
  rewrite (invariant s (embed abs (project abs s)) eq_s a n).
  rewrite (invariant s (embed abs (project abs s)) eq_s b n).
  exact (vr_preserves vr a b (project abs s) p n).
Defined.

(* Identity abstraction: the lifting is trivial. *)
Definition id_abstraction {S : Type} : StateAbstraction S S :=
  {| project := fun s => s;
     embed := fun s => s;
     section := fun _ => eq_refl |}.

(* Product abstraction: independent components compose component-wise. *)
Definition product_abstraction
  {C1 A1 C2 A2 : Type}
  (abs1 : StateAbstraction C1 A1) (abs2 : StateAbstraction C2 A2)
  : StateAbstraction (C1 * C2) (A1 * A2).
Proof.
  refine {| project := fun c => (project abs1 (fst c), project abs2 (snd c));
            embed := fun a => (embed abs1 (fst a), embed abs2 (snd a)) |}.
  intros [a1 a2]; simpl.
  rewrite (section abs1), (section abs2); reflexivity.
Defined.

(* Vertical composition: two-stage abstraction in one step. *)
Definition compose_abstraction
  {C M A : Type}
  (abs1 : StateAbstraction C M) (abs2 : StateAbstraction M A)
  : StateAbstraction C A.
Proof.
  refine {| project := fun c => project abs2 (project abs1 c);
            embed := fun a => embed abs1 (embed abs2 a) |}.
  intro a.
  rewrite (section abs1), (section abs2); reflexivity.
Defined.

(* Abstraction-aware convolution product: abstract two components
   independently, verify FOSD rankings on the abstract systems, then
   lift the convolution product to the full concrete system. *)
Definition abstract_conv_product
  {C1 A1 C2 A2 Act1 Act2 : Type}
  {m1 : C1 -> Act1 -> nat -> Dist nat}
  {m2 : C2 -> Act2 -> nat -> Dist nat}
  {k : nat}
  (abs1 : StateAbstraction C1 A1)
  (abs2 : StateAbstraction C2 A2)
  (inv1 : forall c c', project abs1 c = project abs1 c' ->
     forall a n, m1 c a n = m1 c' a n)
  (inv2 : forall c c', project abs2 c = project abs2 c' ->
     forall a n, m2 c a n = m2 c' a n)
  (tw : forall s a b n,
     total_weight (m1 (embed abs1 s) a n) = total_weight (m1 (embed abs1 s) b n))
  (vr1 : VerifiedRanking A1 Act1 (fun s a n => m1 (embed abs1 s) a n) 0)
  (vr2 : VerifiedRanking A2 Act2 (fun s a n => m2 (embed abs2 s) a n) 0)
  : VerifiedRanking (C1 * C2) (Act1 * Act2)
      (fun s a n => conv (m1 (fst s) (fst a) n) (m2 (snd s) (snd a) n)) k.
Proof.
  apply (abstract_lift (product_abstraction abs1 abs2)).
  - intros [c11 c12] [c21 c22] Heq [a1 a2] n; simpl in *.
    injection Heq as Heq1 Heq2.
    rewrite (inv1 c11 c21 Heq1 a1 n), (inv2 c12 c22 Heq2 a2 n).
    reflexivity.
  - exact (conv_product tw vr1 vr2).
Defined.
