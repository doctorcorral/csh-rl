(* CSHRL portability kernel, Rocq port.
   D12: finite discrete distributions as weighted lists (the finite
   distribution monad underlying the stochastic extension, Agda reference
   src/CSHRL/Probability/Finite.agda).

   Weights are unnormalized naturals for decidability.  This file also
   provides the CDF machinery (cdf_weight) that FOSD and the SD hierarchy
   are built on, with its two distributivity laws (concatenation and
   scaling).

   Milestone-3 files use the Rocq Stdlib (lists, arithmetic, lia); it is
   axiom-free, as certified by Print Assumptions in AxiomCheck.v. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.

Definition Dist (A : Type) : Type := list (A * nat).

Definition dpure {A : Type} (a : A) : Dist A := [(a, 1)].

Definition dscale {A : Type} (k : nat) (d : Dist A) : Dist A :=
  map (fun aw => (fst aw, k * snd aw)) d.

Definition dmap {A B : Type} (f : A -> B) (d : Dist A) : Dist B :=
  map (fun aw => (f (fst aw), snd aw)) d.

Fixpoint dbind {A B : Type} (d : Dist A) (f : A -> Dist B) : Dist B :=
  match d with
  | [] => []
  | (a, w) :: rest => dscale w (f a) ++ dbind rest f
  end.

Definition total_weight {A : Type} (d : Dist A) : nat :=
  fold_right (fun aw acc => snd aw + acc) 0 d.

Definition weighted_sum (d : Dist nat) : nat :=
  fold_right (fun vw acc => fst vw * snd vw + acc) 0 d.

(* CDF: total weight of outcomes <= r. *)
Fixpoint cdf_weight (d : Dist nat) (r : nat) : nat :=
  match d with
  | [] => 0
  | (v, w) :: rest => (if v <=? r then w else 0) + cdf_weight rest r
  end.

(* Definitional unfoldings, to keep rewriting under control. *)
Lemma dmap_cons :
  forall {A B : Type} (f : A -> B) (a : A) (w : nat) (d : Dist A),
    dmap f ((a, w) :: d) = (f a, w) :: dmap f d.
Proof. reflexivity. Qed.

Lemma cdf_weight_cons :
  forall v w (d : Dist nat) r,
    cdf_weight ((v, w) :: d) r = (if v <=? r then w else 0) + cdf_weight d r.
Proof. reflexivity. Qed.

(* Distributivity over concatenation (mixture). *)
Lemma cdf_weight_app :
  forall (d1 d2 : Dist nat) r,
    cdf_weight (d1 ++ d2) r = cdf_weight d1 r + cdf_weight d2 r.
Proof.
  induction d1 as [| [v w] d1 IH]; intros d2 r; simpl.
  - reflexivity.
  - rewrite IH; lia.
Qed.

Lemma total_weight_app :
  forall (d1 d2 : Dist nat),
    total_weight (d1 ++ d2) = total_weight d1 + total_weight d2.
Proof.
  induction d1 as [| [v w] d1 IH]; intro d2; simpl.
  - reflexivity.
  - rewrite IH; lia.
Qed.

(* Distributivity over scaling (reward amplification). *)
Lemma cdf_weight_scale :
  forall (d : Dist nat) r k,
    cdf_weight (dscale k d) r = k * cdf_weight d r.
Proof.
  induction d as [| [v w] d IH]; intros r k; simpl.
  - lia.
  - rewrite IH; destruct (v <=? r); lia.
Qed.

Lemma total_weight_scale :
  forall (d : Dist nat) k,
    total_weight (dscale k d) = k * total_weight d.
Proof.
  induction d as [| [v w] d IH]; intro k; simpl.
  - lia.
  - rewrite IH; lia.
Qed.
