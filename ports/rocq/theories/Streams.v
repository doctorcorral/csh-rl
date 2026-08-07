(* CSHRL portability kernel, Rocq port.
   D2-D4, T1: streams, dominance, and the stream isomorphism.

   Streams are negative coinductives (primitive projections), the closest
   analogue of Agda's copattern records in Codata.Guarded.Stream. *)

Set Primitive Projections.

CoInductive stream (R : Type) : Type := Cons { hd : R; tl : stream R }.

Arguments Cons {R} _ _.
Arguments hd {R} _.
Arguments tl {R} _.

(* n-th element, for the pointwise formulation (D4). *)
Fixpoint nth {R : Type} (n : nat) (s : stream R) : R :=
  match n with
  | O => hd s
  | S k => nth k (tl s)
  end.

(* Constant stream, used by instantiations. *)
CoFixpoint const {R : Type} (r : R) : stream R := Cons r (const r).

Lemma nth_const : forall (R : Type) (r : R) (n : nat), nth n (const r) = r.
Proof.
  intros R r n; induction n; simpl; [reflexivity | exact IHn].
Qed.

Section Dominance.
  Variable R : Type.
  Variable le : R -> R -> Prop.

  (* D3: coinductive stream dominance (the paper's _<=s_). *)
  CoInductive stream_le (x y : stream R) : Prop := StreamLe {
    head_le : le (hd x) (hd y);
    tail_le : stream_le (tl x) (tl y)
  }.

  (* D4: pointwise dominance. *)
  Definition pointwise (x y : stream R) : Prop :=
    forall n : nat, le (nth n x) (nth n y).

  (* T1, forward: unfold the coinductive witness n times. *)
  Lemma stream_le_pointwise : forall x y, stream_le x y -> pointwise x y.
  Proof.
    intros x y H n; revert x y H.
    induction n as [| k IH]; intros x y H; destruct H as [h t]; simpl.
    - exact h.
    - apply IH; exact t.
  Qed.

  (* T1, backward: by coinduction. *)
  Lemma pointwise_stream_le : forall x y, pointwise x y -> stream_le x y.
  Proof.
    cofix CH; intros x y H.
    constructor.
    - exact (H O).
    - apply CH; intro n; exact (H (S n)).
  Qed.

  (* T1: the stream isomorphism (paper section 8). *)
  Theorem stream_le_iff_pointwise :
    forall x y, stream_le x y <-> pointwise x y.
  Proof.
    intros x y; split; [apply stream_le_pointwise | apply pointwise_stream_le].
  Qed.

End Dominance.

Arguments stream_le {R} le x y.
Arguments pointwise {R} le x y.
