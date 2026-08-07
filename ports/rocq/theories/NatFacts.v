(* CSHRL portability kernel, Rocq port.
   Self-contained nat facts shared by Subsumption instantiations and the
   convergence proof, keeping the kernel free of library dependencies
   (only Init is used). *)

Lemma nat_le_trans : forall n m p : nat, n <= m -> m <= p -> n <= p.
Proof.
  intros n m p H1 H2; induction H2; [exact H1 | apply le_S; exact IHle].
Qed.

Lemma nat_add_le_mono_l : forall p n m : nat, n <= m -> p + n <= p + m.
Proof.
  induction p; simpl; intros; [assumption | apply le_n_S; apply IHp; assumption].
Qed.

Lemma nat_add_le_mono_r : forall n m p : nat, n <= m -> n + p <= m + p.
Proof.
  intros n m p H; induction H; simpl; [apply le_n | apply le_S; exact IHle].
Qed.

Lemma nat_add_le_mono :
  forall a b c d : nat, a <= b -> c <= d -> a + c <= b + d.
Proof.
  intros a b c d Hab Hcd.
  apply nat_le_trans with (m := a + d);
    [apply nat_add_le_mono_l; exact Hcd | apply nat_add_le_mono_r; exact Hab].
Qed.

Lemma nat_add_comm : forall a b : nat, a + b = b + a.
Proof.
  induction a; simpl; intros.
  - apply plus_n_O.
  - rewrite IHa; apply plus_n_Sm.
Qed.

Lemma nat_add_assoc : forall a b c : nat, a + (b + c) = (a + b) + c.
Proof.
  induction a; simpl; intros; [reflexivity | rewrite IHa; reflexivity].
Qed.

(* a + (b + c) = b + (a + c): the shuffle used to commute violation counts. *)
Lemma nat_add_shuffle : forall a b c : nat, a + (b + c) = b + (a + c).
Proof.
  intros; rewrite nat_add_assoc, (nat_add_comm a b), <- nat_add_assoc.
  reflexivity.
Qed.

Lemma nat_le_zero : forall n : nat, n <= 0 -> n = 0.
Proof.
  intros n H; inversion H; reflexivity.
Qed.

Lemma nat_add_eq_zero : forall a b : nat, a + b = 0 -> a = 0 /\ b = 0.
Proof.
  intros [| a] b H; simpl in H.
  - split; [reflexivity | exact H].
  - discriminate H.
Qed.
