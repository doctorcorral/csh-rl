(* CSHRL portability kernel, Rocq port.
   T3: strict generality via the BinarySacrifice environment (paper section 6).

   GoTrap pays 1 now and 0 forever after; GoParadise pays 0 now and 1 forever
   after.  The ranking GoTrap <= GoParadise satisfies the successor condition
   (CoinductiveHomomorphism), while NO ranking relating the two actions in
   either direction satisfies the action-value condition (CoindHomo). *)

From CSHRL Require Import Streams Core.

Inductive BState : Type := Start | Trap | Paradise.
Inductive BAction : Type := GoTrap | GoParadise.

Definition bnext (s : BState) (a : BAction) : BState :=
  match s, a with
  | Start, GoTrap => Trap
  | Start, GoParadise => Paradise
  | s', _ => s'
  end.

Definition breward (s : BState) (a : BAction) : nat :=
  match s, a with
  | Start, GoTrap => 1
  | Start, GoParadise => 0
  | Trap, _ => 0
  | Paradise, _ => 1
  end.

(* Capability profiles: Trap yields 0 forever, Paradise 1 forever. *)
Definition bvalue (s : BState) : stream nat :=
  match s with
  | Trap => const 0
  | Paradise => const 1
  | Start => const 0 (* irrelevant for the theorems below *)
  end.

(* The correct strategic ranking: GoTrap <= GoParadise at Start. *)
Definition good_rank : Ranking BState BAction :=
  fun s a b => s = Start /\ a = GoTrap /\ b = GoParadise.

(* T3a: the successor condition holds for the sacrifice-aware ranking. *)
Theorem sacrifice_coinductive_homomorphism :
  CoinductiveHomomorphism nat le BState BAction bnext bvalue good_rank Start.
Proof.
  intros a b [_ [-> ->]]; simpl.
  apply pointwise_stream_le; intro n.
  rewrite !nth_const.
  apply le_S, le_n.
Qed.

(* T3b: no CoindHomo ranking can prefer GoParadise (the correct preference):
   the immediate reward comparison 1 <= 0 fails at the head. *)
Theorem no_coindhomo_forward :
  forall rank : Ranking BState BAction,
    CoindHomo nat le BState BAction bnext breward bvalue rank Start ->
    rank Start GoTrap GoParadise -> False.
Proof.
  intros rank H Hr.
  destruct (H _ _ Hr) as [h _]; simpl in h.
  inversion h.
Qed.

(* T3c: nor can it prefer GoTrap (the wrong preference): the successor
   streams fail at depth 0 of the tail. *)
Theorem no_coindhomo_backward :
  forall rank : Ranking BState BAction,
    CoindHomo nat le BState BAction bnext breward bvalue rank Start ->
    rank Start GoParadise GoTrap -> False.
Proof.
  intros rank H Hr.
  destruct (H _ _ Hr) as [_ t]; simpl in t.
  apply (stream_le_pointwise nat le) in t.
  specialize (t O); rewrite !nth_const in t.
  inversion t.
Qed.
