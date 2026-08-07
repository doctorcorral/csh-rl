(* CSHRL portability kernel, Rocq port.
   T3 (second instance): the SkillInvestment chain (paper section 6).

   A four-stage skill chain: Novice -> Apprentice -> Expert -> Master.
   Train pays 0 now but advances the chain; Work pays the current wage
   (1, 2, 3, then 5 at Master).  Work's immediate reward always beats
   Train's, yet training strictly dominates in capability at every depth.

   The value streams are the verified solve-characterizations of the Agda
   reference (solve-novice-*, solve-apprentice-*, ...):
     Master     : 5, 5, 5, ...
     Expert     : 3, 5, 5, ...
     Apprentice : 2, 3, 5, 5, ...
     Novice     : 1, 2, 3, 5, 5, ... *)

From CSHRL Require Import Streams Core.

Inductive SState : Type := Novice | Apprentice | Expert | Master.
Inductive SAction : Type := Work | Train.

Definition snext (s : SState) (a : SAction) : SState :=
  match s, a with
  | Novice, Train => Apprentice
  | Apprentice, Train => Expert
  | Expert, Train => Master
  | Master, Train => Master
  | s', Work => s'
  end.

Definition sreward (s : SState) (a : SAction) : nat :=
  match s, a with
  | Novice, Work => 1
  | Apprentice, Work => 2
  | Expert, Work => 3
  | Master, _ => 5
  | _, Train => 0
  end.

Definition svalue (s : SState) : stream nat :=
  match s with
  | Master => const 5
  | Expert => Cons 3 (const 5)
  | Apprentice => Cons 2 (Cons 3 (const 5))
  | Novice => Cons 1 (Cons 2 (Cons 3 (const 5)))
  end.

(* The correct strategic ranking at Novice: Work <= Train. *)
Definition skill_rank : Ranking SState SAction :=
  fun s a b => s = Novice /\ a = Work /\ b = Train.

Local Ltac nat_le := repeat (apply le_n || apply le_S).

(* T3a: the successor condition holds: staying Novice is dominated by
   advancing to Apprentice at every depth. *)
Theorem skill_coinductive_homomorphism :
  CoinductiveHomomorphism nat le SState SAction snext svalue skill_rank Novice.
Proof.
  intros a b [_ [-> ->]]; simpl.
  apply pointwise_stream_le; intro n.
  destruct n as [| [| [| k]]]; simpl; try (rewrite !nth_const); nat_le.
Qed.

(* T3b: no CoindHomo ranking can prefer Train (the correct preference):
   Work pays 1 now, Train pays 0. *)
Theorem skill_no_coindhomo_forward :
  forall rank : Ranking SState SAction,
    CoindHomo nat le SState SAction snext sreward svalue rank Novice ->
    rank Novice Work Train -> False.
Proof.
  intros rank H Hr.
  destruct (H _ _ Hr) as [h _]; simpl in h.
  inversion h.
Qed.

(* T3c: nor can it prefer Work: the successor streams fail at depth 0
   (Apprentice starts at 2, Novice at 1). *)
Theorem skill_no_coindhomo_backward :
  forall rank : Ranking SState SAction,
    CoindHomo nat le SState SAction snext sreward svalue rank Novice ->
    rank Novice Train Work -> False.
Proof.
  intros rank H Hr.
  destruct (H _ _ Hr) as [_ t]; simpl in t.
  apply (stream_le_pointwise nat le) in t.
  specialize (t O); simpl in t.
  inversion t as [| m h]; inversion h.
Qed.
