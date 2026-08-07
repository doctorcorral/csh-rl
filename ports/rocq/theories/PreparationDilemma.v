(* CSHRL portability kernel, Rocq port.
   T3 (third instance): the PreparationDilemma (paper section 6).

   Idle --Prepare (0)--> Ready --Rush (3)--> Producing (3 forever)
   Idle --Rush (1)--> Idle: the temptation pays 1 now, forever mediocre.

   Value streams (verified solve-characterizations of the Agda reference):
     Producing : 3, 3, 3, ...
     Ready     : 3, 3, 3, ...   (Rush reaches Producing immediately)
     Idle      : 1, 3, 3, ...   (one step of preparation unlocks 3) *)

From CSHRL Require Import Streams Core.

Inductive PState : Type := Idle | Ready | Producing.
Inductive PAction : Type := Rush | Prepare.

Definition pnext (s : PState) (a : PAction) : PState :=
  match s, a with
  | Idle, Rush => Idle
  | Idle, Prepare => Ready
  | Ready, Rush => Producing
  | Ready, Prepare => Idle
  | Producing, _ => Producing
  end.

Definition preward (s : PState) (a : PAction) : nat :=
  match s, a with
  | Idle, Rush => 1
  | Idle, Prepare => 0
  | Ready, Rush => 3
  | Ready, Prepare => 0
  | Producing, _ => 3
  end.

Definition pvalue (s : PState) : stream nat :=
  match s with
  | Producing => const 3
  | Ready => const 3
  | Idle => Cons 1 (const 3)
  end.

(* The correct strategic ranking at Idle: Rush <= Prepare. *)
Definition prep_rank : Ranking PState PAction :=
  fun s a b => s = Idle /\ a = Rush /\ b = Prepare.

(* T3a: the successor condition holds: staying Idle is dominated by
   getting Ready at every depth. *)
Theorem prep_coinductive_homomorphism :
  CoinductiveHomomorphism nat le PState PAction pnext pvalue prep_rank Idle.
Proof.
  intros a b [_ [-> ->]]; simpl.
  apply pointwise_stream_le; intro n.
  destruct n as [| k]; simpl; try (rewrite !nth_const);
    repeat (apply le_n || apply le_S).
Qed.

(* T3b: no CoindHomo ranking can prefer Prepare (the correct preference):
   Rush pays 1 now, Prepare pays 0. *)
Theorem prep_no_coindhomo_forward :
  forall rank : Ranking PState PAction,
    CoindHomo nat le PState PAction pnext preward pvalue rank Idle ->
    rank Idle Rush Prepare -> False.
Proof.
  intros rank H Hr.
  destruct (H _ _ Hr) as [h _]; simpl in h.
  inversion h.
Qed.

(* T3c: nor can it prefer Rush: the successor streams fail at depth 0
   (Ready starts at 3, Idle at 1). *)
Theorem prep_no_coindhomo_backward :
  forall rank : Ranking PState PAction,
    CoindHomo nat le PState PAction pnext preward pvalue rank Idle ->
    rank Idle Prepare Rush -> False.
Proof.
  intros rank H Hr.
  destruct (H _ _ Hr) as [_ t]; simpl in t.
  apply (stream_le_pointwise nat le) in t.
  specialize (t O); simpl in t.
  inversion t as [| m h]; inversion h.
Qed.
