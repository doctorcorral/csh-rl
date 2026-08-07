(* CSHRL portability kernel, Rocq port.
   T4: subsumption of classical argmax (paper section 7, Agda reference
   src/appendix/Arithmetic.agda).

   Pointwise stream dominance implies partial-sum dominance at every finite
   horizon N.  Hence a CoindHomo ranking maximizes every partial sum of
   rewards, and a CoinductiveHomomorphism ranking every partial sum of
   successor value -- classical finite-horizon optimality is a corollary. *)

From CSHRL Require Import Streams Core.

Section Subsumption.
  Variable R : Type.
  Variable le : R -> R -> Prop.

  (* Reward arithmetic, mirroring the CoreWithArithmetic parameters. *)
  Variable add : R -> R -> R.
  Variable zero : R.
  Hypothesis le_refl : forall r, le r r.
  Hypothesis add_mono :
    forall a b c d, le a b -> le c d -> le (add a c) (add b d).

  (* Partial sum of the first N elements of a reward stream. *)
  Fixpoint partial_sum (n : nat) (s : stream R) : R :=
    match n with
    | O => zero
    | S k => add (hd s) (partial_sum k (tl s))
    end.

  Lemma pointwise_tail :
    forall x y, pointwise le x y -> pointwise le (tl x) (tl y).
  Proof.
    intros x y H n; exact (H (S n)).
  Qed.

  (* T4a: partial sums respect pointwise dominance (induction on N). *)
  Lemma partial_sum_mono :
    forall N x y, pointwise le x y -> le (partial_sum N x) (partial_sum N y).
  Proof.
    induction N as [| k IH]; intros x y H; simpl.
    - apply le_refl.
    - apply add_mono.
      + exact (H O).
      + apply IH; apply pointwise_tail; exact H.
  Qed.

  (* The MDP context of Core. *)
  Variable State Action : Type.
  Variable next : State -> Action -> State.
  Variable reward : State -> Action -> R.
  Variable value : State -> stream R.

  (* T4: a CoindHomo ranking dominates every partial sum of the
     action-value stream, at every finite horizon. *)
  Theorem subsumes_partial_sum :
    forall (rank : Ranking State Action) (s : State),
      CoindHomo R le State Action next reward value rank s ->
      forall a b N,
        rank s a b ->
        le (partial_sum N (qvalue R State Action next reward value s a))
           (partial_sum N (qvalue R State Action next reward value s b)).
  Proof.
    intros rank s H a b N Hab.
    apply partial_sum_mono.
    apply stream_le_pointwise.
    exact (H a b Hab).
  Qed.

  (* T4': the successor form, for CoinductiveHomomorphism rankings.  Used by
     the Q-learning failure analysis. *)
  Theorem subsumes_successor_return :
    forall (rank : Ranking State Action) (s : State),
      CoinductiveHomomorphism R le State Action next value rank s ->
      forall a b N,
        rank s a b ->
        le (partial_sum N (value (next s a)))
           (partial_sum N (value (next s b))).
  Proof.
    intros rank s H a b N Hab.
    apply partial_sum_mono.
    apply stream_le_pointwise.
    exact (H a b Hab).
  Qed.

End Subsumption.
