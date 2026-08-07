(* CSHRL portability kernel, Rocq port.
   D5-D11, T2: the deterministic MDP interface, the two coinductive
   optimality conditions, and the decomposition theorem. *)

From CSHRL Require Import Streams.

Section Core.
  Variable R : Type.
  Variable le : R -> R -> Prop.

  (* D5: deterministic MDP interface. *)
  Variable State Action : Type.
  Variable next : State -> Action -> State.
  Variable reward : State -> Action -> R.

  (* D6: the value stream (capability profile) of a state.  The kernel takes
     it as a parameter; instantiations construct it (e.g. the paper's solve). *)
  Variable value : State -> stream R.

  (* D7: action-value stream = immediate reward consed onto the successor's
     value stream. *)
  Definition qvalue (s : State) (a : Action) : stream R :=
    Cons (reward s a) (value (next s a)).

  (* D8: a ranking of actions at each state. *)
  Definition Ranking : Type := State -> Action -> Action -> Prop.

  (* D9: the successor condition (paper: CoinductiveHomomorphism). *)
  Definition CoinductiveHomomorphism (rank : Ranking) (s : State) : Prop :=
    forall a b, rank s a b -> stream_le le (value (next s a)) (value (next s b)).

  (* D10: immediate-reward compatibility. *)
  Definition RewardCompatible (rank : Ranking) (s : State) : Prop :=
    forall a b, rank s a b -> le (reward s a) (reward s b).

  (* D11: the action-value condition (paper: CoindHomo). *)
  Definition CoindHomo (rank : Ranking) (s : State) : Prop :=
    forall a b, rank s a b -> stream_le le (qvalue s a) (qvalue s b).

  (* T2: the decomposition theorem (paper Theorem 2).  With primitive
     projections, hd/tl of qvalue reduce definitionally, so the proof is a
     single unfolding of the coinductive record. *)
  Theorem decomposition :
    forall (rank : Ranking) (s : State),
      CoindHomo rank s <->
      CoinductiveHomomorphism rank s /\ RewardCompatible rank s.
  Proof.
    intros rank s; split.
    - intro H; split; intros a b Hab; destruct (H a b Hab) as [h t].
      + exact t.
      + exact h.
    - intros [HC HR] a b Hab; constructor; simpl.
      + exact (HR a b Hab).
      + exact (HC a b Hab).
  Qed.

End Core.
