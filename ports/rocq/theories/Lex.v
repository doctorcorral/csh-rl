(* CSHRL portability kernel, Rocq port.
   D13, T8: the stochastic extension's comparison order (Agda reference
   src/CSHRL/Core/Stochastic.agda).

   For stochastic MDPs, pointwise stream dominance on expected-value
   streams is too strong; the paper uses LEXICOGRAPHIC coinductive
   comparison: heads compare, and tails need only compare when the heads
   are equal (earlier rewards break ties).  T8: pointwise dominance
   implies lexicographic dominance, so every deterministic verification
   transfers to the stochastic order for free. *)

From CSHRL Require Import Streams.

Section Lex.
  Variable R : Type.
  Variable le : R -> R -> Prop.

  (* D13a: lexicographic coinductive dominance. *)
  CoInductive lex_le (x y : stream R) : Prop := LexLe {
    lex_head : le (hd x) (hd y);
    lex_tail : hd x = hd y -> lex_le (tl x) (tl y)
  }.

  Hypothesis le_refl : forall r, le r r.

  Lemma lex_le_refl : forall s, lex_le s s.
  Proof.
    cofix CH; intro s; constructor.
    - apply le_refl.
    - intros _; apply CH.
  Qed.

  (* T8: pointwise stream dominance implies lexicographic dominance
     (the converse fails: a strict head win ends the lex comparison). *)
  Theorem stream_le_lex : forall x y, stream_le le x y -> lex_le x y.
  Proof.
    cofix CH; intros x y H; destruct H as [h t]; constructor.
    - exact h.
    - intros _; apply CH; exact t.
  Qed.

  (* D13b: the stochastic optimality condition.  The expected action-value
     stream is a parameter (instantiations build it from the finite
     distribution monad, cf. StochasticCore.expected-action-value); a
     ranking is a stochastic coinductive homomorphism when it preserves
     lexicographic dominance of expected action-value streams. *)
  Variable State Action : Type.
  Variable eqvalue : State -> Action -> stream R.

  Definition StochasticCoindHomo
    (rank : State -> Action -> Action -> Prop) (s : State) : Prop :=
    forall a b, rank s a b -> lex_le (eqvalue s a) (eqvalue s b).

  (* T8 corollary: a ranking that preserves pointwise dominance of the
     expected streams is automatically a stochastic homomorphism. *)
  Theorem pointwise_homo_stochastic :
    forall rank s,
      (forall a b, rank s a b -> stream_le le (eqvalue s a) (eqvalue s b)) ->
      StochasticCoindHomo rank s.
  Proof.
    intros rank s H a b Hab; apply stream_le_lex; apply H; exact Hab.
  Qed.

End Lex.
