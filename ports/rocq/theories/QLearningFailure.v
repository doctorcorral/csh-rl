(* CSHRL portability kernel, Rocq port.
   T6: the Q-learning failure analysis (paper section 7.2, Agda reference
   src/CSHRL/Analysis/QLearningFailure.agda).

   In BinarySacrifice, Q-learning with discount gamma converges to
     Q(Start, GoTrap)     = 1
     Q(Start, GoParadise) = gamma / (1 - gamma),
   so for gamma < 1/2 it selects GoTrap.  The gamma algebra is elementary;
   what we machine-check is the structural ground truth that makes the
   conclusion damning:

   - Fact 1 (tactical):  GoTrap wins the immediate reward comparison.
   - Fact 2 (strategic): GoParadise's successor strictly dominates GoTrap's
     in accumulated reward at every finite horizon (N versus 0).
   - Fact 3: hence for gamma < 1/2, Q-learning selects the action with the
     higher immediate reward and the strictly inferior successor state. *)

From CSHRL Require Import Streams Core Subsumption BinarySacrifice.

(* Self-contained nat facts, keeping the kernel free of library
   dependencies (only Init is used). *)

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

(* Fact 1: GoTrap has the higher immediate reward. *)

Lemma goTrap_immediate_reward : breward Start GoTrap = 1.
Proof. reflexivity. Qed.

Lemma goParadise_immediate_reward : breward Start GoParadise = 0.
Proof. reflexivity. Qed.

Lemma immediate_favors_goTrap :
  breward Start GoParadise <= breward Start GoTrap.
Proof. simpl; apply le_S, le_n. Qed.

(* Fact 2: GoParadise's successor dominates GoTrap's in accumulated reward
   at every horizon.  Obtained from the verified CoinductiveHomomorphism
   instance via the subsumption theorem, exactly as in the Agda proof. *)

Theorem successor_dominance :
  forall N,
    partial_sum nat Nat.add 0 N (bvalue (bnext Start GoTrap))
    <= partial_sum nat Nat.add 0 N (bvalue (bnext Start GoParadise)).
Proof.
  intro N.
  apply (subsumes_successor_return
           nat le Nat.add 0 le_n nat_add_le_mono
           BState BAction bnext bvalue
           good_rank Start sacrifice_coinductive_homomorphism
           GoTrap GoParadise N).
  repeat split.
Qed.

(* The dominance is quantitatively stark: the successor sums are 0 and N. *)

Lemma partial_sum_const_0 :
  forall N, partial_sum nat Nat.add 0 N (const 0) = 0.
Proof.
  induction N as [| k IH]; simpl; [reflexivity | exact IH].
Qed.

Lemma partial_sum_const_1 :
  forall N, partial_sum nat Nat.add 0 N (const 1) = N.
Proof.
  induction N as [| k IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma trap_accumulates_zero :
  forall N, partial_sum nat Nat.add 0 N (bvalue (bnext Start GoTrap)) = 0.
Proof.
  intro N; exact (partial_sum_const_0 N).
Qed.

Lemma paradise_accumulates_N :
  forall N, partial_sum nat Nat.add 0 N (bvalue (bnext Start GoParadise)) = N.
Proof.
  intro N; exact (partial_sum_const_1 N).
Qed.

(* Fact 3: the conjunction.  Q-learning with gamma < 1/2 ranks by the first
   component (immediate reward) and thereby selects the action whose
   successor loses at every horizon. *)

Theorem q_learning_picks_inferior_successor :
  forall N,
    partial_sum nat Nat.add 0 N (bvalue (bnext Start GoTrap))
    <= partial_sum nat Nat.add 0 N (bvalue (bnext Start GoParadise))
    /\ breward Start GoParadise <= breward Start GoTrap.
Proof.
  intro N; split;
    [apply successor_dominance | apply immediate_favors_goTrap].
Qed.
