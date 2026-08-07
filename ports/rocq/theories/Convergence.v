(* CSHRL portability kernel, Rocq port.
   T7: closed convergence of swap-based learning (paper section 14).

   This closes the statement that is an assumption record in the Agda
   reference (ViolationMonotonicityTheorem in Learning/Base.agda): each
   violation repair strictly decreases the total violation count, so the
   learner converges to a ranking that realizes the oracle on EVERY pair
   in at most C(n,2) repairs per state.

   Setting: an explicit ranking is a list of actions, best first, at one
   state.  The oracle is the ground-truth comparator (oracle a b = true
   means a <= b).  A pair (x before y) is violated when the oracle denies
   y <= x.  The repair is an ADJACENT transposition -- the generator set
   of the symmetric group, matching the paper's narrative that learning
   walks S_n by transpositions.

   Results, all closed (no assumption records):
   - swap_adjacent_decreases: an adjacent repair decreases the violation
     count by EXACTLY one (needs only totality of the oracle);
   - fix_first_progress: the first-violation repair either certifies zero
     violations or strictly decreases them (needs transitivity);
   - swap_convergence / swap_convergence_bound: iterating the repair
     reaches zero violations within violations(xs) <= C(length xs, 2)
     steps;
   - violations_zero_iff: zero violations means the ranking realizes the
     oracle on every ordered pair -- the homomorphism property at this
     state. *)

From CSHRL Require Import NatFacts.

Local Open Scope list_scope.

Section Convergence.
  Variable Action : Type.
  Variable oracle : Action -> Action -> bool.

  Hypothesis oracle_total :
    forall a b, oracle a b = true \/ oracle b a = true.
  Hypothesis oracle_trans :
    forall a b c, oracle a b = true -> oracle b c = true -> oracle a c = true.

  (* Violations of x against the actions ranked after it. *)
  Fixpoint viol_with (x : Action) (ys : list Action) : nat :=
    match ys with
    | nil => 0
    | y :: ys' => (if oracle y x then 0 else 1) + viol_with x ys'
    end.

  (* Total violations of a ranking list (sum over all ordered pairs). *)
  Fixpoint violations (xs : list Action) : nat :=
    match xs with
    | nil => 0
    | x :: xs' => viol_with x xs' + violations xs'
    end.

  (* viol_with only sees the multiset of later actions. *)
  Lemma viol_with_swap :
    forall p x y pre post,
      viol_with p (pre ++ x :: y :: post)
      = viol_with p (pre ++ y :: x :: post).
  Proof.
    intros p x y pre post; induction pre as [| a pre IH]; simpl.
    - apply nat_add_shuffle.
    - rewrite IH; reflexivity.
  Qed.

  (* T7a: an adjacent repair decreases violations by exactly one. *)
  Theorem swap_adjacent_decreases :
    forall pre x y post,
      oracle y x = false ->
      oracle x y = true ->
      violations (pre ++ x :: y :: post)
      = S (violations (pre ++ y :: x :: post)).
  Proof.
    intros pre x y post Hyx Hxy; induction pre as [| a pre IH]; simpl.
    - rewrite Hyx, Hxy; simpl.
      rewrite (nat_add_shuffle (viol_with x post) (viol_with y post)).
      reflexivity.
    - rewrite IH, (viol_with_swap a x y pre post).
      symmetry; apply plus_n_Sm.
  Qed.

  (* Transitivity propagates zero-violation certificates down the list. *)
  Lemma viol_with_mono :
    forall x y rest,
      oracle y x = true -> viol_with y rest = 0 -> viol_with x rest = 0.
  Proof.
    intros x y rest Hyx H; induction rest as [| z r IH]; simpl in *.
    - reflexivity.
    - destruct (oracle z y) eqn:E; simpl in H.
      + rewrite (oracle_trans z y x E Hyx); simpl.
        apply IH; exact H.
      + discriminate H.
  Qed.

  (* The repair function: fix the first adjacent violation. *)
  Fixpoint fix_first (xs : list Action) : list Action :=
    match xs with
    | x :: ((y :: rest) as t) =>
        if oracle y x then x :: fix_first t else y :: x :: rest
    | _ => xs
    end.

  (* Definitional unfoldings, used to keep rewriting under control. *)
  Lemma viol_with_cons :
    forall x y t,
      viol_with x (y :: t) = (if oracle y x then 0 else 1) + viol_with x t.
  Proof. reflexivity. Qed.

  Lemma violations_cons :
    forall x t, violations (x :: t) = viol_with x t + violations t.
  Proof. reflexivity. Qed.

  (* viol_with is invariant under the repair (it permutes the list). *)
  Lemma viol_with_fix_first :
    forall p t, viol_with p (fix_first t) = viol_with p t.
  Proof.
    intros p t; induction t as [| a t IH]; simpl.
    - reflexivity.
    - destruct t as [| b r]; simpl.
      + reflexivity.
      + destruct (oracle b a) eqn:E; simpl.
        * simpl in IH; rewrite IH; reflexivity.
        * apply nat_add_shuffle.
    Qed.

  (* T7b: the repair either certifies zero violations or strictly
     decreases the count. *)
  Theorem fix_first_progress :
    forall xs,
      violations xs = S (violations (fix_first xs))
      \/ (fix_first xs = xs /\ violations xs = 0).
  Proof.
    induction xs as [| x xs IH].
    - right; split; reflexivity.
    - destruct xs as [| y rest].
      + right; split; reflexivity.
      + change (fix_first (x :: y :: rest))
          with (if oracle y x
                then x :: fix_first (y :: rest)
                else y :: x :: rest).
        destruct (oracle y x) eqn:E.
        * (* adjacent pair fine; recurse *)
          destruct IH as [Hdec | [Hfix Hzero]].
          -- left.
             rewrite (violations_cons x (y :: rest)).
             rewrite (violations_cons x (fix_first (y :: rest))).
             rewrite (viol_with_fix_first x (y :: rest)).
             rewrite Hdec.
             symmetry; apply plus_n_Sm.
          -- right; split.
             ++ rewrite Hfix; reflexivity.
             ++ rewrite violations_cons in Hzero.
                destruct (nat_add_eq_zero _ _ Hzero) as [Hy Hr].
                rewrite (violations_cons x (y :: rest)).
                rewrite (viol_with_cons x y rest), E.
                rewrite (viol_with_mono x y rest E Hy).
                rewrite (violations_cons y rest), Hy, Hr.
                reflexivity.
        * (* adjacent violation found: swap it *)
          left.
          destruct (oracle_total x y) as [Hxy | Hyx];
            [| rewrite Hyx in E; discriminate E].
          exact (swap_adjacent_decreases nil x y rest E Hxy).
  Qed.

  (* The learner: iterate the repair. *)
  Fixpoint learn (fuel : nat) (xs : list Action) : list Action :=
    match fuel with
    | 0 => xs
    | S k => learn k (fix_first xs)
    end.

  Lemma learn_fuel :
    forall n xs, violations xs <= n -> violations (learn n xs) = 0.
  Proof.
    induction n as [| k IH]; intros xs H; simpl.
    - exact (nat_le_zero _ H).
    - destruct (fix_first_progress xs) as [Hdec | [Hfix Hzero]].
      + apply IH.
        apply le_S_n.
        rewrite <- Hdec; exact H.
      + rewrite Hfix.
        apply IH.
        rewrite Hzero; apply le_0_n.
  Qed.

  (* T7c: convergence within the initial violation count. *)
  Theorem swap_convergence :
    forall xs, violations (learn (violations xs) xs) = 0.
  Proof.
    intro xs; apply learn_fuel; apply le_n.
  Qed.

  (* The combinatorial bound C(n, 2). *)
  Fixpoint pairs (n : nat) : nat :=
    match n with
    | 0 => 0
    | S k => k + pairs k
    end.

  Lemma viol_with_bound :
    forall x ys, viol_with x ys <= length ys.
  Proof.
    intros x ys; induction ys as [| z r IH]; simpl.
    - apply le_n.
    - destruct (oracle z x); simpl.
      + apply le_S; exact IH.
      + apply le_n_S; exact IH.
  Qed.

  Lemma violations_bound :
    forall xs, violations xs <= pairs (length xs).
  Proof.
    induction xs as [| x xs IH]; simpl.
    - apply le_n.
    - apply nat_add_le_mono; [apply viol_with_bound | exact IH].
  Qed.

  (* T7d: C(n,2) repairs always suffice. *)
  Theorem swap_convergence_bound :
    forall xs, violations (learn (pairs (length xs)) xs) = 0.
  Proof.
    intro xs; apply learn_fuel; apply violations_bound.
  Qed.

  (* Semantics of zero violations: the ranking realizes the oracle on
     every ordered pair -- the homomorphism property at this state. *)

  Fixpoint Mem (a : Action) (xs : list Action) : Prop :=
    match xs with
    | nil => False
    | x :: xs' => x = a \/ Mem a xs'
    end.

  Fixpoint all_pairs_correct (xs : list Action) : Prop :=
    match xs with
    | nil => True
    | x :: xs' =>
        (forall y, Mem y xs' -> oracle y x = true) /\ all_pairs_correct xs'
    end.

  Lemma viol_with_zero_iff :
    forall x ys,
      viol_with x ys = 0 <-> (forall y, Mem y ys -> oracle y x = true).
  Proof.
    intros x ys; induction ys as [| z r IH]; simpl.
    - split; [intros _ y F; destruct F | intros _; reflexivity].
    - destruct (oracle z x) eqn:E; simpl.
      + split.
        * intros H0 y [Hzy | Hm]; [rewrite <- Hzy; exact E | apply IH; assumption].
        * intro Hall; apply IH; intros y Hm; apply Hall; right; exact Hm.
      + split.
        * intro H; discriminate H.
        * intro Hall; rewrite (Hall z (or_introl eq_refl)) in E; discriminate E.
  Qed.

  (* T7e: zero violations = full pairwise realization of the oracle. *)
  Theorem violations_zero_iff :
    forall xs, violations xs = 0 <-> all_pairs_correct xs.
  Proof.
    induction xs as [| x xs IH]; simpl.
    - split; [intros _; exact I | intros _; reflexivity].
    - split.
      + intro H.
        destruct (nat_add_eq_zero _ _ H) as [Hv Hr].
        split; [apply viol_with_zero_iff; exact Hv | apply IH; exact Hr].
      + intros [Hall Hrest].
        rewrite (proj2 (viol_with_zero_iff x xs) Hall); simpl.
        apply IH; exact Hrest.
  Qed.

  (* The headline corollary: the learner reaches a ranking that realizes
     the oracle on every pair, within C(n,2) repairs. *)
  Corollary learn_realizes_oracle :
    forall xs, all_pairs_correct (learn (pairs (length xs)) xs).
  Proof.
    intro xs.
    apply violations_zero_iff.
    apply swap_convergence_bound.
  Qed.

End Convergence.
