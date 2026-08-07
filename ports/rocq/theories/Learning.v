(* CSHRL portability kernel, Rocq port.
   T5: the learning kernel (paper section 14, Agda reference
   src/CSHRL/Learning/Base.agda).

   Explicit rankings are lists of actions, best first.  We port exactly the
   machine-checked lemmas of the Agda reference:

   - is_dominated_by is reflexive and total (the ranking is a total preorder);
   - swap_fixes_pair: after swapping a violated pair, the ranking agrees with
     the oracle on that pair (the repair is a transposition);
   - state_updater_locality: the state-specific updater touches only the
     violated state;
   - demote_preserves_dominance and its corollaries: demoting an action to
     the end preserves the dominance relation between all other pairs, so
     action unavailability is an O(1) adaptation (paper Remark 2).

   As in the Agda reference, the global violation-decrease statement
   (ViolationMonotonicityTheorem) is an assumption record, not a closed
   proof; it is therefore not part of the kernel. *)

Local Open Scope list_scope.

Section Learning.
  Variable State Action : Type.
  Variable eq_dec : forall a b : Action, {a = b} + {a <> b}.

  (* A ranking list per state, best action first. *)
  Definition ExplicitRanking : Type := State -> list Action.

  (* is_dominated_by xs a b = true means a <= b in the order given by xs
     (b appears no later than a; absent actions rank equal). *)
  Fixpoint is_dominated_by (xs : list Action) (a b : Action) : bool :=
    match xs with
    | nil => true
    | x :: xs' =>
        if eq_dec a x
        then (if eq_dec b x then true else false)
        else if eq_dec b x then true else is_dominated_by xs' a b
    end.

  (* D8 support: the induced order is reflexive and total. *)
  Lemma is_dominated_by_refl :
    forall xs a, is_dominated_by xs a a = true.
  Proof.
    induction xs as [| x xs IH]; intro a; simpl.
    - reflexivity.
    - destruct (eq_dec a x); [reflexivity | apply IH].
  Qed.

  Lemma dominated_total :
    forall xs a b,
      is_dominated_by xs a b = true \/ is_dominated_by xs b a = true.
  Proof.
    induction xs as [| x xs IH]; intros a b; simpl.
    - left; reflexivity.
    - destruct (eq_dec a x); destruct (eq_dec b x); auto.
  Qed.

  (* Skipping a head that is neither a nor b leaves dominance unchanged. *)
  Lemma is_dominated_by_skip :
    forall x a b xs,
      a <> x -> b <> x ->
      is_dominated_by (x :: xs) a b = is_dominated_by xs a b.
  Proof.
    intros x a b xs Hax Hbx; simpl.
    destruct (eq_dec a x); destruct (eq_dec b x);
      try contradiction; reflexivity.
  Qed.

  (* Appending one action c never changes the dominance of a pair (a, b)
     when neither a nor b equals c. *)
  Lemma dominated_snoc_irrelevant :
    forall c a b xs,
      a <> c -> b <> c ->
      is_dominated_by (xs ++ c :: nil) a b = is_dominated_by xs a b.
  Proof.
    intros c a b xs Hac Hbc; induction xs as [| x xs IH]; simpl.
    - destruct (eq_dec a c); try contradiction.
      destruct (eq_dec b c); try contradiction.
      reflexivity.
    - destruct (eq_dec a x); destruct (eq_dec b x); try reflexivity.
      exact IH.
  Qed.

  (**********************************************************************)
  (* Swap: the violation repair (a transposition).                       *)
  (**********************************************************************)

  Fixpoint remove_action (a : Action) (xs : list Action) : list Action :=
    match xs with
    | nil => nil
    | y :: ys => if eq_dec y a then ys else y :: remove_action a ys
    end.

  (* Put better immediately before worse at worse's old position. *)
  Fixpoint swap_in_list (better worse : Action) (xs : list Action)
    : list Action :=
    match xs with
    | nil => nil
    | x :: xs' =>
        if eq_dec x worse
        then better :: worse :: remove_action better xs'
        else x :: swap_in_list better worse xs'
    end.

  (* T5a: the swap fixes the violated pair (Agda: swap-fixes-pair). *)
  Theorem swap_fixes_pair :
    forall better worse xs,
      better <> worse ->
      is_dominated_by (swap_in_list better worse xs) worse better = true.
  Proof.
    intros better worse xs Hbw; induction xs as [| x xs IH]; simpl.
    - reflexivity.
    - destruct (eq_dec x worse) as [e | n]; simpl.
      + destruct (eq_dec worse better) as [e' | _].
        * exfalso; apply Hbw; symmetry; exact e'.
        * destruct (eq_dec better better) as [_ | n''];
            [reflexivity | exfalso; apply n''; reflexivity].
      + destruct (eq_dec worse x) as [e' | _].
        * exfalso; apply n; symmetry; exact e'.
        * destruct (eq_dec better x); [reflexivity | exact IH].
  Qed.

  (* T5b: the state-specific updater only modifies the violated state
     (Agda: state-updater-locality). *)
  Section StateSpecific.
    Variable st_eq_dec : forall s1 s2 : State, {s1 = s2} + {s1 <> s2}.

    Definition state_swap_updater
      (viol_state : State) (better worse : Action)
      (ranking : ExplicitRanking) : ExplicitRanking :=
      fun s =>
        if st_eq_dec s viol_state
        then swap_in_list better worse (ranking s)
        else ranking s.

    Lemma state_updater_locality :
      forall viol_state better worse ranking s,
        s <> viol_state ->
        state_swap_updater viol_state better worse ranking s = ranking s.
    Proof.
      intros vs better worse ranking s Hne; unfold state_swap_updater.
      destruct (st_eq_dec s vs); [contradiction | reflexivity].
    Qed.
  End StateSpecific.

  (**********************************************************************)
  (* Demotion: O(1) adaptation to action unavailability.                 *)
  (**********************************************************************)

  Fixpoint demote_to_end (target : Action) (xs : list Action)
    : list Action :=
    match xs with
    | nil => nil
    | x :: xs' =>
        if eq_dec x target
        then xs' ++ target :: nil
        else x :: demote_to_end target xs'
    end.

  (* T5c: demotion preserves the dominance relation between any two actions
     other than the demoted one (Agda: demote-preserves-dominance). *)
  Theorem demote_preserves_dominance :
    forall target a b xs,
      a <> target -> b <> target ->
      is_dominated_by (demote_to_end target xs) a b
      = is_dominated_by xs a b.
  Proof.
    intros target a b xs Hat Hbt; induction xs as [| x xs IH]; simpl.
    - reflexivity.
    - destruct (eq_dec x target) as [e | n].
      + subst x.
        rewrite dominated_snoc_irrelevant by assumption.
        destruct (eq_dec a target); try contradiction.
        destruct (eq_dec b target); try contradiction.
        reflexivity.
      + simpl.
        destruct (eq_dec a x); destruct (eq_dec b x); try reflexivity.
        exact IH.
  Qed.

  (* Corollary: if the ranking realizes a target relation on a pair of
     non-demoted actions, the demoted ranking realizes the same relation
     (Agda: demote-preserves-homomorphism). *)
  Corollary demote_preserves_homomorphism :
    forall target a b xs (Rel : Action -> Action -> bool),
      a <> target -> b <> target ->
      is_dominated_by xs a b = Rel a b ->
      is_dominated_by (demote_to_end target xs) a b = Rel a b.
  Proof.
    intros target a b xs Rel Hat Hbt Heq.
    rewrite demote_preserves_dominance by assumption.
    exact Heq.
  Qed.

  (* The public runtime API inherits the result pointwise at every state
     (Agda: make-action-unavailable-preserves-dominance). *)
  Definition make_action_unavailable
    (forbidden : Action) (ranking : ExplicitRanking) : ExplicitRanking :=
    fun s => demote_to_end forbidden (ranking s).

  Corollary make_action_unavailable_preserves_dominance :
    forall forbidden a b (ranking : ExplicitRanking) s,
      a <> forbidden -> b <> forbidden ->
      is_dominated_by (make_action_unavailable forbidden ranking s) a b
      = is_dominated_by (ranking s) a b.
  Proof.
    intros forbidden a b ranking s Haf Hbf.
    apply demote_preserves_dominance; assumption.
  Qed.

End Learning.
