(* CSHRL portability kernel, Rocq port.
   D17, T13: the combinatorial placement environment class and its trace
   bridge.

   Ports the CombinatorialPlacementMDP environment class from the Agda
   reference implementation: constraint-satisfaction placement games
   (N-Queens, Sudoku, graph coloring) with absorbing Dead/Solved states and
   sparse binary rewards.

   The main theorem (T13, placement_coindhomo) is the trace bridge: the
   computable lexicographic ranking of finite reward traces forms a
   CoindHomo -- it preserves dominance of the full (coinductive)
   action-value streams.  The proof goes through the binary structure of
   solve (every value is 0 or R) and its monotonicity, which together turn
   lexicographic trace comparison into pointwise comparison; the coinductive
   statement is recovered through the stream isomorphism (T1).

   As in the Lean port, horizon sufficiency is discharged generically for
   sized games (placement increases a size measure by one and solving means
   exactly reaching the horizon), so concrete instances (Sudoku.v) get the
   CoindHomo with no proof obligations beyond their static description. *)

From Stdlib Require Import List Arith Lia Bool.
Import ListNotations.
From CSHRL Require Import Streams Core.

(* Stream of the values of a function, for building value streams. *)
CoFixpoint tabulate (f : nat -> nat) : stream nat :=
  Cons (f 0) (tabulate (fun n => f (S n))).

Lemma nth_tabulate : forall n f, nth n (tabulate f) = f n.
Proof.
  induction n as [|n IH]; intros f; simpl.
  - reflexivity.
  - apply IH.
Qed.

(* States of a placement game. *)
Inductive pstate (Config : Type) : Type :=
| Ongoing : Config -> pstate Config
| PDead : pstate Config
| PSolved : Config -> pstate Config.

Arguments Ongoing {Config} c.
Arguments PDead {Config}.
Arguments PSolved {Config} c.

Section Placement.
  Variable Config Action : Type.
  Variable is_dead is_solved : Config -> bool.
  Variable place : Config -> Action -> Config.
  Variable Rw : nat.
  Hypothesis Rpos : 0 < Rw.
  Variable actions : list Action.
  Hypothesis actions_ne : actions <> nil.
  Variable horizon : nat.

  (* One step of the placement MDP: Dead and Solved are absorbing. *)
  Definition step (s : pstate Config) (a : Action) : pstate Config * nat :=
    match s with
    | PDead => (PDead, 0)
    | PSolved c => (PSolved c, Rw)
    | Ongoing c =>
        let c' := place c a in
        if is_dead c' then (PDead, 0)
        else if is_solved c' then (PSolved c', Rw)
        else (Ongoing c', 0)
    end.

  Fixpoint max_list (l : list nat) : nat :=
    match l with
    | nil => 0
    | x :: xs => Nat.max x (max_list xs)
    end.

  (* Finite-horizon optimal value (the n-step Bellman backup). *)
  Fixpoint solve (s : pstate Config) (n : nat) {struct n} : nat :=
    match n with
    | 0 => max_list (map (fun a => snd (step s a)) actions)
    | S n' => max_list (map (fun a => solve (fst (step s a)) n') actions)
    end.

  Definition pnext (s : pstate Config) (a : Action) : pstate Config :=
    fst (step s a).

  Definition preward (s : pstate Config) (a : Action) : nat :=
    snd (step s a).

  Definition pvalue (s : pstate Config) : stream nat := tabulate (solve s).

  (* ------------------------------------------------------------------ *)
  (* max_list toolkit                                                    *)
  (* ------------------------------------------------------------------ *)

  Lemma max_list_all_zero :
    forall (A : Type) (f : A -> nat) (l : list A),
      (forall x, In x l -> f x = 0) -> max_list (map f l) = 0.
  Proof.
    intros A f l; induction l as [|x xs IH]; intros H; simpl.
    - reflexivity.
    - rewrite (H x (or_introl eq_refl)), IH; [lia | intros y Hy; apply H; right; exact Hy].
  Qed.

  Lemma max_list_all_R :
    forall (A : Type) (f : A -> nat) (l : list A),
      l <> nil -> (forall x, In x l -> f x = Rw) -> max_list (map f l) = Rw.
  Proof.
    intros A f l; induction l as [|x xs IH]; intros Hne H; simpl.
    - contradiction Hne; reflexivity.
    - rewrite (H x (or_introl eq_refl)).
      destruct xs as [|y ys].
      + simpl; lia.
      + rewrite IH; [lia | discriminate | intros z Hz; apply H; right; exact Hz].
  Qed.

  Lemma max_list_binary :
    forall (A : Type) (f : A -> nat) (l : list A),
      (forall x, In x l -> f x = 0 \/ f x = Rw) ->
      max_list (map f l) = 0 \/ max_list (map f l) = Rw.
  Proof.
    intros A f l; induction l as [|x xs IH]; intros H; simpl.
    - left; reflexivity.
    - destruct (H x (or_introl eq_refl)) as [Hx | Hx];
      destruct (IH (fun y Hy => H y (or_intror Hy))) as [Hxs | Hxs]; lia.
  Qed.

  Lemma max_list_le :
    forall (A : Type) (f : A -> nat) (l : list A) (B : nat),
      (forall x, In x l -> f x <= B) -> max_list (map f l) <= B.
  Proof.
    intros A f l B; induction l as [|x xs IH]; intros H; simpl.
    - lia.
    - specialize (IH (fun y Hy => H y (or_intror Hy))).
      specialize (H x (or_introl eq_refl)); lia.
  Qed.

  Lemma max_list_mem_R :
    forall (A : Type) (f : A -> nat) (l : list A) (x : A),
      In x l -> f x = Rw -> (forall y, In y l -> f y <= Rw) ->
      max_list (map f l) = Rw.
  Proof.
    intros A f l; induction l as [|z zs IH]; intros x Hx Hfx Hle; simpl.
    - contradiction Hx.
    - destruct Hx as [Heq | Hin].
      + subst z.
        pose proof (max_list_le _ f zs Rw (fun y Hy => Hle y (or_intror Hy))).
        lia.
      + rewrite (IH x Hin Hfx (fun y Hy => Hle y (or_intror Hy))).
        specialize (Hle z (or_introl eq_refl)); lia.
  Qed.

  Lemma max_list_R_exists :
    forall (A : Type) (f : A -> nat) (l : list A),
      max_list (map f l) = Rw -> exists x, In x l /\ f x = Rw.
  Proof.
    intros A f l; induction l as [|x xs IH]; intros H; simpl in H.
    - lia.
    - destruct (Nat.eq_dec (f x) Rw) as [Hx | Hx].
      + exists x; split; [left; reflexivity | exact Hx].
      + assert (Hxs : max_list (map f xs) = Rw) by lia.
        destruct (IH Hxs) as [y [Hy Hfy]].
        exists y; split; [right; exact Hy | exact Hfy].
  Qed.

  Lemma max_list_congr :
    forall (A : Type) (f g : A -> nat) (l : list A),
      (forall x, In x l -> f x = g x) ->
      max_list (map f l) = max_list (map g l).
  Proof.
    intros A f g l; induction l as [|x xs IH]; intros H; simpl.
    - reflexivity.
    - rewrite (H x (or_introl eq_refl)), IH;
        [reflexivity | intros y Hy; apply H; right; exact Hy].
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Absorbing states and the binary structure of solve                  *)
  (* ------------------------------------------------------------------ *)

  Lemma solve_dead : forall n, solve PDead n = 0.
  Proof.
    induction n as [|n IH]; simpl.
    - apply max_list_all_zero; intros a _; reflexivity.
    - apply max_list_all_zero; intros a _; exact IH.
  Qed.

  Lemma solve_solved : forall c n, solve (PSolved c) n = Rw.
  Proof.
    intros c n; revert c; induction n as [|n IH]; intros c; simpl.
    - apply max_list_all_R; [exact actions_ne | intros a _; reflexivity].
    - apply max_list_all_R; [exact actions_ne | intros a _; apply IH].
  Qed.

  Lemma reward_binary :
    forall s a, snd (step s a) = 0 \/ snd (step s a) = Rw.
  Proof.
    intros s a; destruct s as [c | | c]; simpl.
    - destruct (is_dead (place c a)); simpl.
      + left; reflexivity.
      + destruct (is_solved (place c a)); simpl; [right | left]; reflexivity.
    - left; reflexivity.
    - right; reflexivity.
  Qed.

  Lemma solve_binary :
    forall n s, solve s n = 0 \/ solve s n = Rw.
  Proof.
    induction n as [|n IH]; intros s; simpl.
    - apply max_list_binary; intros a _; apply reward_binary.
    - apply max_list_binary; intros a _; apply IH.
  Qed.

  Lemma solve_le_R : forall s n, solve s n <= Rw.
  Proof.
    intros s n; destruct (solve_binary n s); lia.
  Qed.

  (* If the immediate reward is R, the successor's 0-step value is R. *)
  Lemma step_R_solve0 :
    forall s a, snd (step s a) = Rw -> solve (fst (step s a)) 0 = Rw.
  Proof.
    intros s a H; destruct s as [c | | c]; simpl in *.
    - destruct (is_dead (place c a)); simpl in *.
      + lia.
      + destruct (is_solved (place c a)); simpl in *.
        * exact (solve_solved (place c a) 0).
        * lia.
    - lia.
    - exact (solve_solved c 0).
  Qed.

  Lemma solve_mono :
    forall n s, solve s n = Rw -> solve s (S n) = Rw.
  Proof.
    induction n as [|n IH]; intros s H; simpl in *.
    - destruct (max_list_R_exists _ _ _ H) as [a [Ha Hfa]].
      apply (max_list_mem_R _ _ _ a Ha).
      + apply step_R_solve0; exact Hfa.
      + intros b _; exact (solve_le_R (fst (step s b)) 0).
    - destruct (max_list_R_exists _ _ _ H) as [a [Ha Hfa]].
      apply (max_list_mem_R _ _ _ a Ha).
      + apply IH; exact Hfa.
      + intros b _; exact (solve_le_R (fst (step s b)) (S n)).
  Qed.

  Lemma solve_R_le :
    forall s m n, m <= n -> solve s m = Rw -> solve s n = Rw.
  Proof.
    intros s m n; revert m; induction n as [|n IH]; intros m Hmn H.
    - assert (m = 0) by lia; subst; exact H.
    - destruct (Nat.eq_dec m (S n)) as [He | He].
      + subst; exact H.
      + apply solve_mono; apply (IH m); [lia | exact H].
  Qed.

  Lemma solve_zero_le :
    forall s m n, m <= n -> solve s n = 0 -> solve s m = 0.
  Proof.
    intros s m n Hmn H.
    destruct (solve_binary m s) as [H0 | HR].
    - exact H0.
    - pose proof (solve_R_le s m n Hmn HR); lia.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Traces and the lexicographic comparison                             *)
  (* ------------------------------------------------------------------ *)

  Fixpoint lex_le (u v : list nat) : bool :=
    match u, v with
    | nil, _ => true
    | _ :: _, nil => false
    | x :: xs, y :: ys =>
        if x <? y then true
        else if y <? x then false
        else lex_le xs ys
    end.

  Lemma lex_le_total :
    forall u v, lex_le u v = false -> lex_le v u = true.
  Proof.
    induction u as [|x xs IH]; intros v H; simpl in H.
    - discriminate.
    - destruct v as [|y ys]; simpl.
      + reflexivity.
      + destruct (x <? y) eqn:Hxy; [discriminate |].
        destruct (y <? x) eqn:Hyx.
        * reflexivity.
        * apply IH; exact H.
  Qed.

  (* Trace entries are 0 or R up to index j. *)
  Definition bin_to (t : list nat) (j : nat) : Prop :=
    forall i, i <= j -> List.nth i t 0 = 0 \/ List.nth i t 0 = Rw.

  (* Once a trace entry is R it stays R, up to index j. *)
  Definition mono_to (t : list nat) (j : nat) : Prop :=
    forall i, S i <= j -> List.nth i t 0 = Rw -> List.nth (S i) t 0 = Rw.

  Lemma all_R_from_head :
    forall t j, List.nth 0 t 0 = Rw -> mono_to t j ->
    forall i, i <= j -> List.nth i t 0 = Rw.
  Proof.
    intros t j Hh Hm; induction i as [|i IH]; intros Hij.
    - exact Hh.
    - apply Hm; [lia | apply IH; lia].
  Qed.

  (* The heart of the bridge: for binary monotone traces, lexicographic
     comparison implies pointwise comparison. *)
  Lemma lex_pointwise :
    forall u v j, lex_le u v = true ->
    bin_to u j -> bin_to v j -> mono_to u j -> mono_to v j ->
    List.nth j u 0 <= List.nth j v 0.
  Proof.
    induction u as [|x xs IH]; intros v j Hlex Hbu Hbv Hmu Hmv.
    - destruct j; simpl; lia.
    - destruct v as [|y ys]; simpl in Hlex; [discriminate |].
      destruct (x <? y) eqn:Hxy.
      + (* heads differ: x = 0, y = R; monotonicity forces v to be R at j *)
        apply Nat.ltb_lt in Hxy.
        pose proof (Hbu 0 (Nat.le_0_l _)) as Hx0; simpl in Hx0.
        pose proof (Hbv 0 (Nat.le_0_l _)) as Hy0; simpl in Hy0.
        assert (HyR : y = Rw) by lia.
        assert (Hvj : List.nth j (y :: ys) 0 = Rw).
        { apply (all_R_from_head (y :: ys) j); [simpl; exact HyR | exact Hmv | lia]. }
        pose proof (Hbu j (Nat.le_refl _)).
        lia.
      + destruct (y <? x) eqn:Hyx; [discriminate |].
        apply Nat.ltb_ge in Hxy; apply Nat.ltb_ge in Hyx.
        destruct j as [|j]; simpl.
        * lia.
        * apply IH; clear IH.
          -- exact Hlex.
          -- intros i Hi; exact (Hbu (S i) ltac:(lia)).
          -- intros i Hi; exact (Hbv (S i) ltac:(lia)).
          -- intros i Hi Hr; exact (Hmu (S i) ltac:(lia) Hr).
          -- intros i Hi Hr; exact (Hmv (S i) ltac:(lia) Hr).
  Qed.

  (* ------------------------------------------------------------------ *)
  (* The lexicographic maximum trace                                     *)
  (* ------------------------------------------------------------------ *)

  Fixpoint max_trace_aux (t : list nat) (ts : list (list nat)) : list nat :=
    match ts with
    | nil => t
    | u :: us => if lex_le t u then max_trace_aux u us else max_trace_aux t us
    end.

  Definition max_trace (ts : list (list nat)) : list nat :=
    match ts with
    | nil => nil
    | t :: ts' => max_trace_aux t ts'
    end.

  (* For binary monotone traces, the lex maximum achieves the pointwise
     maximum at every position. *)
  Lemma max_trace_aux_nth :
    forall ts t j,
      bin_to t j -> mono_to t j ->
      (forall u, In u ts -> bin_to u j /\ mono_to u j) ->
      List.nth j (max_trace_aux t ts) 0 =
        Nat.max (List.nth j t 0) (max_list (map (fun u => List.nth j u 0) ts)).
  Proof.
    induction ts as [|u us IH]; intros t j Hbt Hmt Hall; simpl.
    - lia.
    - destruct (Hall u (or_introl eq_refl)) as [Hbu Hmu].
      assert (Hus : forall w, In w us -> bin_to w j /\ mono_to w j)
        by (intros w Hw; apply Hall; right; exact Hw).
      destruct (lex_le t u) eqn:Hlex.
      + pose proof (lex_pointwise t u j Hlex Hbt Hbu Hmt Hmu).
        rewrite (IH u j Hbu Hmu Hus); lia.
      + pose proof (lex_le_total t u Hlex) as Hlex'.
        pose proof (lex_pointwise u t j Hlex' Hbu Hbt Hmu Hmt).
        rewrite (IH t j Hbt Hmt Hus); lia.
  Qed.

  Lemma max_trace_nth :
    forall ts j,
      (forall u, In u ts -> bin_to u j /\ mono_to u j) ->
      List.nth j (max_trace ts) 0 = max_list (map (fun u => List.nth j u 0) ts).
  Proof.
    intros ts j Hall; destruct ts as [|t ts']; simpl.
    - destruct j; reflexivity.
    - destruct (Hall t (or_introl eq_refl)) as [Hbt Hmt].
      apply (max_trace_aux_nth ts' t j Hbt Hmt).
      intros u Hu; apply Hall; right; exact Hu.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Best traces (the Finder's scoring function)                         *)
  (* ------------------------------------------------------------------ *)

  (* Best k-step reward trace from a state, with absorbing short-circuits. *)
  Fixpoint best_trace (s : pstate Config) (k : nat) {struct k} : list nat :=
    match k with
    | 0 => nil
    | S k' =>
        match s with
        | PDead => 0 :: repeat 0 k'
        | PSolved _ => Rw :: repeat Rw k'
        | Ongoing c =>
            max_trace (map (fun a =>
              snd (step (Ongoing c) a) :: best_trace (fst (step (Ongoing c) a)) k')
              actions)
        end
    end.

  (* The trace of taking action a: immediate reward, then the best trace. *)
  Definition trace_action (s : pstate Config) (a : Action) (k : nat) : list nat :=
    snd (step s a) :: best_trace (fst (step s a)) k.

  Lemma nth_repeat_zero : forall k i, List.nth i (repeat 0 k) 0 = 0.
  Proof.
    induction k as [|k IH]; intros i; destruct i; simpl; auto.
  Qed.

  Lemma nth_repeat_lt : forall (x : nat) k i, i < k -> List.nth i (repeat x k) 0 = x.
  Proof.
    induction k as [|k IH]; intros i Hi.
    - lia.
    - destruct i; simpl; [reflexivity | apply IH; lia].
  Qed.

  (* THE KEY LEMMA: the i-th entry of the best (k+1)-step trace is the
     i-step optimal value, for i <= k. *)
  Lemma best_trace_is_solve :
    forall k s i, i <= k -> List.nth i (best_trace s (S k)) 0 = solve s i.
  Proof.
    induction k as [|k IH]; intros s i Hi.
    - assert (i = 0) by lia; subst i.
      destruct s as [c | | c].
      + (* Ongoing at depth 1 *)
        cbn [best_trace].
        rewrite (max_trace_nth _ 0).
        * rewrite map_map.
          cbn [solve].
          apply max_list_congr; intros a _; reflexivity.
        * intros u Hu; apply in_map_iff in Hu; destruct Hu as [a [Ha _]]; subst u.
          split.
          -- intros i Hi0; assert (i = 0) by lia; subst i.
             exact (reward_binary (Ongoing c) a).
          -- intros i Hi0; exfalso; lia.
      + rewrite (solve_dead 0); reflexivity.
      + rewrite (solve_solved c 0); reflexivity.
    - destruct s as [c | | c].
      + (* Ongoing: use the binary/monotone structure of the action traces *)
        assert (Hbin : forall a, bin_to
          (snd (step (Ongoing c) a) :: best_trace (fst (step (Ongoing c) a)) (S k)) i).
        { intros a i' Hi'.
          destruct i' as [|i'].
          - exact (reward_binary (Ongoing c) a).
          - cbn [List.nth].
            rewrite (IH (fst (step (Ongoing c) a)) i' ltac:(lia)).
            exact (solve_binary i' _). }
        assert (Hmono : forall a, mono_to
          (snd (step (Ongoing c) a) :: best_trace (fst (step (Ongoing c) a)) (S k)) i).
        { intros a i' Hi' HR.
          destruct i' as [|i'].
          - cbn [List.nth] in HR |- *.
            rewrite (IH (fst (step (Ongoing c) a)) 0 ltac:(lia)).
            exact (step_R_solve0 (Ongoing c) a HR).
          - cbn [List.nth] in HR |- *.
            rewrite (IH (fst (step (Ongoing c) a)) i' ltac:(lia)) in HR.
            rewrite (IH (fst (step (Ongoing c) a)) (S i') ltac:(lia)).
            exact (solve_mono i' _ HR). }
        cbn [best_trace].
        rewrite (max_trace_nth _ i).
        * rewrite map_map.
          destruct i as [|i].
          -- cbn [solve List.nth].
             apply max_list_congr; intros a _; reflexivity.
          -- cbn [solve List.nth].
             apply max_list_congr; intros a _.
             exact (IH (fst (step (Ongoing c) a)) i ltac:(lia)).
        * intros u Hu; apply in_map_iff in Hu; destruct Hu as [a [Ha _]]; subst u.
          exact (conj (Hbin a) (Hmono a)).
      + (* Dead *)
        destruct i as [|i].
        * rewrite (solve_dead 0); reflexivity.
        * cbn [best_trace List.nth].
          rewrite nth_repeat_zero, (solve_dead (S i)); reflexivity.
      + (* Solved *)
        destruct i as [|i].
        * rewrite (solve_solved c 0); reflexivity.
        * cbn [best_trace List.nth].
          rewrite (nth_repeat_lt Rw (S k) i ltac:(lia)), (solve_solved c (S i)).
          reflexivity.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* The Finder's ranking and the trace bridge                           *)
  (* ------------------------------------------------------------------ *)

  (* D18: the Finder's ranking -- lexicographic comparison of reward traces
     explored to depth horizon+1. *)
  Definition ranks (s : pstate Config) (a b : Action) : Prop :=
    lex_le (trace_action s a (S horizon)) (trace_action s b (S horizon)) = true.

  Lemma trace_action_bin :
    forall s a k, bin_to (trace_action s a (S k)) (S k).
  Proof.
    intros s a k i Hi; destruct i as [|i]; unfold trace_action.
    - exact (reward_binary s a).
    - cbn [List.nth].
      rewrite (best_trace_is_solve k _ i ltac:(lia)); exact (solve_binary i _).
  Qed.

  Lemma trace_action_mono :
    forall s a k, mono_to (trace_action s a (S k)) (S k).
  Proof.
    intros s a k i Hi HR; destruct i as [|i]; unfold trace_action in *;
      cbn [List.nth] in HR |- *.
    - rewrite (best_trace_is_solve k _ 0 ltac:(lia)).
      exact (step_R_solve0 s a HR).
    - rewrite (best_trace_is_solve k _ i ltac:(lia)) in HR.
      rewrite (best_trace_is_solve k _ (S i) ltac:(lia)).
      exact (solve_mono i _ HR).
  Qed.

  (* Within the horizon: trace ordering gives pointwise solve ordering. *)
  Lemma trace_to_solve_at :
    forall s a b n, n <= horizon -> ranks s a b ->
    solve (fst (step s a)) n <= solve (fst (step s b)) n.
  Proof.
    intros s a b n Hn Hab.
    pose proof (lex_pointwise
      (trace_action s a (S horizon)) (trace_action s b (S horizon)) (S n)
      Hab
      (fun i Hi => trace_action_bin s a horizon i ltac:(lia))
      (fun i Hi => trace_action_bin s b horizon i ltac:(lia))
      (fun i Hi => trace_action_mono s a horizon i ltac:(lia))
      (fun i Hi => trace_action_mono s b horizon i ltac:(lia))) as Hpt.
    unfold trace_action in Hpt; cbn [List.nth] in Hpt.
    rewrite (best_trace_is_solve horizon _ n Hn) in Hpt.
    rewrite (best_trace_is_solve horizon _ n Hn) in Hpt.
    exact Hpt.
  Qed.

  (* Horizon sufficiency: the domain-specific termination property. *)
  Definition horizon_suf : Prop :=
    forall c, solve (Ongoing c) horizon = 0 -> forall n, solve (Ongoing c) n = 0.

  (* Above the horizon: solve is determined by its value at the horizon. *)
  Lemma trace_to_solve_above :
    horizon_suf ->
    forall s a b n, horizon < n -> ranks s a b ->
    solve (fst (step s a)) n <= solve (fst (step s b)) n.
  Proof.
    intros Hsuf s a b n Hn Hab.
    pose proof (trace_to_solve_at s a b horizon (Nat.le_refl _) Hab) as HH.
    destruct (solve_binary n (fst (step s a))) as [H0 | HRn].
    - lia.
    - (* solve at n is R; show solve at horizon is R too *)
      assert (HaH : solve (fst (step s a)) horizon = Rw).
      { destruct (solve_binary horizon (fst (step s a))) as [H0 | HRH].
        - exfalso.
          destruct (fst (step s a)) as [c | | c] eqn:Hsa.
          + rewrite (Hsuf c H0 n) in HRn; lia.
          + rewrite (solve_dead n) in HRn; lia.
          + rewrite (solve_solved c horizon) in H0; lia.
        - exact HRH. }
      assert (HbH : solve (fst (step s b)) horizon = Rw).
      { pose proof (solve_le_R (fst (step s b)) horizon); lia. }
      assert (Hbn : solve (fst (step s b)) n = Rw).
      { destruct (fst (step s b)) as [c | | c] eqn:Hsb.
        - apply (solve_R_le _ horizon n ltac:(lia) HbH).
        - rewrite (solve_dead horizon) in HbH; lia.
        - apply (solve_solved c n). }
      lia.
  Qed.

  (* T13: THE TRACE BRIDGE.  The Finder's lexicographic trace ranking is a
     CoindHomo: it preserves dominance of the full coinductive action-value
     streams, at every state of any placement game with the
     horizon-sufficiency property. *)
  Theorem placement_coindhomo :
    horizon_suf ->
    forall s, CoindHomo nat le (pstate Config) Action pnext preward pvalue ranks s.
  Proof.
    intros Hsuf s a b Hab.
    apply pointwise_stream_le; intro n.
    destruct n as [|n]; simpl.
    - (* head: immediate rewards, index 0 of the traces *)
      pose proof (lex_pointwise
        (trace_action s a (S horizon)) (trace_action s b (S horizon)) 0
        Hab
        (fun i Hi => trace_action_bin s a horizon i ltac:(lia))
        (fun i Hi => trace_action_bin s b horizon i ltac:(lia))
        (fun i Hi => trace_action_mono s a horizon i ltac:(lia))
        (fun i Hi => trace_action_mono s b horizon i ltac:(lia))) as Hpt.
      exact Hpt.
    - (* tail: value streams of the successors *)
      unfold pvalue; rewrite 2!nth_tabulate.
      destruct (Nat.le_gt_cases n horizon) as [Hle | Hgt].
      + apply trace_to_solve_at; assumption.
      + apply trace_to_solve_above; assumption.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Sized games: horizon sufficiency for free                           *)
  (* ------------------------------------------------------------------ *)

  Variable size : Config -> nat.
  Hypothesis place_size : forall c a, size (place c a) = S (size c).
  Hypothesis solved_iff : forall c, is_solved c = (size c =? horizon).

  Lemma sized_not_solved :
    forall c a, horizon <= size c -> is_solved (place c a) = false.
  Proof.
    intros c a Hc; rewrite solved_iff, place_size.
    apply Nat.eqb_neq; lia.
  Qed.

  (* When the size budget is exhausted, solve is identically 0. *)
  Lemma sized_solve0 :
    forall n c, horizon <= size c -> solve (Ongoing c) n = 0.
  Proof.
    induction n as [|n IH]; intros c Hc; simpl;
      apply max_list_all_zero; intros a _.
    - destruct (is_dead (place c a)) eqn:Hd; simpl; rewrite ?Hd; simpl.
      + reflexivity.
      + rewrite (sized_not_solved c a Hc); reflexivity.
    - destruct (is_dead (place c a)) eqn:Hd; simpl; rewrite ?Hd; simpl.
      + apply solve_dead.
      + rewrite (sized_not_solved c a Hc); simpl.
        apply IH; rewrite place_size; lia.
  Qed.

  (* If solve is 0 at depth m+1, each successor's solve is 0 at depth m. *)
  Lemma solve_component_zero :
    forall s m, solve s (S m) = 0 ->
    forall a, In a actions -> solve (fst (step s a)) m = 0.
  Proof.
    intros s m H a Ha.
    destruct (solve_binary m (fst (step s a))) as [H0 | HR].
    - exact H0.
    - exfalso.
      assert (Hmax : max_list (map (fun a' => solve (fst (step s a')) m) actions) = Rw).
      { apply (max_list_mem_R _ _ _ a Ha HR).
        intros b _; apply solve_le_R. }
      simpl in H; lia.
  Qed.

  (* Fuel induction: solve 0 at the remaining-budget depth forces solve 0
     at every depth. *)
  Lemma sized_shs :
    forall fuel c, fuel = horizon - size c ->
    solve (Ongoing c) fuel = 0 ->
    forall n, solve (Ongoing c) n = 0.
  Proof.
    induction fuel as [|fuel IH]; intros c Hf Hq n.
    - apply sized_solve0; lia.
    - pose proof (solve_component_zero (Ongoing c) fuel Hq) as Hcomp.
      destruct n as [|n].
      + apply (solve_zero_le (Ongoing c) 0 (S fuel)); [lia | exact Hq].
      + simpl; apply max_list_all_zero; intros a Ha.
        specialize (Hcomp a Ha).
        simpl in Hcomp |- *.
        destruct (is_dead (place c a)) eqn:Hd; simpl in Hcomp |- *.
        * apply solve_dead.
        * destruct (is_solved (place c a)) eqn:Hs; simpl in Hcomp |- *.
          -- rewrite (solve_solved (place c a) fuel) in Hcomp; lia.
          -- apply (IH (place c a)); [rewrite place_size; lia | exact Hcomp].
  Qed.

  (* Sized games satisfy horizon sufficiency with no extra obligations. *)
  Lemma sized_horizon_suf : horizon_suf.
  Proof.
    intros c H n.
    apply (sized_shs (horizon - size c) c eq_refl).
    apply (solve_zero_le (Ongoing c) (horizon - size c) horizon); [lia | exact H].
  Qed.

  (* T13 for sized games. *)
  Theorem sized_coindhomo :
    forall s, CoindHomo nat le (pstate Config) Action pnext preward pvalue ranks s.
  Proof.
    apply placement_coindhomo; exact sized_horizon_suf.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* The Finder's policy (executable)                                    *)
  (* ------------------------------------------------------------------ *)

  (* Pick the lex-greatest action trace (first maximum wins). *)
  Definition find_policy (s : pstate Config) (k : nat) : option Action :=
    match actions with
    | nil => None
    | a :: rest =>
        Some (fold_left (fun best x =>
          if lex_le (trace_action s best k) (trace_action s x k) then x else best)
          rest a)
    end.

  Fixpoint run_policy (s : pstate Config) (depth n : nat) {struct n} : list Action :=
    match n with
    | 0 => nil
    | S n' =>
        match find_policy s depth with
        | None => nil
        | Some a => a :: run_policy (fst (step s a)) depth n'
        end
    end.

End Placement.
