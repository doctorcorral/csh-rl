(* CSHRL portability kernel, Rocq port.
   T10: FOSD and SD[k] are closed under convolution (independent sum),
   the composition law for product MDPs with additive rewards (Agda
   reference src/CSHRL/Probability/Convolution.agda).

   Proof structure (discrete Abel summation):
   1. the CDF of a convolution decomposes as a generalized weighted sum
      (gws) over the first distribution, of shifted CDFs of the second;
   2. kernel direction: gws is monotone in the summand (gws_mono);
   3. base direction: FOSD implies gws dominance for every non-increasing
      eventually-zero summand, by induction on the support bound
      (gws_split peels off the last level: Abel's identity);
   4. FOSD_conv chains both directions; FOSD_SD_conv lifts the result to
      the whole hierarchy. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
From CSHRL Require Import Dist SDHierarchy.

(* Convolution: independent sum of two distributions. *)
Definition conv (d1 d2 : Dist nat) : Dist nat :=
  dbind d1 (fun v => dmap (fun u => v + u) d2).

(* Generalized weighted sum: sum over (v, w) in d of w * h v. *)
Fixpoint gws (d : Dist nat) (h : nat -> nat) : nat :=
  match d with
  | [] => 0
  | (v, w) :: rest => w * h v + gws rest h
  end.

(* The CDF of a convolution decomposes as a gws of shifted CDFs. *)
Lemma cdf_conv :
  forall (d1 d2 : Dist nat) r,
    cdf_weight (conv d1 d2) r
    = gws d1 (fun v => cdf_weight (dmap (fun u => v + u) d2) r).
Proof.
  induction d1 as [| [v w] d1 IH]; intros d2 r.
  - reflexivity.
  - unfold conv in *; simpl.
    rewrite cdf_weight_app, cdf_weight_scale, IH.
    reflexivity.
Qed.

(* Kernel direction: gws is monotone in the summand. *)
Lemma gws_mono :
  forall (d : Dist nat) (h1 h2 : nat -> nat),
    (forall v, h1 v <= h2 v) -> gws d h1 <= gws d h2.
Proof.
  induction d as [| [v w] d IH]; intros h1 h2 H; simpl.
  - lia.
  - specialize (IH h1 h2 H); specialize (H v); nia.
Qed.

(* Shifted CDFs. *)
Lemma cdf_dmap_add :
  forall k (d : Dist nat) r,
    k <= r ->
    cdf_weight (dmap (fun u => k + u) d) r = cdf_weight d (r - k).
Proof.
  intros k d r Hkr; induction d as [| [u w] d IH]; simpl.
  - reflexivity.
  - rewrite IH.
    destruct (k + u <=? r) eqn:E1; destruct (u <=? r - k) eqn:E2;
      try reflexivity.
    + apply Nat.leb_le in E1; apply Nat.leb_gt in E2; lia.
    + apply Nat.leb_gt in E1; apply Nat.leb_le in E2; lia.
Qed.

Lemma cdf_dmap_zero :
  forall k (d : Dist nat) r,
    r < k -> cdf_weight (dmap (fun u => k + u) d) r = 0.
Proof.
  intros k d r Hrk; induction d as [| [u w] d IH]; simpl.
  - reflexivity.
  - destruct (k + u <=? r) eqn:E.
    + apply Nat.leb_le in E; lia.
    + rewrite IH; reflexivity.
Qed.

(* FOSD is preserved by shifting. *)
Lemma FOSD_shift :
  forall k mu nu,
    FOSD_le mu nu ->
    FOSD_le (dmap (fun u => k + u) mu) (dmap (fun u => k + u) nu).
Proof.
  intros k mu nu H r.
  destruct (le_dec k r) as [Hkr | Hkr].
  - rewrite !cdf_dmap_add by assumption; apply H.
  - rewrite !cdf_dmap_zero by lia; lia.
Qed.

(* The shifted CDF is non-increasing in the shift and eventually zero. *)
Lemma shift_cdf_mono :
  forall (d : Dist nat) v r,
    cdf_weight (dmap (fun u => S v + u) d) r
    <= cdf_weight (dmap (fun u => v + u) d) r.
Proof.
  induction d as [| [u w] d IH]; intros v r.
  - simpl; lia.
  - specialize (IH v r).
    rewrite !dmap_cons, !cdf_weight_cons; cbv beta.
    destruct (Nat.leb_spec (S v + u) r); destruct (Nat.leb_spec (v + u) r); lia.
Qed.

Lemma shift_cdf_zero :
  forall (d : Dist nat) r,
    cdf_weight (dmap (fun u => S r + u) d) r = 0.
Proof.
  intros d r; apply cdf_dmap_zero; lia.
Qed.

(* Non-increasing summands vanish beyond their support bound. *)
Lemma h_vanish :
  forall (h : nat -> nat),
    (forall v, h (S v) <= h v) ->
    forall M, h M = 0 -> forall n, h (n + M) = 0.
Proof.
  intros h mono M h0 n; induction n as [| n IH]; simpl.
  - exact h0.
  - specialize (mono (n + M)); lia.
Qed.

Lemma mono_chain :
  forall (h : nat -> nat),
    (forall v, h (S v) <= h v) ->
    forall m n, h (m + n) <= h n.
Proof.
  intros h mono m n; induction m as [| m IH]; simpl.
  - lia.
  - specialize (mono (m + n)); lia.
Qed.

(* Base of the Abel induction: h nonzero only at 0. *)
Lemma gws_base :
  forall (d : Dist nat) (h : nat -> nat),
    (forall v, h (S v) <= h v) ->
    h 1 = 0 ->
    gws d h = h 0 * cdf_weight d 0.
Proof.
  induction d as [| [v w] d IH]; intros h mono h1; simpl.
  - lia.
  - rewrite (IH h mono h1).
    destruct v as [| v'].
    + simpl; nia.
    + assert (Hv : h (S v') = 0).
      { replace (S v') with (v' + 1) by lia.
        apply h_vanish; assumption. }
      simpl; rewrite Hv; nia.
Qed.

(* Abel's identity: peel the last level off a non-increasing summand. *)
Lemma gws_split :
  forall (d : Dist nat) (h : nat -> nat) (M : nat),
    (forall v, h (S v) <= h v) ->
    h (S M) = 0 ->
    gws d h = gws d (fun v => h v - h M) + h M * cdf_weight d M.
Proof.
  induction d as [| [v w] d IH]; intros h M mono hsM; simpl.
  - lia.
  - rewrite (IH h M mono hsM).
    destruct (v <=? M) eqn:E.
    + apply Nat.leb_le in E.
      assert (HM : h M <= h v).
      { replace M with ((M - v) + v) by lia.
        apply mono_chain; assumption. }
      nia.
    + apply Nat.leb_gt in E.
      assert (Hv : h v = 0).
      { replace v with ((v - S M) + S M) by lia.
        apply h_vanish; assumption. }
      rewrite Hv; nia.
Qed.

(* Base direction: FOSD implies gws dominance for every non-increasing
   summand vanishing beyond M.  Induction on M via Abel's identity. *)
Lemma fosd_gws :
  forall M (mu nu : Dist nat) (h : nat -> nat),
    total_weight mu = total_weight nu ->
    FOSD_le mu nu ->
    (forall v, h (S v) <= h v) ->
    h (S M) = 0 ->
    gws nu h <= gws mu h.
Proof.
  induction M as [| M IH]; intros mu nu h tw fosd mono hM.
  - rewrite (gws_base nu h mono hM), (gws_base mu h mono hM).
    apply Nat.mul_le_mono_l; exact (fosd 0).
  - rewrite (gws_split nu h (S M) mono hM), (gws_split mu h (S M) mono hM).
    assert (IH' : gws nu (fun v => h v - h (S M))
                  <= gws mu (fun v => h v - h (S M))).
    { apply IH; try assumption.
      - intro v; specialize (mono v); lia.
      - lia. }
    apply Nat.add_le_mono.
    + exact IH'.
    + apply Nat.mul_le_mono_l; exact (fosd (S M)).
Qed.

(* T10: FOSD closed under convolution. *)
Theorem FOSD_conv :
  forall mu1 nu1 mu2 nu2,
    total_weight mu1 = total_weight nu1 ->
    FOSD_le mu1 nu1 -> FOSD_le mu2 nu2 ->
    FOSD_le (conv mu1 mu2) (conv nu1 nu2).
Proof.
  intros mu1 nu1 mu2 nu2 tw f1 f2 r.
  rewrite !cdf_conv.
  eapply Nat.le_trans.
  - apply gws_mono; intro v.
    apply (FOSD_shift v mu2 nu2 f2 r).
  - apply (fosd_gws r mu1 nu1
             (fun v => cdf_weight (dmap (fun u => v + u) mu2) r) tw f1).
    + intro v; apply shift_cdf_mono.
    + apply shift_cdf_zero.
Qed.

(* T10 corollary: the closure lifts to every level of the hierarchy. *)
Theorem FOSD_SD_conv :
  forall k mu1 nu1 mu2 nu2,
    total_weight mu1 = total_weight nu1 ->
    FOSD_le mu1 nu1 -> FOSD_le mu2 nu2 ->
    SD_le k (conv mu1 mu2) (conv nu1 nu2).
Proof.
  induction k as [| k IH]; intros.
  - apply FOSD_conv; assumption.
  - apply SD_subsumes; apply IH; assumption.
Qed.
