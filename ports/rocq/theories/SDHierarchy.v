(* CSHRL portability kernel, Rocq port.
   D14, T9: FOSD and the stochastic dominance hierarchy (Agda references
   src/CSHRL/Probability/FOSD.agda, SD.agda, Compose.agda).

   FOSD:   mu FOSD<= nu iff every CDF value of nu is below mu's
           (preferred by ALL monotone utility functions).
   SD[k]:  k-fold iterated prefix sums of the CDF; SD[0] = FOSD,
           SD[1] = SOSD (risk-averse agents), SD[2] = TOSD, ...

   T9a (hierarchy):  SD[k] implies SD[k+1] -- prefix sums preserve
        pointwise dominance, so each level subsumes the previous one.
   T9b (closure):    FOSD and every SD[k] are closed under mixture (++)
        and reward scaling; sd_weight is a linear operator. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
From CSHRL Require Import Dist.

(* D14a: first-order stochastic dominance. *)
Definition FOSD_le (mu nu : Dist nat) : Prop :=
  forall r, cdf_weight nu r <= cdf_weight mu r.

Lemma FOSD_refl : forall d, FOSD_le d d.
Proof. intros d r; lia. Qed.

Lemma FOSD_trans :
  forall a b c, FOSD_le a b -> FOSD_le b c -> FOSD_le a c.
Proof. intros a b c H1 H2 r; specialize (H1 r); specialize (H2 r); lia. Qed.

(* D14b: iterated prefix sums and the SD[k] hierarchy. *)
Fixpoint prefix_sum (f : nat -> nat) (r : nat) : nat :=
  match r with
  | 0 => f 0
  | S k => f (S k) + prefix_sum f k
  end.

Fixpoint sd_weight (k : nat) (d : Dist nat) : nat -> nat :=
  match k with
  | 0 => cdf_weight d
  | S k' => prefix_sum (sd_weight k' d)
  end.

Definition SD_le (k : nat) (mu nu : Dist nat) : Prop :=
  forall r, sd_weight k nu r <= sd_weight k mu r.

(* SD[0] is definitionally FOSD. *)
Lemma SD0_FOSD : forall mu nu, SD_le 0 mu nu <-> FOSD_le mu nu.
Proof. intros mu nu; split; intro H; exact H. Qed.

Lemma SD_refl : forall k d, SD_le k d d.
Proof. intros k d r; lia. Qed.

Lemma SD_trans :
  forall k a b c, SD_le k a b -> SD_le k b c -> SD_le k a c.
Proof. intros k a b c H1 H2 r; specialize (H1 r); specialize (H2 r); lia. Qed.

(* Prefix sums preserve pointwise dominance. *)
Lemma prefix_sum_mono :
  forall (f g : nat -> nat),
    (forall r, f r <= g r) ->
    forall r, prefix_sum f r <= prefix_sum g r.
Proof.
  intros f g H r; induction r as [| r IH]; simpl.
  - apply H.
  - specialize (H (S r)); lia.
Qed.

(* T9a: the hierarchy.  Verified at level k, verified at level k+1. *)
Theorem SD_subsumes :
  forall k mu nu, SD_le k mu nu -> SD_le (S k) mu nu.
Proof.
  intros k mu nu H r; simpl; apply prefix_sum_mono; exact H.
Qed.

Theorem SD_subsumes_n :
  forall k j mu nu, SD_le k mu nu -> SD_le (j + k) mu nu.
Proof.
  intros k j; induction j as [| j IH]; intros mu nu H; simpl.
  - exact H.
  - apply SD_subsumes; apply IH; exact H.
Qed.

(* Linearity of prefix_sum, hence of sd_weight. *)
Lemma prefix_sum_ext :
  forall (f g : nat -> nat),
    (forall r, f r = g r) ->
    forall r, prefix_sum f r = prefix_sum g r.
Proof.
  intros f g H r; induction r as [| r IH]; simpl.
  - apply H.
  - rewrite IH, H; reflexivity.
Qed.

Lemma prefix_sum_add :
  forall (f g : nat -> nat) r,
    prefix_sum (fun t => f t + g t) r = prefix_sum f r + prefix_sum g r.
Proof.
  intros f g r; induction r as [| r IH]; simpl.
  - reflexivity.
  - rewrite IH; lia.
Qed.

Lemma prefix_sum_mul :
  forall c (f : nat -> nat) r,
    prefix_sum (fun t => c * f t) r = c * prefix_sum f r.
Proof.
  intros c f r; induction r as [| r IH]; simpl.
  - reflexivity.
  - rewrite IH; lia.
Qed.

Lemma sd_weight_app :
  forall k (d1 d2 : Dist nat) r,
    sd_weight k (d1 ++ d2) r = sd_weight k d1 r + sd_weight k d2 r.
Proof.
  induction k as [| k IH]; intros d1 d2 r; simpl.
  - apply cdf_weight_app.
  - rewrite (prefix_sum_ext _ _ (IH d1 d2) r).
    apply prefix_sum_add.
Qed.

Lemma sd_weight_scale :
  forall k (d : Dist nat) r c,
    sd_weight k (dscale c d) r = c * sd_weight k d r.
Proof.
  induction k as [| k IH]; intros d r c; simpl.
  - apply cdf_weight_scale.
  - rewrite (prefix_sum_ext _ _ (fun t => IH d t c) r).
    apply prefix_sum_mul.
Qed.

(* T9b: closure of the whole hierarchy under mixture and scaling. *)
Theorem FOSD_app :
  forall mu1 nu1 mu2 nu2,
    FOSD_le mu1 nu1 -> FOSD_le mu2 nu2 ->
    FOSD_le (mu1 ++ mu2) (nu1 ++ nu2).
Proof.
  intros mu1 nu1 mu2 nu2 H1 H2 r.
  rewrite !cdf_weight_app.
  specialize (H1 r); specialize (H2 r); lia.
Qed.

Theorem FOSD_scale :
  forall k mu nu, FOSD_le mu nu -> FOSD_le (dscale k mu) (dscale k nu).
Proof.
  intros k mu nu H r.
  rewrite !cdf_weight_scale.
  specialize (H r); nia.
Qed.

Theorem SD_app :
  forall k mu1 nu1 mu2 nu2,
    SD_le k mu1 nu1 -> SD_le k mu2 nu2 ->
    SD_le k (mu1 ++ mu2) (nu1 ++ nu2).
Proof.
  intros k mu1 nu1 mu2 nu2 H1 H2 r.
  rewrite !sd_weight_app.
  specialize (H1 r); specialize (H2 r); lia.
Qed.

Theorem SD_scale :
  forall k c mu nu, SD_le k mu nu -> SD_le k (dscale c mu) (dscale c nu).
Proof.
  intros k c mu nu H r.
  rewrite !sd_weight_scale.
  specialize (H r); nia.
Qed.
