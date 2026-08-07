(* CSHRL portability kernel, Rocq port.
   D15, T11: the compositional ranking algebra (Agda reference
   src/CSHRL/Core/Compose.agda).

   VerifiedRanking bundles an action ordering with a proof that it
   preserves SD[k] on a marginal-reward function at every timestep.
   The algebra: verify components in isolation, compose the proofs.

   T11a: hierarchy subsumption (free upgrade from level k to k+1);
   T11b: product composition for any SD[k]-preserving operation, with
         mixture (++), convolution, and scaling as concrete instances;
   T11c: sum composition for disjoint environments. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
From CSHRL Require Import Dist SDHierarchy Convolution.

(* D15: a verified ranking on marginal rewards, at SD level k. *)
Record VerifiedRanking
  (State Action : Type)
  (marginal : State -> Action -> nat -> Dist nat)
  (k : nat) : Type := {
  vr_rank : State -> Action -> Action -> Prop;
  vr_preserves :
    forall a b s,
      vr_rank s a b ->
      forall n, SD_le k (marginal s a n) (marginal s b n)
}.

Arguments vr_rank {State Action marginal k}.
Arguments vr_preserves {State Action marginal k}.

(* T11a: verified at level k, verified at level k+1. *)
Definition ranking_subsumes
  {State Action : Type} {m : State -> Action -> nat -> Dist nat} {k : nat}
  (vr : VerifiedRanking State Action m k)
  : VerifiedRanking State Action m (S k) :=
  {| vr_rank := vr_rank vr;
     vr_preserves := fun a b s p n =>
       SD_subsumes k _ _ (vr_preserves vr a b s p n) |}.

(* T11b: abstract product composition.  Any operation on distributions
   that preserves SD[k] composes verified rankings component-wise. *)
Definition product_ranking
  {S1 A1 S2 A2 : Type}
  {m1 : S1 -> A1 -> nat -> Dist nat}
  {m2 : S2 -> A2 -> nat -> Dist nat}
  {k : nat}
  (compose : Dist nat -> Dist nat -> Dist nat)
  (compose_preserves :
    forall mu1 nu1 mu2 nu2,
      SD_le k mu1 nu1 -> SD_le k mu2 nu2 ->
      SD_le k (compose mu1 mu2) (compose nu1 nu2))
  (vr1 : VerifiedRanking S1 A1 m1 k)
  (vr2 : VerifiedRanking S2 A2 m2 k)
  : VerifiedRanking (S1 * S2) (A1 * A2)
      (fun s a n => compose (m1 (fst s) (fst a) n) (m2 (snd s) (snd a) n)) k :=
  {| vr_rank := fun s a b =>
       vr_rank vr1 (fst s) (fst a) (fst b) /\
       vr_rank vr2 (snd s) (snd a) (snd b);
     vr_preserves := fun a b s p n =>
       compose_preserves _ _ _ _
         (vr_preserves vr1 (fst a) (fst b) (fst s) (proj1 p) n)
         (vr_preserves vr2 (snd a) (snd b) (snd s) (proj2 p) n) |}.

(* Concrete instance: mixture product via concatenation. *)
Definition app_product
  {S1 A1 S2 A2 : Type}
  {m1 : S1 -> A1 -> nat -> Dist nat}
  {m2 : S2 -> A2 -> nat -> Dist nat}
  {k : nat}
  (vr1 : VerifiedRanking S1 A1 m1 k)
  (vr2 : VerifiedRanking S2 A2 m2 k)
  : VerifiedRanking (S1 * S2) (A1 * A2)
      (fun s a n => m1 (fst s) (fst a) n ++ m2 (snd s) (snd a) n) k :=
  product_ranking (@app _) (SD_app k) vr1 vr2.

(* Concrete instance: scaling preserves verification. *)
Definition scale_ranking
  {State Action : Type} {m : State -> Action -> nat -> Dist nat} {k : nat}
  (c : nat)
  (vr : VerifiedRanking State Action m k)
  : VerifiedRanking State Action (fun s a n => dscale c (m s a n)) k :=
  {| vr_rank := vr_rank vr;
     vr_preserves := fun a b s p n =>
       SD_scale k c _ _ (vr_preserves vr a b s p n) |}.

(* Composability demonstration: compose via ++, then scale. *)
Definition scaled_product
  {S1 A1 S2 A2 : Type}
  {m1 : S1 -> A1 -> nat -> Dist nat}
  {m2 : S2 -> A2 -> nat -> Dist nat}
  {k : nat}
  (c : nat)
  (vr1 : VerifiedRanking S1 A1 m1 k)
  (vr2 : VerifiedRanking S2 A2 m2 k)
  : VerifiedRanking (S1 * S2) (A1 * A2)
      (fun s a n => dscale c (m1 (fst s) (fst a) n ++ m2 (snd s) (snd a) n)) k :=
  scale_ranking c (app_product vr1 vr2).

(* Concrete instance: convolution product.  Requires FOSD-level component
   rankings (level 0) and equal total weights on the first component;
   yields verification at EVERY level k via FOSD_SD_conv. *)
Definition conv_product
  {S1 A1 S2 A2 : Type}
  {m1 : S1 -> A1 -> nat -> Dist nat}
  {m2 : S2 -> A2 -> nat -> Dist nat}
  {k : nat}
  (tw : forall s a b n, total_weight (m1 s a n) = total_weight (m1 s b n))
  (vr1 : VerifiedRanking S1 A1 m1 0)
  (vr2 : VerifiedRanking S2 A2 m2 0)
  : VerifiedRanking (S1 * S2) (A1 * A2)
      (fun s a n => conv (m1 (fst s) (fst a) n) (m2 (snd s) (snd a) n)) k :=
  {| vr_rank := fun s a b =>
       vr_rank vr1 (fst s) (fst a) (fst b) /\
       vr_rank vr2 (snd s) (snd a) (snd b);
     vr_preserves := fun a b s p n =>
       FOSD_SD_conv k _ _ _ _
         (tw (fst s) (fst a) (fst b) n)
         (vr_preserves vr1 (fst a) (fst b) (fst s) (proj1 p) n)
         (vr_preserves vr2 (snd a) (snd b) (snd s) (proj2 p) n) |}.

(* T11c: sum composition for disjoint environments; the combined ranking
   dispatches to the matching component, mismatches are impossible. *)
Section SumCompose.
  Context {S1 A1 S2 A2 : Type}.
  Context {m1 : S1 -> A1 -> nat -> Dist nat}.
  Context {m2 : S2 -> A2 -> nat -> Dist nat}.
  Context {k : nat}.

  Definition sum_marginal (s : S1 + S2) (a : A1 + A2) (n : nat) : Dist nat :=
    match s, a with
    | inl s1, inl a1 => m1 s1 a1 n
    | inr s2, inr a2 => m2 s2 a2 n
    | _, _ => []
    end.

  Definition sum_rank
    (vr1 : VerifiedRanking S1 A1 m1 k) (vr2 : VerifiedRanking S2 A2 m2 k)
    (s : S1 + S2) (a b : A1 + A2) : Prop :=
    match s, a, b with
    | inl s1, inl a1, inl b1 => vr_rank vr1 s1 a1 b1
    | inr s2, inr a2, inr b2 => vr_rank vr2 s2 a2 b2
    | _, _, _ => False
    end.

  Definition sum_ranking
    (vr1 : VerifiedRanking S1 A1 m1 k) (vr2 : VerifiedRanking S2 A2 m2 k)
    : VerifiedRanking (S1 + S2) (A1 + A2) sum_marginal k.
  Proof.
    refine {| vr_rank := sum_rank vr1 vr2 |}.
    intros a b s p n.
    destruct s as [s1 | s2]; destruct a as [a1 | a2]; destruct b as [b1 | b2];
      simpl in p; try contradiction; simpl.
    - exact (vr_preserves vr1 a1 b1 s1 p n).
    - exact (vr_preserves vr2 a2 b2 s2 p n).
  Defined.

End SumCompose.
