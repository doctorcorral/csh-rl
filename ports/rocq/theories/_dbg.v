From CSHRL Require Import Streams Core Subsumption BinarySacrifice.
Lemma paradise_accumulates_N :
  forall N, partial_sum nat Nat.add 0 N (bvalue (bnext Start GoParadise)) = N.
Proof.
  induction N as [| k IH]; simpl.
  - reflexivity.
  - Show.
