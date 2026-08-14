(* CSHRL portability kernel, Rocq port.
   Conformance check: every kernel theorem must be closed under the
   global context (no axioms, no admitted proofs).

   Each Print Assumptions below must output
     "Closed under the global context". *)

From CSHRL Require Import
  Streams Core BinarySacrifice SkillInvestment PreparationDilemma
  Subsumption Learning Convergence QLearningFailure
  Dist Lex SDHierarchy Convolution Ranking Abstraction
  Placement Sudoku.

(* T1 *)
Print Assumptions stream_le_iff_pointwise.
(* T2 *)
Print Assumptions decomposition.
(* T3 *)
Print Assumptions sacrifice_coinductive_homomorphism.
Print Assumptions no_coindhomo_forward.
Print Assumptions no_coindhomo_backward.
Print Assumptions skill_coinductive_homomorphism.
Print Assumptions skill_no_coindhomo_forward.
Print Assumptions skill_no_coindhomo_backward.
Print Assumptions prep_coinductive_homomorphism.
Print Assumptions prep_no_coindhomo_forward.
Print Assumptions prep_no_coindhomo_backward.
(* T4 *)
Print Assumptions subsumes_partial_sum.
Print Assumptions subsumes_successor_return.
(* T5 *)
Print Assumptions swap_fixes_pair.
Print Assumptions demote_preserves_dominance.
(* T6 *)
Print Assumptions q_learning_picks_inferior_successor.
(* T7 *)
Print Assumptions swap_adjacent_decreases.
Print Assumptions fix_first_progress.
Print Assumptions swap_convergence_bound.
Print Assumptions violations_zero_iff.
Print Assumptions learn_realizes_oracle.
(* T8 *)
Print Assumptions stream_le_lex.
Print Assumptions pointwise_homo_stochastic.
(* T9 *)
Print Assumptions SD_subsumes.
Print Assumptions SD_app.
Print Assumptions SD_scale.
(* T10 *)
Print Assumptions FOSD_conv.
Print Assumptions FOSD_SD_conv.
(* T11 *)
Print Assumptions ranking_subsumes.
Print Assumptions product_ranking.
Print Assumptions conv_product.
Print Assumptions sum_ranking.
(* T12 *)
Print Assumptions abstract_lift.
Print Assumptions abstract_conv_product.
(* T13 *)
Print Assumptions best_trace_is_solve.
Print Assumptions placement_coindhomo.
Print Assumptions sized_coindhomo.
Print Assumptions Sudoku4.sudoku4_coindhomo.
Print Assumptions Sudoku9.sudoku9_coindhomo.
