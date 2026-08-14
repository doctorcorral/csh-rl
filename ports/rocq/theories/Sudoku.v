(* CSHRL portability kernel, Rocq port.
   T13 instances: verified Sudoku via the placement environment class.

   Two instances of the sized placement game (Placement.v):

   - 4x4 Sudoku (Shidoku) with 8 givens and a unique solution, mirroring
     the Agda CSHRL.Tasks.Verified.Sudoku4;
   - full 9x9 Sudoku with 38 givens and a unique solution, mirroring the
     Agda CSHRL.Tasks.Verified.Sudoku9.  The puzzle is chosen so that every
     empty cell (in row-major fill order) is directly conflict-forced,
     making the Finder's search tree linear.

   For each instance the trace-bridge CoindHomo (T13) is obtained from
   sized_coindhomo with no proof obligations beyond the static game
   description, and the Finder's policy rollout is verified to produce the
   unique completion by evaluation (vm_compute) -- including the FULL 9x9
   rollout, which call-by-value evaluation shares perfectly. *)

From Stdlib Require Import List Arith Lia Bool.
Import ListNotations.
From CSHRL Require Import Streams Core Placement.

(* ------------------------------------------------------------------ *)
(* Shared board machinery                                              *)
(* ------------------------------------------------------------------ *)

Definition cell := option nat.

(* Merge assigned digits into the template's empty slots, in order. *)
Fixpoint merge (t : list cell) (cfg : list nat) {struct t} : list cell :=
  match t with
  | nil => nil
  | Some d :: t' => Some d :: merge t' cfg
  | None :: t' =>
      match cfg with
      | nil => None :: merge t' nil
      | d :: cfg' => Some d :: merge t' cfg'
      end
  end.

(* Positions of the empty cells, in row-major order. *)
Fixpoint holes_of (p : nat) (t : list cell) {struct t} : list nat :=
  match t with
  | nil => nil
  | None :: t' => p :: holes_of (S p) t'
  | Some _ :: t' => holes_of (S p) t'
  end.

(* Does digit d at position p conflict with any other filled cell? *)
Fixpoint conflicts (sees : nat -> nat -> bool) (p d q : nat) (b : list cell)
    {struct b} : bool :=
  match b with
  | nil => false
  | None :: rest => conflicts sees p d (S q) rest
  | Some e :: rest =>
      (negb (q =? p) && sees p q && (d =? e)) || conflicts sees p d (S q) rest
  end.

(* Full-board pairwise consistency. *)
Fixpoint check_one (sees : nat -> nat -> bool) (p d q : nat) (b : list cell)
    {struct b} : bool :=
  match b with
  | nil => true
  | None :: rest => check_one sees p d (S q) rest
  | Some e :: rest =>
      negb (sees p q && (d =? e)) && check_one sees p d (S q) rest
  end.

Fixpoint ok_board_from (sees : nat -> nat -> bool) (p : nat) (b : list cell)
    {struct b} : bool :=
  match b with
  | nil => true
  | None :: rest => ok_board_from sees (S p) rest
  | Some d :: rest => check_one sees p d (S p) rest && ok_board_from sees (S p) rest
  end.

Definition ok_board (sees : nat -> nat -> bool) (b : list cell) : bool :=
  ok_board_from sees 0 b.

(* ------------------------------------------------------------------ *)
(* 4x4 Sudoku                                                          *)
(* ------------------------------------------------------------------ *)

Module Sudoku4.

  (* Peers on the 4x4 board: same row, column, or 2x2 box. *)
  Definition sees (p q : nat) : bool :=
    (p / 4 =? q / 4) || (p mod 4 =? q mod 4) ||
    ((p / 4 / 2 =? q / 4 / 2) && (p mod 4 / 2 =? q mod 4 / 2)).

  (* The puzzle (8 givens, unique solution):
     1 . . 4 / . 4 1 . / 2 . . 3 / . 3 2 . *)
  Definition template : list cell :=
    [Some 1; None; None; Some 4;
     None; Some 4; Some 1; None;
     Some 2; None; None; Some 3;
     None; Some 3; Some 2; None].

  Definition board_of (cfg : list nat) : list cell := merge template cfg.

  Inductive act : Type := D1 | D2 | D3 | D4.

  Definition digit (a : act) : nat :=
    match a with D1 => 1 | D2 => 2 | D3 => 3 | D4 => 4 end.

  Definition is_dead (cfg : list nat) : bool :=
    negb (ok_board sees (board_of cfg)).

  Definition is_solved (cfg : list nat) : bool := length cfg =? 8.

  Definition do_place (cfg : list nat) (a : act) : list nat := cfg ++ [digit a].

  Definition all_actions : list act := [D1; D2; D3; D4].

  Lemma Rpos : 0 < 100.
  Proof. lia. Qed.

  Lemma actions_ne : all_actions <> nil.
  Proof. discriminate. Qed.

  Lemma place_size :
    forall (c : list nat) (a : act), length (do_place c a) = S (length c).
  Proof.
    intros c a; unfold do_place; rewrite length_app; simpl; lia.
  Qed.

  Lemma solved_iff :
    forall c : list nat, is_solved c = (length c =? 8).
  Proof. reflexivity. Qed.

  (* T13 at the 4x4 Sudoku instance: the Finder's trace ranking preserves
     dominance of the full coinductive action-value streams. *)
  Theorem sudoku4_coindhomo :
    forall s,
      CoindHomo nat le (pstate (list nat)) act
        (pnext (list nat) act is_dead is_solved do_place 100)
        (preward (list nat) act is_dead is_solved do_place 100)
        (pvalue (list nat) act is_dead is_solved do_place 100 all_actions)
        (ranks (list nat) act is_dead is_solved do_place 100 all_actions 8) s.
  Proof.
    exact (sized_coindhomo (list nat) act is_dead is_solved do_place 100
             Rpos all_actions actions_ne 8
             (@length nat) place_size solved_iff).
  Qed.

  (* The digits of the unique completion, in row-major hole order. *)
  Definition solution : list nat := [2; 3; 3; 2; 1; 4; 4; 1].

  (* The Finder solves the puzzle: rolling out the verified policy fills
     the 8 empty cells with the unique solution. *)
  Example rollout :
    run_policy (list nat) act is_dead is_solved do_place 100 all_actions
      (Ongoing nil) 8 8 = [D2; D3; D3; D2; D1; D4; D4; D1].
  Proof. vm_compute; reflexivity. Qed.

  (* The completed board passes the full pairwise constraint check. *)
  Example valid : ok_board sees (board_of solution) = true.
  Proof. vm_compute; reflexivity. Qed.

  Example complete : is_solved solution = true.
  Proof. vm_compute; reflexivity. Qed.

End Sudoku4.

(* ------------------------------------------------------------------ *)
(* 9x9 Sudoku                                                          *)
(* ------------------------------------------------------------------ *)

Module Sudoku9.

  (* Peers on the 9x9 board: same row, column, or 3x3 box. *)
  Definition sees (p q : nat) : bool :=
    (p / 9 =? q / 9) || (p mod 9 =? q mod 9) ||
    ((p / 9 / 3 =? q / 9 / 3) && (p mod 9 / 3 =? q mod 9 / 3)).

  (* The puzzle (38 givens, unique solution, all empty cells directly
     conflict-forced in row-major order):

       . . 3 | 4 5 . | 7 8 .
       4 . 6 | . 8 9 | . . 3
       . . . | 1 2 . | . . 6
       ------+-------+------
       2 . 4 | . 6 . | . . 1
       . 6 . | 8 9 1 | 2 . 4
       8 9 . | . . . | 5 . .
       ------+-------+------
       3 . . | . . 8 | 9 . .
       . 7 . | . 1 . | . . 5
       9 1 2 | 3 4 . | . 7 .  *)
  Definition template : list cell :=
    [None; None; Some 3; Some 4; Some 5; None; Some 7; Some 8; None;
     Some 4; None; Some 6; None; Some 8; Some 9; None; None; Some 3;
     None; None; None; Some 1; Some 2; None; None; None; Some 6;
     Some 2; None; Some 4; None; Some 6; None; None; None; Some 1;
     None; Some 6; None; Some 8; Some 9; Some 1; Some 2; None; Some 4;
     Some 8; Some 9; None; None; None; None; Some 5; None; None;
     Some 3; None; None; None; None; Some 8; Some 9; None; None;
     None; Some 7; None; None; Some 1; None; None; None; Some 5;
     Some 9; Some 1; Some 2; Some 3; Some 4; None; None; Some 7; None].

  Definition board_of (cfg : list nat) : list cell := merge template cfg.

  Definition hole_positions : list nat := holes_of 0 template.

  Inductive act : Type := A1 | A2 | A3 | A4 | A5 | A6 | A7 | A8 | A9.

  Definition digit (a : act) : nat :=
    match a with
    | A1 => 1 | A2 => 2 | A3 => 3 | A4 => 4 | A5 => 5
    | A6 => 6 | A7 => 7 | A8 => 8 | A9 => 9
    end.

  (* For efficiency the dead check only tests the most recently placed cell
     against the board: on reachable configurations this coincides with
     full-board consistency, and the final board is re-validated with the
     full pairwise check below. *)
  Definition is_dead (cfg : list nat) : bool :=
    let k := pred (length cfg) in
    conflicts sees (List.nth k hole_positions 0) (List.nth k cfg 0) 0
      (board_of cfg).

  Definition is_solved (cfg : list nat) : bool := length cfg =? 43.

  Definition do_place (cfg : list nat) (a : act) : list nat := cfg ++ [digit a].

  Definition all_actions : list act := [A1; A2; A3; A4; A5; A6; A7; A8; A9].

  Lemma Rpos : 0 < 100.
  Proof. lia. Qed.

  Lemma actions_ne : all_actions <> nil.
  Proof. discriminate. Qed.

  Lemma place_size :
    forall (c : list nat) (a : act), length (do_place c a) = S (length c).
  Proof.
    intros c a; unfold do_place; rewrite length_app; simpl; lia.
  Qed.

  Lemma solved_iff :
    forall c : list nat, is_solved c = (length c =? 43).
  Proof. reflexivity. Qed.

  (* T13 at the full 9x9 Sudoku instance. *)
  Theorem sudoku9_coindhomo :
    forall s,
      CoindHomo nat le (pstate (list nat)) act
        (pnext (list nat) act is_dead is_solved do_place 100)
        (preward (list nat) act is_dead is_solved do_place 100)
        (pvalue (list nat) act is_dead is_solved do_place 100 all_actions)
        (ranks (list nat) act is_dead is_solved do_place 100 all_actions 43) s.
  Proof.
    exact (sized_coindhomo (list nat) act is_dead is_solved do_place 100
             Rpos all_actions actions_ne 43
             (@length nat) place_size solved_iff).
  Qed.

  (* The digits of the unique completion, in row-major hole order. *)
  Definition solution : list nat :=
    [1; 2; 6; 9; 5; 7; 1; 2; 7; 8; 9; 3; 4; 5; 3; 5; 7; 8;
     9; 5; 7; 3; 1; 2; 3; 4; 6; 7; 4; 5; 6; 7; 1; 2; 6; 8;
     9; 2; 3; 4; 5; 6; 8].

  (* The Finder solves the full 9x9 puzzle: rolling out the verified policy
     fills all 43 empty cells with the unique completion. *)
  Example rollout :
    map digit
      (run_policy (list nat) act is_dead is_solved do_place 100 all_actions
        (Ongoing nil) 43 43) = solution.
  Proof. vm_compute; reflexivity. Qed.

  (* The completed board passes the full pairwise constraint check. *)
  Example valid : ok_board sees (board_of solution) = true.
  Proof. vm_compute; reflexivity. Qed.

  Example complete : is_solved solution = true.
  Proof. vm_compute; reflexivity. Qed.

End Sudoku9.
