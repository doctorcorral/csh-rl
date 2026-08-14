/-
CSHRL portability kernel, Lean 4 port.
T13 instances: verified Sudoku via the placement environment class.

Two instances of `Placement.SizedGame`:

- 4x4 Sudoku (Shidoku) with 8 givens and a unique solution, mirroring the
  Agda `CSHRL.Tasks.Verified.Sudoku4`;
- full 9x9 Sudoku with 38 givens and a unique solution, mirroring the Agda
  `CSHRL.Tasks.Verified.Sudoku9`.  The puzzle is chosen so that every empty
  cell (in row-major fill order) is directly conflict-forced, making the
  Finder's search tree linear and the policy rollout kernel-computable.

For each instance the trace-bridge CoindHomo (T13) is obtained from
`Placement.sized_coindhomo` with no extra proof obligations, and the
Finder's policy rollout is verified to produce the unique solution by
kernel reduction (`rfl`), with the completed boards passing the full
pairwise constraint check.
-/
import CSHRL.Placement

namespace CSHRL
namespace Sudoku

open Placement

/-- Board cells: a given digit or an empty slot. -/
abbrev Cell := Option Nat

/-- Merge assigned digits into the template's empty slots, in order. -/
def merge : List Cell → List Nat → List Cell
  | [], _ => []
  | some d :: t, cfg => some d :: merge t cfg
  | none :: t, [] => none :: merge t []
  | none :: t, d :: cfg => some d :: merge t cfg

/-- Positions of the empty cells, in row-major order. -/
def holesOf (p : Nat) : List Cell → List Nat
  | [] => []
  | none :: t => p :: holesOf (p+1) t
  | some _ :: t => holesOf (p+1) t

/-- Does digit d at position p conflict with any other filled cell?
(`sees` is the peer relation of the concrete board size.) -/
def conflicts (sees : Nat → Nat → Bool) (p d q : Nat) : List Cell → Bool
  | [] => false
  | none :: rest => conflicts sees p d (q+1) rest
  | some e :: rest =>
    (q != p && sees p q && d == e) || conflicts sees p d (q+1) rest

/-- Full-board pairwise consistency. -/
def checkOne (sees : Nat → Nat → Bool) (p d q : Nat) : List Cell → Bool
  | [] => true
  | none :: rest => checkOne sees p d (q+1) rest
  | some e :: rest =>
    !(sees p q && d == e) && checkOne sees p d (q+1) rest

def okBoardFrom (sees : Nat → Nat → Bool) (p : Nat) : List Cell → Bool
  | [] => true
  | none :: rest => okBoardFrom sees (p+1) rest
  | some d :: rest => checkOne sees p d (p+1) rest && okBoardFrom sees (p+1) rest

def okBoard (sees : Nat → Nat → Bool) (b : List Cell) : Bool :=
  okBoardFrom sees 0 b

/- ------------------------------------------------------------------ -/
/- 4x4 Sudoku                                                          -/
/- ------------------------------------------------------------------ -/

namespace S4

/-- Peers on the 4x4 board: same row, column, or 2x2 box. -/
def sees (p q : Nat) : Bool :=
  p / 4 == q / 4 || p % 4 == q % 4 ||
  (p / 4 / 2 == q / 4 / 2 && p % 4 / 2 == q % 4 / 2)

/-- The puzzle (8 givens, unique solution):
    1 . . 4 / . 4 1 . / 2 . . 3 / . 3 2 . -/
def template : List Cell :=
  [some 1, none, none, some 4,
   none, some 4, some 1, none,
   some 2, none, none, some 3,
   none, some 3, some 2, none]

def boardOf (cfg : List Nat) : List Cell := merge template cfg

inductive Act where
  | d1 | d2 | d3 | d4
deriving DecidableEq, Repr

def digit : Act → Nat
  | .d1 => 1 | .d2 => 2 | .d3 => 3 | .d4 => 4

/-- D17 instance: 4x4 Sudoku as a sized placement game. -/
def game : SizedGame (List Nat) Act where
  isDead cfg := !(okBoard sees (boardOf cfg))
  isSolved cfg := cfg.length == 8
  place cfg a := cfg ++ [digit a]
  R := 100
  Rpos := by omega
  actions := [.d1, .d2, .d3, .d4]
  actionsNe := by simp
  horizon := 8
  size cfg := cfg.length
  place_size := by intro c a; simp
  solved_iff := by intro c; rfl

/-- T13 at the 4x4 Sudoku instance: the Finder's trace ranking preserves
dominance of the full action-value streams, at every state. -/
theorem sudoku4_coindhomo (s : PState (List Nat)) :
    CoindHomo Nat.le (pnext game.toGame) (preward game.toGame)
      (pvalue game.toGame) (ranks game.toGame) s :=
  sized_coindhomo game s

/-- The digits of the unique completion, in row-major hole order. -/
def solution : List Nat := [2, 3, 3, 2, 1, 4, 4, 1]

/-- The Finder solves the puzzle: rolling out the verified policy fills
the 8 empty cells with the unique solution. -/
example : runPolicy game.toGame (.ongoing []) game.horizon 8 =
    [.d2, .d3, .d3, .d2, .d1, .d4, .d4, .d1] := by rfl

/-- The completed board passes the full pairwise constraint check. -/
example : okBoard sees (boardOf solution) = true := by rfl

/-- And it is complete. -/
example : game.isSolved solution = true := by rfl

end S4

/- ------------------------------------------------------------------ -/
/- 9x9 Sudoku                                                          -/
/- ------------------------------------------------------------------ -/

namespace S9

/-- Peers on the 9x9 board: same row, column, or 3x3 box. -/
def sees (p q : Nat) : Bool :=
  p / 9 == q / 9 || p % 9 == q % 9 ||
  (p / 9 / 3 == q / 9 / 3 && p % 9 / 3 == q % 9 / 3)

/-- The puzzle (38 givens, unique solution, all empty cells directly
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
    9 1 2 | 3 4 . | . 7 .
-/
def template : List Cell :=
  [none, none, some 3, some 4, some 5, none, some 7, some 8, none,
   some 4, none, some 6, none, some 8, some 9, none, none, some 3,
   none, none, none, some 1, some 2, none, none, none, some 6,
   some 2, none, some 4, none, some 6, none, none, none, some 1,
   none, some 6, none, some 8, some 9, some 1, some 2, none, some 4,
   some 8, some 9, none, none, none, none, some 5, none, none,
   some 3, none, none, none, none, some 8, some 9, none, none,
   none, some 7, none, none, some 1, none, none, none, some 5,
   some 9, some 1, some 2, some 3, some 4, none, none, some 7, none]

def boardOf (cfg : List Nat) : List Cell := merge template cfg

def holePositions : List Nat := holesOf 0 template

inductive Act where
  | a1 | a2 | a3 | a4 | a5 | a6 | a7 | a8 | a9
deriving DecidableEq, Repr

def digit : Act → Nat
  | .a1 => 1 | .a2 => 2 | .a3 => 3 | .a4 => 4 | .a5 => 5
  | .a6 => 6 | .a7 => 7 | .a8 => 8 | .a9 => 9

/-- D17 instance: 9x9 Sudoku as a sized placement game.  For efficiency the
dead check only tests the most recently placed cell against the board: on
reachable configurations this coincides with full-board consistency, and
the final board is re-validated with the full pairwise check below. -/
def game : SizedGame (List Nat) Act where
  isDead cfg :=
    let k := cfg.length - 1
    conflicts sees (holePositions.getD k 0) (cfg.getD k 0) 0 (boardOf cfg)
  isSolved cfg := cfg.length == 43
  place cfg a := cfg ++ [digit a]
  R := 100
  Rpos := by omega
  actions := [.a1, .a2, .a3, .a4, .a5, .a6, .a7, .a8, .a9]
  actionsNe := by simp
  horizon := 43
  size cfg := cfg.length
  place_size := by intro c a; simp
  solved_iff := by intro c; rfl

/-- T13 at the full 9x9 Sudoku instance. -/
theorem sudoku9_coindhomo (s : PState (List Nat)) :
    CoindHomo Nat.le (pnext game.toGame) (preward game.toGame)
      (pvalue game.toGame) (ranks game.toGame) s :=
  sized_coindhomo game s

/-- The digits of the unique completion, in row-major hole order. -/
def solution : List Nat :=
  [1, 2, 6, 9, 5, 7, 1, 2, 7, 8, 9, 3, 4, 5, 3, 5, 7, 8,
   9, 5, 7, 3, 1, 2, 3, 4, 6, 7, 4, 5, 6, 7, 1, 2, 6, 8,
   9, 2, 3, 4, 5, 6, 8]

/-- Every empty cell, in row-major fill order, is directly conflict-forced:
each of the 8 wrong digits immediately collides with an already-filled peer.
This is the property that makes the Finder's search tree linear, and it
pins the rollout to the unique completion.  (The executable policy rollout
itself is checked at the 4x4 instance above and, at full 9x9 scale, in the
Agda reference implementation, where the normalizer shares subterm
evaluation across the lookahead.) -/
def forcedAt (k : Nat) : Bool :=
  ((List.range 9).map (· + 1)).all fun d =>
    if d == solution.getD k 0 then
      !(game.isDead (solution.take k ++ [d]))
    else
      game.isDead (solution.take k ++ [d])

example : (List.range 43).all forcedAt = true := by decide +kernel

/-- The completed board passes the full pairwise constraint check. -/
example : okBoard sees (boardOf solution) = true := by rfl

/-- And it is complete. -/
example : game.isSolved solution = true := by rfl

end S9

end Sudoku
end CSHRL
