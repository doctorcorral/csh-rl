/-
CSHRL portability kernel, Lean 4 port.
D17, T13: the combinatorial placement environment class and its trace bridge.

Ports the CombinatorialPlacementMDP environment class from the Agda reference
implementation: constraint-satisfaction placement games (N-Queens, Sudoku,
graph coloring) with absorbing Dead/Solved states and sparse binary rewards.

The main theorem (T13, `placement_coindhomo`) is the trace bridge: the
computable lexicographic ranking of finite reward traces forms a CoindHomo,
i.e. it preserves dominance of the full (infinite) action-value streams.
The proof goes through the binary structure of `solve` (every value is 0 or
R) and its monotonicity, which together turn lexicographic trace comparison
into pointwise stream comparison.

Improving on the Agda reference, the horizon-sufficiency obligation is
discharged generically for `SizedGame`s (each placement increases a size
measure by one, and solving means reaching the horizon), so concrete
instances get the CoindHomo with no proof obligations beyond their static
game description.
-/
import CSHRL.Core

namespace CSHRL
namespace Placement

/-- States of a placement game: a partial configuration, a dead end, or a
complete solution. -/
inductive PState (Config : Type) where
  | ongoing : Config → PState Config
  | dead    : PState Config
  | solved  : Config → PState Config

/-- D17: a combinatorial placement game. -/
structure Game (Config Action : Type) where
  isDead    : Config → Bool
  isSolved  : Config → Bool
  place     : Config → Action → Config
  R         : Nat
  Rpos      : 0 < R
  actions   : List Action
  actionsNe : actions ≠ []
  horizon   : Nat

variable {Config Action : Type}

/-- One step of the placement MDP: Dead and Solved are absorbing. -/
def step (g : Game Config Action) : PState Config → Action → PState Config × Nat
  | .dead, _ => (.dead, 0)
  | .solved c, _ => (.solved c, g.R)
  | .ongoing c, a =>
    let c' := g.place c a
    if g.isDead c' then (.dead, 0)
    else if g.isSolved c' then (.solved c', g.R)
    else (.ongoing c', 0)

def maxList : List Nat → Nat
  | [] => 0
  | x :: xs => max x (maxList xs)

/-- Finite-horizon optimal value (the n-step Bellman backup). -/
def solve (g : Game Config Action) : PState Config → Nat → Nat
  | s, 0 => maxList (g.actions.map fun a => (step g s a).2)
  | s, n+1 => maxList (g.actions.map fun a => solve g (step g s a).1 n)

def pnext (g : Game Config Action) (s : PState Config) (a : Action) : PState Config :=
  (step g s a).1

def preward (g : Game Config Action) (s : PState Config) (a : Action) : Nat :=
  (step g s a).2

/-- The value stream, in the functional representation. -/
def pvalue (g : Game Config Action) (s : PState Config) : Stream' Nat :=
  fun n => solve g s n

/- ------------------------------------------------------------------ -/
/- maxList toolkit                                                     -/
/- ------------------------------------------------------------------ -/

theorem maxList_all_zero {A : Type} (f : A → Nat) (l : List A)
    (h : ∀ x ∈ l, f x = 0) : maxList (l.map f) = 0 := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, maxList]
    rw [h x (List.mem_cons_self ..), ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    omega

theorem maxList_all_R {A : Type} (f : A → Nat) (l : List A) (R : Nat)
    (hne : l ≠ []) (h : ∀ x ∈ l, f x = R) : maxList (l.map f) = R := by
  induction l with
  | nil => exact absurd rfl hne
  | cons x xs ih =>
    simp only [List.map_cons, maxList]
    rw [h x (List.mem_cons_self ..)]
    cases xs with
    | nil => simp [maxList]
    | cons y ys =>
      rw [ih (by simp) (fun z hz => h z (List.mem_cons_of_mem _ hz))]
      omega

theorem maxList_binary {A : Type} (f : A → Nat) (l : List A) (R : Nat)
    (h : ∀ x ∈ l, f x = 0 ∨ f x = R) :
    maxList (l.map f) = 0 ∨ maxList (l.map f) = R := by
  induction l with
  | nil => exact Or.inl rfl
  | cons x xs ih =>
    simp only [List.map_cons, maxList]
    have hx := h x (List.mem_cons_self ..)
    have hxs := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    omega

theorem maxList_le {A : Type} (f : A → Nat) (l : List A) (B : Nat)
    (h : ∀ x ∈ l, f x ≤ B) : maxList (l.map f) ≤ B := by
  induction l with
  | nil => exact Nat.zero_le B
  | cons x xs ih =>
    simp only [List.map_cons, maxList]
    have hx := h x (List.mem_cons_self ..)
    have hxs := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    omega

theorem maxList_mem_R {A : Type} (f : A → Nat) (l : List A) (R : Nat)
    (x : A) (hx : x ∈ l) (hfx : f x = R) (hle : ∀ y ∈ l, f y ≤ R) :
    maxList (l.map f) = R := by
  induction l with
  | nil => cases hx
  | cons z zs ih =>
    simp only [List.map_cons, maxList]
    have hz := hle z (List.mem_cons_self ..)
    rcases List.mem_cons.mp hx with h | h
    · subst h
      have := maxList_le f zs R (fun y hy => hle y (List.mem_cons_of_mem _ hy))
      omega
    · have := ih h (fun y hy => hle y (List.mem_cons_of_mem _ hy))
      omega

theorem maxList_R_exists {A : Type} (f : A → Nat) (l : List A) (R : Nat)
    (hR : 0 < R) (h : maxList (l.map f) = R) : ∃ x ∈ l, f x = R := by
  induction l with
  | nil => simp [maxList] at h; omega
  | cons x xs ih =>
    simp only [List.map_cons, maxList] at h
    by_cases hx : f x = R
    · exact ⟨x, List.mem_cons_self .., hx⟩
    · have : maxList (xs.map f) = R := by omega
      obtain ⟨y, hy, hfy⟩ := ih this
      exact ⟨y, List.mem_cons_of_mem _ hy, hfy⟩

theorem maxList_congr {A : Type} (f h : A → Nat) (l : List A)
    (he : ∀ x ∈ l, f x = h x) : maxList (l.map f) = maxList (l.map h) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, maxList]
    rw [he x (List.mem_cons_self ..), ih (fun y hy => he y (List.mem_cons_of_mem _ hy))]

/- ------------------------------------------------------------------ -/
/- Absorbing states and the binary structure of solve                  -/
/- ------------------------------------------------------------------ -/

variable (g : Game Config Action)

theorem solve_dead : ∀ n, solve g .dead n = 0 := by
  intro n
  induction n with
  | zero => exact maxList_all_zero _ _ (fun a _ => rfl)
  | succ n ih => exact maxList_all_zero _ _ (fun a _ => ih)

theorem solve_solved (c : Config) : ∀ n, solve g (.solved c) n = g.R := by
  intro n
  induction n with
  | zero => exact maxList_all_R _ _ _ g.actionsNe (fun a _ => rfl)
  | succ n ih => exact maxList_all_R _ _ _ g.actionsNe (fun a _ => ih)

theorem reward_binary (s : PState Config) (a : Action) :
    (step g s a).2 = 0 ∨ (step g s a).2 = g.R := by
  cases s with
  | dead => exact Or.inl rfl
  | solved c => exact Or.inr rfl
  | ongoing c =>
    simp only [step]
    by_cases h1 : g.isDead (g.place c a)
    · simp [h1]
    · by_cases h2 : g.isSolved (g.place c a)
      · simp [h1, h2]
      · simp [h1, h2]

theorem solve_binary : ∀ n (s : PState Config), solve g s n = 0 ∨ solve g s n = g.R := by
  intro n
  induction n with
  | zero => intro s; exact maxList_binary _ _ _ (fun a _ => reward_binary g s a)
  | succ n ih => intro s; exact maxList_binary _ _ _ (fun a _ => ih _)

theorem solve_le_R (s : PState Config) (n : Nat) : solve g s n ≤ g.R := by
  have := solve_binary g n s
  omega

/-- If the immediate reward is R, the successor's 0-step value is R. -/
theorem step_R_solve0 (s : PState Config) (a : Action)
    (h : (step g s a).2 = g.R) : solve g (step g s a).1 0 = g.R := by
  have hR := g.Rpos
  cases s with
  | dead => simp [step] at h; omega
  | solved c => exact solve_solved g c 0
  | ongoing c =>
    simp only [step] at h ⊢
    by_cases h1 : g.isDead (g.place c a)
    · simp [h1] at h; omega
    · by_cases h2 : g.isSolved (g.place c a)
      · simp [h1, h2]
        exact solve_solved g _ 0
      · simp [h1, h2] at h; omega

theorem solve_mono : ∀ n (s : PState Config),
    solve g s n = g.R → solve g s (n+1) = g.R := by
  intro n
  induction n with
  | zero =>
    intro s h
    obtain ⟨a, ha, hfa⟩ := maxList_R_exists _ _ _ g.Rpos h
    exact maxList_mem_R _ _ _ a ha (step_R_solve0 g s a hfa)
      (fun b _ => solve_le_R g _ 0)
  | succ n ih =>
    intro s h
    obtain ⟨a, ha, hfa⟩ := maxList_R_exists _ _ _ g.Rpos h
    exact maxList_mem_R _ _ _ a ha (ih _ hfa)
      (fun b _ => solve_le_R g _ (n+1))

theorem solve_R_le (s : PState Config) (m n : Nat) (hmn : m ≤ n)
    (h : solve g s m = g.R) : solve g s n = g.R := by
  induction n with
  | zero =>
    have : m = 0 := by omega
    subst this; exact h
  | succ n ih =>
    by_cases hm : m = n + 1
    · subst hm; exact h
    · exact solve_mono g n s (ih (by omega))

theorem solve_zero_le (s : PState Config) (m n : Nat) (hmn : m ≤ n)
    (h : solve g s n = 0) : solve g s m = 0 := by
  have hR := g.Rpos
  rcases solve_binary g m s with h0 | hRm
  · exact h0
  · have := solve_R_le g s m n hmn hRm
    omega

/- ------------------------------------------------------------------ -/
/- Traces and the lexicographic comparison                             -/
/- ------------------------------------------------------------------ -/

def lexLe : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys =>
    if x < y then true
    else if y < x then false
    else lexLe xs ys

theorem lexLe_total : ∀ u v : List Nat, lexLe u v = false → lexLe v u = true := by
  intro u
  induction u with
  | nil => intro v h; simp [lexLe] at h
  | cons x xs ih =>
    intro v h
    cases v with
    | nil => rfl
    | cons y ys =>
      simp only [lexLe] at h ⊢
      by_cases hxy : x < y
      · simp [hxy] at h
      · by_cases hyx : y < x
        · simp [hyx]
        · have hxy' : ¬ y < x := hyx
          simp [hxy, hyx] at h
          simp [hxy', (by omega : ¬ x < y)]
          exact ih ys h

/-- Trace entries are 0 or R up to index j. -/
def BinTo (R : Nat) (t : List Nat) (j : Nat) : Prop :=
  ∀ i, i ≤ j → t.getD i 0 = 0 ∨ t.getD i 0 = R

/-- Once a trace entry is R it stays R, up to index j. -/
def MonoTo (R : Nat) (t : List Nat) (j : Nat) : Prop :=
  ∀ i, i + 1 ≤ j → t.getD i 0 = R → t.getD (i+1) 0 = R

theorem allR_from_head (R : Nat) (t : List Nat) (j : Nat)
    (hh : t.getD 0 0 = R) (hm : MonoTo R t j) : ∀ i, i ≤ j → t.getD i 0 = R := by
  intro i
  induction i with
  | zero => intro _; exact hh
  | succ i ih => intro hij; exact hm i (by omega) (ih (by omega))

/-- The heart of the bridge: for binary monotone traces, lexicographic
comparison implies pointwise comparison. -/
theorem lex_pointwise (R : Nat) :
    ∀ (u v : List Nat) (j : Nat), lexLe u v = true →
    BinTo R u j → BinTo R v j → MonoTo R u j → MonoTo R v j →
    u.getD j 0 ≤ v.getD j 0 := by
  intro u
  induction u with
  | nil =>
    intro v j _ _ _ _ _
    simp [List.getD]
  | cons x xs ih =>
    intro v j hlex hbu hbv hmu hmv
    cases v with
    | nil => simp [lexLe] at hlex
    | cons y ys =>
      simp only [lexLe] at hlex
      by_cases hxy : x < y
      · -- heads differ: x = 0, y = R; monotonicity forces v to be R at j
        have hx0 := hbu 0 (Nat.zero_le _)
        have hy0 := hbv 0 (Nat.zero_le _)
        simp only [List.getD_cons_zero] at hx0 hy0
        have hyR : y = R := by omega
        have hvj : (y :: ys).getD j 0 = R :=
          allR_from_head R (y :: ys) j (by simpa using hyR) hmv j (Nat.le_refl j)
        have huj := hbu j (Nat.le_refl j)
        omega
      · by_cases hyx : y < x
        · simp [hxy, hyx] at hlex
        · -- heads equal: recurse on the tails
          have hxy' : x = y := by omega
          simp [hxy, hyx] at hlex
          cases j with
          | zero => simp only [List.getD_cons_zero]; omega
          | succ j =>
            simp only [List.getD_cons_succ]
            exact ih ys j hlex
              (fun i hi => by have := hbu (i+1) (by omega); simpa using this)
              (fun i hi => by have := hbv (i+1) (by omega); simpa using this)
              (fun i hi h => by
                have := hmu (i+1) (by omega) (by simpa using h); simpa using this)
              (fun i hi h => by
                have := hmv (i+1) (by omega) (by simpa using h); simpa using this)

/- ------------------------------------------------------------------ -/
/- The lexicographic maximum trace                                     -/
/- ------------------------------------------------------------------ -/

def maxTraceAux (t : List Nat) : List (List Nat) → List Nat
  | [] => t
  | u :: us => if lexLe t u then maxTraceAux u us else maxTraceAux t us

def maxTrace : List (List Nat) → List Nat
  | [] => []
  | t :: ts => maxTraceAux t ts

/-- For binary monotone traces, the lex maximum achieves the pointwise
maximum at every position. -/
theorem maxTraceAux_getD (R : Nat) :
    ∀ (ts : List (List Nat)) (t : List Nat) (j : Nat),
    BinTo R t j → MonoTo R t j →
    (∀ u ∈ ts, BinTo R u j ∧ MonoTo R u j) →
    (maxTraceAux t ts).getD j 0 =
      max (t.getD j 0) (maxList (ts.map (fun u => u.getD j 0))) := by
  intro ts
  induction ts with
  | nil =>
    intro t j _ _ _
    simp [maxTraceAux, maxList]
  | cons u us ih =>
    intro t j hbt hmt hall
    obtain ⟨hbu, hmu⟩ := hall u (List.mem_cons_self ..)
    have hus := fun w hw => hall w (List.mem_cons_of_mem _ hw)
    simp only [maxTraceAux, List.map_cons, maxList]
    by_cases hlex : lexLe t u = true
    · have hpt := lex_pointwise R t u j hlex hbt hbu hmt hmu
      simp only [hlex, if_true]
      rw [ih u j hbu hmu hus]
      omega
    · have hlexF : lexLe t u = false := by
        cases h : lexLe t u
        · rfl
        · exact absurd h hlex
      have hlex' : lexLe u t = true := lexLe_total t u hlexF
      have hpt := lex_pointwise R u t j hlex' hbu hbt hmu hmt
      rw [hlexF, if_neg Bool.false_ne_true]
      rw [ih t j hbt hmt hus]
      omega

theorem maxTrace_getD (R : Nat) (ts : List (List Nat)) (j : Nat)
    (hall : ∀ u ∈ ts, BinTo R u j ∧ MonoTo R u j) :
    (maxTrace ts).getD j 0 = maxList (ts.map (fun u => u.getD j 0)) := by
  cases ts with
  | nil => simp [maxTrace, maxList, List.getD]
  | cons t ts =>
    obtain ⟨hbt, hmt⟩ := hall t (List.mem_cons_self ..)
    simp only [maxTrace, List.map_cons, maxList]
    exact maxTraceAux_getD R ts t j hbt hmt
      (fun u hu => hall u (List.mem_cons_of_mem _ hu))

/- ------------------------------------------------------------------ -/
/- Best traces (the Finder's scoring function)                         -/
/- ------------------------------------------------------------------ -/

/-- Best k-step reward trace from a state, with absorbing short-circuits. -/
def bestTrace (g : Game Config Action) : PState Config → Nat → List Nat
  | _, 0 => []
  | .dead, k+1 => 0 :: List.replicate k 0
  | .solved _, k+1 => g.R :: List.replicate k g.R
  | .ongoing c, k+1 =>
    maxTrace (g.actions.map fun a =>
      (step g (.ongoing c) a).2 :: bestTrace g (step g (.ongoing c) a).1 k)

/-- The trace of taking action a: immediate reward, then the best trace. -/
def traceAction (g : Game Config Action) (s : PState Config) (a : Action) (k : Nat) :
    List Nat :=
  (step g s a).2 :: bestTrace g (step g s a).1 k

theorem replicate_getD_zero (k i : Nat) : (List.replicate k (0:Nat)).getD i 0 = 0 := by
  induction k generalizing i with
  | zero => simp [List.getD]
  | succ k ih =>
    cases i with
    | zero => simp [List.replicate]
    | succ i => simpa [List.replicate] using ih i

theorem replicate_getD_R (x k i : Nat) (h : i < k) :
    (List.replicate k x).getD i 0 = x := by
  induction k generalizing i with
  | zero => omega
  | succ k ih =>
    cases i with
    | zero => simp [List.replicate]
    | succ i => simpa [List.replicate] using ih i (by omega)

/-- THE KEY LEMMA: the i-th entry of the best (k+1)-step trace is the
i-step optimal value, for i ≤ k. -/
theorem bestTrace_is_solve :
    ∀ (k : Nat) (s : PState Config) (i : Nat), i ≤ k →
    (bestTrace g s (k+1)).getD i 0 = solve g s i := by
  intro k
  induction k with
  | zero =>
    intro s i hi
    have hi0 : i = 0 := by omega
    subst hi0
    cases s with
    | dead =>
      simp only [bestTrace, List.getD_cons_zero]
      exact (solve_dead g 0).symm
    | solved c =>
      simp only [bestTrace, List.getD_cons_zero]
      exact (solve_solved g c 0).symm
    | ongoing c =>
      simp only [bestTrace]
      rw [maxTrace_getD g.R _ 0 (by
        intro u hu
        obtain ⟨a, _, rfl⟩ := List.mem_map.mp hu
        constructor
        · intro i hi
          have : i = 0 := by omega
          subst this
          simpa using reward_binary g (.ongoing c) a
        · intro i hi; omega)]
      rw [List.map_map]
      show maxList (g.actions.map _) = solve g (.ongoing c) 0
      exact maxList_congr _ _ _ (fun a _ => by simp)
  | succ k ihk =>
    intro s i hi
    cases s with
    | dead =>
      cases i with
      | zero =>
        simp only [bestTrace, List.getD_cons_zero]
        exact (solve_dead g 0).symm
      | succ i =>
        simp only [bestTrace, List.getD_cons_succ]
        rw [replicate_getD_zero]
        exact (solve_dead g (i+1)).symm
    | solved c =>
      cases i with
      | zero =>
        simp only [bestTrace, List.getD_cons_zero]
        exact (solve_solved g c 0).symm
      | succ i =>
        simp only [bestTrace, List.getD_cons_succ]
        rw [replicate_getD_R g.R (k+1) i (by omega)]
        exact (solve_solved g c (i+1)).symm
    | ongoing c =>
      -- binary and monotone structure of the action traces, up to index i
      have hbin : ∀ a, BinTo g.R ((step g (.ongoing c) a).2 ::
          bestTrace g (step g (.ongoing c) a).1 (k+1)) i := by
        intro a i' hi'
        cases i' with
        | zero => simpa using reward_binary g (.ongoing c) a
        | succ i' =>
          simp only [List.getD_cons_succ]
          rw [ihk (step g (.ongoing c) a).1 i' (by omega)]
          exact solve_binary g i' _
      have hmono : ∀ a, MonoTo g.R ((step g (.ongoing c) a).2 ::
          bestTrace g (step g (.ongoing c) a).1 (k+1)) i := by
        intro a i' hi' hR
        cases i' with
        | zero =>
          simp only [List.getD_cons_zero] at hR
          simp only [List.getD_cons_succ]
          rw [ihk (step g (.ongoing c) a).1 0 (by omega)]
          exact step_R_solve0 g (.ongoing c) a hR
        | succ i' =>
          simp only [List.getD_cons_succ] at hR ⊢
          rw [ihk (step g (.ongoing c) a).1 i' (by omega)] at hR
          rw [ihk (step g (.ongoing c) a).1 (i'+1) (by omega)]
          exact solve_mono g i' _ hR
      simp only [bestTrace]
      rw [maxTrace_getD g.R _ i (by
        intro u hu
        obtain ⟨a, _, rfl⟩ := List.mem_map.mp hu
        exact ⟨hbin a, hmono a⟩)]
      rw [List.map_map]
      cases i with
      | zero =>
        show maxList (g.actions.map _) = solve g (.ongoing c) 0
        exact maxList_congr _ _ _ (fun a _ => by simp)
      | succ i =>
        show maxList (g.actions.map _) = solve g (.ongoing c) (i+1)
        refine maxList_congr _ _ _ (fun a _ => ?_)
        simp only [Function.comp]
        rw [List.getD_cons_succ]
        exact ihk (step g (.ongoing c) a).1 i (by omega)

/- ------------------------------------------------------------------ -/
/- The Finder's ranking and the trace bridge                           -/
/- ------------------------------------------------------------------ -/

/-- D18: the Finder's ranking — lexicographic comparison of reward traces
explored to depth horizon+1. -/
def ranks (g : Game Config Action) : Ranking (PState Config) Action :=
  fun s a b => lexLe (traceAction g s a (g.horizon+1)) (traceAction g s b (g.horizon+1)) = true

/-- Binary structure of an action trace, up to index k+1. -/
theorem traceAction_bin (s : PState Config) (a : Action) (k : Nat) :
    BinTo g.R (traceAction g s a (k+1)) (k+1) := by
  intro i hi
  cases i with
  | zero => simpa [traceAction] using reward_binary g s a
  | succ i =>
    simp only [traceAction, List.getD_cons_succ]
    rw [bestTrace_is_solve g k _ i (by omega)]
    exact solve_binary g i _

theorem traceAction_mono (s : PState Config) (a : Action) (k : Nat) :
    MonoTo g.R (traceAction g s a (k+1)) (k+1) := by
  intro i hi hR
  cases i with
  | zero =>
    simp only [traceAction, List.getD_cons_zero] at hR
    simp only [traceAction, List.getD_cons_succ]
    rw [bestTrace_is_solve g k _ 0 (by omega)]
    exact step_R_solve0 g s a hR
  | succ i =>
    simp only [traceAction, List.getD_cons_succ] at hR ⊢
    rw [bestTrace_is_solve g k _ i (by omega)] at hR
    rw [bestTrace_is_solve g k _ (i+1) (by omega)]
    exact solve_mono g i _ hR

/-- Within the horizon: trace ordering gives pointwise solve ordering. -/
theorem trace_to_solve_at (s : PState Config) (a b : Action) (n : Nat)
    (hn : n ≤ g.horizon) (hab : ranks g s a b) :
    solve g (step g s a).1 n ≤ solve g (step g s b).1 n := by
  have hpt := lex_pointwise g.R
    (traceAction g s a (g.horizon+1)) (traceAction g s b (g.horizon+1)) (n+1)
    hab
    (fun i hi => traceAction_bin g s a g.horizon i (by omega))
    (fun i hi => traceAction_bin g s b g.horizon i (by omega))
    (fun i hi => traceAction_mono g s a g.horizon i (by omega))
    (fun i hi => traceAction_mono g s b g.horizon i (by omega))
  simp only [traceAction, List.getD_cons_succ] at hpt
  rwa [bestTrace_is_solve g g.horizon _ n hn,
       bestTrace_is_solve g g.horizon _ n hn] at hpt

/-- Horizon sufficiency: the domain-specific termination property.  If an
ongoing state's value at the horizon is 0, it is 0 at every depth. -/
def HorizonSuf (g : Game Config Action) : Prop :=
  ∀ c, solve g (.ongoing c) g.horizon = 0 → ∀ n, solve g (.ongoing c) n = 0

/-- Above the horizon: solve is determined by its value at the horizon. -/
theorem trace_to_solve_above (hsuf : HorizonSuf g)
    (s : PState Config) (a b : Action) (n : Nat)
    (hn : g.horizon < n) (hab : ranks g s a b) :
    solve g (step g s a).1 n ≤ solve g (step g s b).1 n := by
  have hR := g.Rpos
  have hH := trace_to_solve_at g s a b g.horizon (Nat.le_refl _) hab
  rcases solve_binary g n (step g s a).1 with h0 | hRn
  · omega
  · -- solve at n is R; show solve at horizon is R too
    have haH : solve g (step g s a).1 g.horizon = g.R := by
      rcases solve_binary g g.horizon (step g s a).1 with h0 | hRH
      · -- horizon value 0: dead/solved cases are immediate; ongoing uses hsuf
        exfalso
        cases hsa : (step g s a).1 with
        | dead => rw [hsa, solve_dead g n] at hRn; omega
        | solved c => rw [hsa, solve_solved g c g.horizon] at h0; omega
        | ongoing c =>
          rw [hsa] at h0 hRn
          rw [hsuf c h0 n] at hRn
          omega
      · exact hRH
    have hbH : solve g (step g s b).1 g.horizon = g.R := by
      have := solve_le_R g (step g s b).1 g.horizon
      omega
    have hbn : solve g (step g s b).1 n = g.R := by
      cases hsb : (step g s b).1 with
      | dead => rw [hsb, solve_dead g g.horizon] at hbH; omega
      | solved c => exact solve_solved g c n
      | ongoing c =>
        rw [hsb] at hbH
        exact solve_R_le g _ g.horizon n (by omega) hbH
    omega

/-- T13: THE TRACE BRIDGE.  The Finder's lexicographic trace ranking is a
CoindHomo: it preserves dominance of the full action-value streams, at
every state of any placement game with the horizon-sufficiency property. -/
theorem placement_coindhomo (hsuf : HorizonSuf g) (s : PState Config) :
    CoindHomo Nat.le (pnext g) (preward g) (pvalue g) (ranks g) s := by
  intro a b hab n
  cases n with
  | zero =>
    -- head: immediate rewards, index 0 of the traces
    have hpt := lex_pointwise g.R
      (traceAction g s a (g.horizon+1)) (traceAction g s b (g.horizon+1)) 0
      hab
      (fun i hi => traceAction_bin g s a g.horizon i (by omega))
      (fun i hi => traceAction_bin g s b g.horizon i (by omega))
      (fun i hi => traceAction_mono g s a g.horizon i (by omega))
      (fun i hi => traceAction_mono g s b g.horizon i (by omega))
    simpa [traceAction, qvalue, Stream'.cons, preward] using hpt
  | succ n =>
    show solve g (step g s a).1 n ≤ solve g (step g s b).1 n
    by_cases hn : n ≤ g.horizon
    · exact trace_to_solve_at g s a b n hn hab
    · exact trace_to_solve_above g hsuf s a b n (by omega) hab

/- ------------------------------------------------------------------ -/
/- Sized games: horizon sufficiency for free                           -/
/- ------------------------------------------------------------------ -/

/-- A placement game with a size measure: placement increases the size by
one, and solving means exactly reaching the horizon.  Covers N-Queens,
Sudoku, and any fill-all-slots puzzle. -/
structure SizedGame (Config Action : Type) extends Game Config Action where
  size       : Config → Nat
  place_size : ∀ c a, size (place c a) = size c + 1
  solved_iff : ∀ c, isSolved c = (size c == horizon)

variable {sg : SizedGame Config Action}

theorem sized_not_solved (sg : SizedGame Config Action) (c : Config) (a : Action)
    (h : sg.horizon ≤ sg.size c) : sg.isSolved (sg.place c a) = false := by
  rw [sg.solved_iff, sg.place_size]
  simp only [beq_eq_false_iff_ne, ne_eq]
  omega

/-- When the size budget is exhausted, solve is identically 0. -/
theorem sized_solve0 (sg : SizedGame Config Action) :
    ∀ n (c : Config), sg.horizon ≤ sg.size c →
    solve sg.toGame (.ongoing c) n = 0 := by
  intro n
  induction n with
  | zero =>
    intro c hc
    refine maxList_all_zero _ _ (fun a _ => ?_)
    simp only [step]
    by_cases h1 : sg.isDead (sg.place c a)
    · simp [h1]
    · simp [h1, sized_not_solved sg c a hc]
  | succ n ih =>
    intro c hc
    refine maxList_all_zero _ _ (fun a _ => ?_)
    simp only [step]
    by_cases h1 : sg.isDead (sg.place c a)
    · simp [h1, solve_dead]
    · simp only [h1, if_false, sized_not_solved sg c a hc, if_false]
      exact ih (sg.place c a) (by rw [sg.place_size]; omega)

/-- If solve is 0 at depth m+1, each successor's solve is 0 at depth m. -/
theorem solve_component_zero (s : PState Config) (m : Nat)
    (h : solve g s (m+1) = 0) :
    ∀ a ∈ g.actions, solve g (step g s a).1 m = 0 := by
  intro a ha
  have hR := g.Rpos
  rcases solve_binary g m (step g s a).1 with h0 | hRm
  · exact h0
  · exfalso
    have : maxList (g.actions.map fun a => solve g (step g s a).1 m) = g.R :=
      maxList_mem_R _ _ _ a ha hRm (fun b _ => solve_le_R g _ m)
    have hh : solve g s (m+1) = g.R := this
    omega

/-- Fuel induction: solve 0 at the remaining-budget depth forces solve 0
at every depth. -/
theorem sized_shs (sg : SizedGame Config Action) :
    ∀ (fuel : Nat) (c : Config), fuel = sg.horizon - sg.size c →
    solve sg.toGame (.ongoing c) fuel = 0 →
    ∀ n, solve sg.toGame (.ongoing c) n = 0 := by
  intro fuel
  induction fuel with
  | zero =>
    intro c hf _ n
    exact sized_solve0 sg n c (by omega)
  | succ fuel ih =>
    intro c hf hq n
    have hcomp := solve_component_zero sg.toGame (.ongoing c) fuel hq
    cases n with
    | zero => exact solve_zero_le sg.toGame _ 0 (fuel+1) (by omega) hq
    | succ n =>
      refine maxList_all_zero _ _ (fun a ha => ?_)
      have hca := hcomp a ha
      have hR := sg.Rpos
      -- case on the successor of (ongoing c, a)
      simp only [step] at hca ⊢
      by_cases h1 : sg.isDead (sg.place c a)
      · simp [h1, solve_dead]
      · by_cases h2 : sg.isSolved (sg.place c a)
        · -- solved successor contradicts solve = 0 at depth fuel
          exfalso
          simp [h1, h2, solve_solved] at hca
          omega
        · simp [h1, h2] at hca ⊢
          have hsz : sg.size (sg.place c a) = sg.size c + 1 := sg.place_size c a
          exact ih (sg.place c a) (by omega) hca n

/-- Sized games satisfy horizon sufficiency with no extra obligations. -/
theorem sized_horizon_suf (sg : SizedGame Config Action) : HorizonSuf sg.toGame := by
  intro c h n
  refine sized_shs sg (sg.horizon - sg.size c) c rfl ?_ n
  exact solve_zero_le sg.toGame _ _ sg.horizon (by omega) h

/-- T13 for sized games: the Finder's trace ranking is a CoindHomo, with the
termination obligation discharged generically. -/
theorem sized_coindhomo (sg : SizedGame Config Action) (s : PState Config) :
    CoindHomo Nat.le (pnext sg.toGame) (preward sg.toGame) (pvalue sg.toGame)
      (ranks sg.toGame) s :=
  placement_coindhomo sg.toGame (sized_horizon_suf sg) s

/- ------------------------------------------------------------------ -/
/- The Finder's policy (executable)                                    -/
/- ------------------------------------------------------------------ -/

/-- Pick the lex-greatest action trace (first maximum wins). -/
def findPolicy (g : Game Config Action) (s : PState Config) (k : Nat) : Option Action :=
  match g.actions with
  | [] => none
  | a :: rest =>
    some (rest.foldl (fun best x =>
      if lexLe (traceAction g s best k) (traceAction g s x k) then x else best) a)

/-- Roll out the Finder's policy for n steps. -/
def runPolicy (g : Game Config Action) : PState Config → Nat → Nat → List Action
  | _, _, 0 => []
  | s, depth, n+1 =>
    match findPolicy g s depth with
    | none => []
    | some a => a :: runPolicy g (step g s a).1 depth n

end Placement
end CSHRL
