/-
CSHRL portability kernel, Lean 4 port.
T7: closed convergence of swap-based learning (paper section 14).

This closes the statement that is an assumption record in the Agda reference
(ViolationMonotonicityTheorem in Learning/Base.agda): each violation repair
strictly decreases the total violation count, so the learner converges to a
ranking that realizes the oracle on EVERY pair in at most C(n,2) repairs per
state.

Setting: an explicit ranking is a list of actions, best first, at one state.
The oracle is the ground-truth comparator (`oracle a b = true` means a ≤ b).
A pair (x before y) is violated when the oracle denies y ≤ x.  The repair is
an ADJACENT transposition — the generator set of the symmetric group,
matching the paper's narrative that learning walks Sₙ by transpositions.

Results, all closed (no assumption records):
- `swap_adjacent_decreases`: an adjacent repair decreases the violation
  count by EXACTLY one (needs only totality of the oracle);
- `fixFirst_progress`: the first-violation repair either certifies zero
  violations or strictly decreases them (needs transitivity);
- `swap_convergence` / `swap_convergence_bound`: iterating the repair
  reaches zero violations within violations(xs) ≤ C(length xs, 2) steps;
- `violations_zero_iff`: zero violations means the ranking realizes the
  oracle on every ordered pair — the homomorphism property at this state.
-/

namespace CSHRL

variable {Action : Type}

section Convergence

variable (oracle : Action → Action → Bool)

/-- Violations of x against the actions ranked after it. -/
def violWith (x : Action) : List Action → Nat
  | [] => 0
  | y :: ys => (if oracle y x then 0 else 1) + violWith x ys

/-- Total violations of a ranking list (sum over all ordered pairs). -/
def violations : List Action → Nat
  | [] => 0
  | x :: xs => violWith oracle x xs + violations xs

/-- violWith only sees the multiset of later actions. -/
theorem violWith_swap (p x y : Action) (pre post : List Action) :
    violWith oracle p (pre ++ x :: y :: post)
      = violWith oracle p (pre ++ y :: x :: post) := by
  induction pre with
  | nil => simp [violWith, Nat.add_left_comm]
  | cons a pre ih => simp [violWith, ih]

/-- T7a: an adjacent repair decreases violations by exactly one. -/
theorem swap_adjacent_decreases (pre : List Action) (x y : Action)
    (post : List Action) (hyx : oracle y x = false) (hxy : oracle x y = true) :
    violations oracle (pre ++ x :: y :: post)
      = violations oracle (pre ++ y :: x :: post) + 1 := by
  induction pre with
  | nil => simp [violations, violWith, hyx, hxy]; omega
  | cons a pre ih =>
    simp only [List.cons_append, violations]
    rw [ih, violWith_swap]
    omega

/-- Transitivity propagates zero-violation certificates down the list. -/
theorem violWith_mono
    (htrans : ∀ a b c, oracle a b = true → oracle b c = true → oracle a c = true)
    (x y : Action) (rest : List Action)
    (hyx : oracle y x = true) (h : violWith oracle y rest = 0) :
    violWith oracle x rest = 0 := by
  induction rest with
  | nil => rfl
  | cons z r ih =>
    cases E : oracle z y with
    | false => simp [violWith, E] at h
    | true =>
      simp [violWith, E] at h
      simp [violWith, htrans z y x E hyx]
      exact ih h

/-- The repair function: fix the first adjacent violation. -/
def fixFirst : List Action → List Action
  | x :: y :: rest =>
    if oracle y x then x :: fixFirst (y :: rest) else y :: x :: rest
  | xs => xs

/-- violWith is invariant under the repair (it permutes the list). -/
theorem violWith_fixFirst (p : Action) :
    ∀ t : List Action, violWith oracle p (fixFirst oracle t) = violWith oracle p t
  | [] => rfl
  | [_] => rfl
  | x :: y :: rest => by
    cases E : oracle y x with
    | true => simp [fixFirst, E, violWith, violWith_fixFirst p (y :: rest)]
    | false => simp [fixFirst, E, violWith, Nat.add_left_comm]

/-- T7b: the repair either certifies zero violations or strictly decreases
the count. -/
theorem fixFirst_progress
    (htotal : ∀ a b, oracle a b = true ∨ oracle b a = true)
    (htrans : ∀ a b c, oracle a b = true → oracle b c = true → oracle a c = true) :
    ∀ xs : List Action,
      violations oracle xs = violations oracle (fixFirst oracle xs) + 1
      ∨ (fixFirst oracle xs = xs ∧ violations oracle xs = 0)
  | [] => .inr ⟨rfl, rfl⟩
  | [_] => .inr ⟨rfl, rfl⟩
  | x :: y :: rest => by
    cases E : oracle y x with
    | true =>
      rcases fixFirst_progress htotal htrans (y :: rest) with hdec | ⟨hfix, hzero⟩
      · left
        simp only [fixFirst, E, if_pos, violations]
        rw [violWith_fixFirst]
        have hd : violWith oracle y rest + violations oracle rest
            = violations oracle (fixFirst oracle (y :: rest)) + 1 := hdec
        omega
      · right
        constructor
        · simp [fixFirst, E, hfix]
        · have h0 : violWith oracle y rest + violations oracle rest = 0 := by
            simpa [violations] using hzero
          have hy : violWith oracle y rest = 0 := by omega
          have hr : violations oracle rest = 0 := by omega
          have hx : violWith oracle x rest = 0 := violWith_mono oracle htrans x y rest E hy
          simp [violations, violWith, E, hx, hy, hr]
    | false =>
      left
      have hxy : oracle x y = true := by
        rcases htotal x y with h | h
        · exact h
        · rw [h] at E; cases E
      have hswap := swap_adjacent_decreases oracle [] x y rest E hxy
      simp only [List.nil_append] at hswap
      simp [fixFirst, E]
      omega

/-- The learner: iterate the repair. -/
def learn : Nat → List Action → List Action
  | 0, xs => xs
  | k + 1, xs => learn k (fixFirst oracle xs)

theorem learn_fuel
    (htotal : ∀ a b, oracle a b = true ∨ oracle b a = true)
    (htrans : ∀ a b c, oracle a b = true → oracle b c = true → oracle a c = true) :
    ∀ (n : Nat) (xs : List Action),
      violations oracle xs ≤ n → violations oracle (learn oracle n xs) = 0
  | 0, xs, h => Nat.le_zero.mp h
  | k + 1, xs, h => by
    rcases fixFirst_progress oracle htotal htrans xs with hdec | ⟨hfix, hzero⟩
    · exact learn_fuel htotal htrans k (fixFirst oracle xs) (by omega)
    · show violations oracle (learn oracle k (fixFirst oracle xs)) = 0
      rw [hfix]
      exact learn_fuel htotal htrans k xs (by omega)

/-- T7c: convergence within the initial violation count. -/
theorem swap_convergence
    (htotal : ∀ a b, oracle a b = true ∨ oracle b a = true)
    (htrans : ∀ a b c, oracle a b = true → oracle b c = true → oracle a c = true)
    (xs : List Action) :
    violations oracle (learn oracle (violations oracle xs) xs) = 0 :=
  learn_fuel oracle htotal htrans _ xs (Nat.le_refl _)

/-- The combinatorial bound C(n, 2). -/
def pairs : Nat → Nat
  | 0 => 0
  | k + 1 => k + pairs k

theorem violWith_bound (x : Action) :
    ∀ ys : List Action, violWith oracle x ys ≤ ys.length
  | [] => Nat.le_refl 0
  | z :: r => by
    have ih := violWith_bound x r
    cases E : oracle z x <;> simp [violWith, E] <;> omega

theorem violations_bound :
    ∀ xs : List Action, violations oracle xs ≤ pairs xs.length
  | [] => Nat.le_refl 0
  | x :: xs => by
    have h1 := violWith_bound oracle x xs
    have h2 := violations_bound xs
    simp [violations, pairs]
    omega

/-- T7d: C(n,2) repairs always suffice. -/
theorem swap_convergence_bound
    (htotal : ∀ a b, oracle a b = true ∨ oracle b a = true)
    (htrans : ∀ a b c, oracle a b = true → oracle b c = true → oracle a c = true)
    (xs : List Action) :
    violations oracle (learn oracle (pairs xs.length) xs) = 0 :=
  learn_fuel oracle htotal htrans _ xs (violations_bound oracle xs)

/-- Zero violations semantics: the ranking realizes the oracle on every
ordered pair — the homomorphism property at this state. -/
def allPairsCorrect : List Action → Prop
  | [] => True
  | x :: xs => (∀ y, y ∈ xs → oracle y x = true) ∧ allPairsCorrect xs

theorem violWith_zero_iff (x : Action) :
    ∀ ys : List Action,
      (violWith oracle x ys = 0 ↔ ∀ y, y ∈ ys → oracle y x = true)
  | [] => by simp [violWith]
  | z :: r => by
    have ih := violWith_zero_iff x r
    cases E : oracle z x with
    | true => simp [violWith, E, ih]
    | false =>
      simp only [violWith, E, if_neg Bool.false_ne_true]
      constructor
      · intro h; omega
      · intro h
        have := h z (List.mem_cons_self ..)
        rw [this] at E; cases E

/-- T7e: zero violations = full pairwise realization of the oracle. -/
theorem violations_zero_iff :
    ∀ xs : List Action,
      (violations oracle xs = 0 ↔ allPairsCorrect oracle xs)
  | [] => by simp [violations, allPairsCorrect]
  | x :: xs => by
    have h1 := violWith_zero_iff oracle x xs
    have h2 := violations_zero_iff xs
    constructor
    · intro h
      have h0 : violWith oracle x xs + violations oracle xs = 0 := by
        simpa [violations] using h
      exact ⟨h1.mp (by omega), h2.mp (by omega)⟩
    · rintro ⟨hall, hrest⟩
      simp [violations, h1.mpr hall, h2.mpr hrest]

/-- The headline corollary: the learner reaches a ranking that realizes the
oracle on every pair, within C(n,2) repairs. -/
theorem learn_realizes_oracle
    (htotal : ∀ a b, oracle a b = true ∨ oracle b a = true)
    (htrans : ∀ a b c, oracle a b = true → oracle b c = true → oracle a c = true)
    (xs : List Action) :
    allPairsCorrect oracle (learn oracle (pairs xs.length) xs) :=
  (violations_zero_iff oracle _).mp (swap_convergence_bound oracle htotal htrans xs)

end Convergence

end CSHRL
