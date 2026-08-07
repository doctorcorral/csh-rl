/-
CSHRL portability kernel, Lean 4 port.
D12: finite discrete distributions as weighted lists (the finite
distribution monad underlying the stochastic extension, Agda reference
src/CSHRL/Probability/Finite.agda).

Weights are unnormalized naturals for decidability.  This file also
provides the CDF machinery (cdfWeight) that FOSD and the SD hierarchy are
built on, with its two distributivity laws (concatenation and scaling).
-/

namespace CSHRL

abbrev Dist (A : Type) : Type := List (A × Nat)

def dpure {A : Type} (a : A) : Dist A := [(a, 1)]

def dscale {A : Type} (k : Nat) (d : Dist A) : Dist A :=
  d.map (fun aw => (aw.1, k * aw.2))

def dmap {A B : Type} (f : A → B) (d : Dist A) : Dist B :=
  d.map (fun aw => (f aw.1, aw.2))

def dbind {A B : Type} : Dist A → (A → Dist B) → Dist B
  | [], _ => []
  | (a, w) :: rest, f => dscale w (f a) ++ dbind rest f

def totalWeight {A : Type} : Dist A → Nat
  | [] => 0
  | (_, w) :: rest => w + totalWeight rest

def weightedSum : Dist Nat → Nat
  | [] => 0
  | (v, w) :: rest => v * w + weightedSum rest

/-- CDF: total weight of outcomes ≤ r. -/
def cdfWeight : Dist Nat → Nat → Nat
  | [], _ => 0
  | (v, w) :: rest, r => (if v ≤ r then w else 0) + cdfWeight rest r

@[simp] theorem dmap_nil {A B : Type} (f : A → B) : dmap f ([] : Dist A) = [] := rfl

@[simp] theorem dmap_cons {A B : Type} (f : A → B) (a : A) (w : Nat) (d : Dist A) :
    dmap f ((a, w) :: d) = (f a, w) :: dmap f d := rfl

@[simp] theorem cdfWeight_nil (r : Nat) : cdfWeight [] r = 0 := rfl

@[simp] theorem cdfWeight_cons (v w : Nat) (d : Dist Nat) (r : Nat) :
    cdfWeight ((v, w) :: d) r = (if v ≤ r then w else 0) + cdfWeight d r := rfl

/-- Distributivity over concatenation (mixture). -/
theorem cdfWeight_append (d1 d2 : Dist Nat) (r : Nat) :
    cdfWeight (d1 ++ d2) r = cdfWeight d1 r + cdfWeight d2 r := by
  induction d1 with
  | nil => simp [cdfWeight]
  | cons a d1 ih =>
    obtain ⟨v, w⟩ := a
    simp [cdfWeight, ih]
    omega

theorem totalWeight_append {A : Type} (d1 d2 : Dist A) :
    totalWeight (d1 ++ d2) = totalWeight d1 + totalWeight d2 := by
  induction d1 with
  | nil => simp [totalWeight]
  | cons a d1 ih =>
    obtain ⟨v, w⟩ := a
    simp [totalWeight, ih]
    omega

/-- Distributivity over scaling (reward amplification). -/
theorem cdfWeight_scale (d : Dist Nat) (r k : Nat) :
    cdfWeight (dscale k d) r = k * cdfWeight d r := by
  induction d with
  | nil => simp [dscale, cdfWeight]
  | cons a d ih =>
    obtain ⟨v, w⟩ := a
    by_cases h : v ≤ r <;> simp [dscale, cdfWeight, h, ih] at * <;>
      simp [Nat.mul_add, ih]

theorem totalWeight_scale {A : Type} (d : Dist A) (k : Nat) :
    totalWeight (dscale k d) = k * totalWeight d := by
  induction d with
  | nil => simp [dscale, totalWeight]
  | cons a d ih =>
    obtain ⟨v, w⟩ := a
    simp [dscale, totalWeight] at *
    simp [ih, Nat.mul_add]

end CSHRL
