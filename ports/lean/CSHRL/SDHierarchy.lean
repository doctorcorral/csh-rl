/-
CSHRL portability kernel, Lean 4 port.
D14, T9: FOSD and the stochastic dominance hierarchy (Agda references
src/CSHRL/Probability/FOSD.agda, SD.agda, Compose.agda).

FOSD:  mu FOSD≤ nu iff every CDF value of nu is below mu's (preferred by
ALL monotone utility functions).
SD[k]: k-fold iterated prefix sums of the CDF; SD[0] = FOSD, SD[1] = SOSD
(risk-averse agents), SD[2] = TOSD, ...

T9a (hierarchy): SD[k] implies SD[k+1] — prefix sums preserve pointwise
dominance, so each level subsumes the previous one.
T9b (closure): FOSD and every SD[k] are closed under mixture (++) and
reward scaling; sdWeight is a linear operator.
-/

import CSHRL.Dist

namespace CSHRL

/-- D14a: first-order stochastic dominance. -/
def FOSDle (mu nu : Dist Nat) : Prop :=
  ∀ r, cdfWeight nu r ≤ cdfWeight mu r

theorem FOSD_refl (d : Dist Nat) : FOSDle d d := fun _ => Nat.le_refl _

theorem FOSD_trans {a b c : Dist Nat} (h1 : FOSDle a b) (h2 : FOSDle b c) :
    FOSDle a c :=
  fun r => Nat.le_trans (h2 r) (h1 r)

/-- D14b: iterated prefix sums and the SD[k] hierarchy. -/
def prefixSum (f : Nat → Nat) : Nat → Nat
  | 0 => f 0
  | r + 1 => f (r + 1) + prefixSum f r

def sdWeight : Nat → Dist Nat → Nat → Nat
  | 0, d => cdfWeight d
  | k + 1, d => prefixSum (sdWeight k d)

def SDle (k : Nat) (mu nu : Dist Nat) : Prop :=
  ∀ r, sdWeight k nu r ≤ sdWeight k mu r

/-- SD[0] is definitionally FOSD. -/
theorem SD0_FOSD (mu nu : Dist Nat) : SDle 0 mu nu ↔ FOSDle mu nu :=
  Iff.rfl

theorem SD_refl (k : Nat) (d : Dist Nat) : SDle k d d := fun _ => Nat.le_refl _

theorem SD_trans {k : Nat} {a b c : Dist Nat}
    (h1 : SDle k a b) (h2 : SDle k b c) : SDle k a c :=
  fun r => Nat.le_trans (h2 r) (h1 r)

/-- Prefix sums preserve pointwise dominance. -/
theorem prefixSum_mono {f g : Nat → Nat} (h : ∀ r, f r ≤ g r) :
    ∀ r, prefixSum f r ≤ prefixSum g r
  | 0 => h 0
  | r + 1 => Nat.add_le_add (h (r + 1)) (prefixSum_mono h r)

/-- T9a: the hierarchy.  Verified at level k, verified at level k+1. -/
theorem SD_subsumes (k : Nat) {mu nu : Dist Nat} (h : SDle k mu nu) :
    SDle (k + 1) mu nu :=
  fun r => prefixSum_mono h r

theorem SD_subsumes_n (k j : Nat) {mu nu : Dist Nat} (h : SDle k mu nu) :
    SDle (k + j) mu nu := by
  induction j with
  | zero => exact h
  | succ j ih => exact SD_subsumes (k + j) ih

/-- Linearity of prefixSum, hence of sdWeight. -/
theorem prefixSum_ext {f g : Nat → Nat} (h : ∀ r, f r = g r) :
    ∀ r, prefixSum f r = prefixSum g r
  | 0 => h 0
  | r + 1 => by rw [prefixSum, prefixSum, h (r + 1), prefixSum_ext h r]

theorem prefixSum_add (f g : Nat → Nat) :
    ∀ r, prefixSum (fun t => f t + g t) r = prefixSum f r + prefixSum g r
  | 0 => rfl
  | r + 1 => by
    show f (r + 1) + g (r + 1) + prefixSum (fun t => f t + g t) r = _
    rw [prefixSum_add f g r]
    show _ = f (r + 1) + prefixSum f r + (g (r + 1) + prefixSum g r)
    omega

theorem prefixSum_mul (c : Nat) (f : Nat → Nat) :
    ∀ r, prefixSum (fun t => c * f t) r = c * prefixSum f r
  | 0 => rfl
  | r + 1 => by
    show c * f (r + 1) + prefixSum (fun t => c * f t) r = _
    rw [prefixSum_mul c f r]
    show _ = c * (f (r + 1) + prefixSum f r)
    rw [Nat.mul_add]

theorem sdWeight_append :
    ∀ (k : Nat) (d1 d2 : Dist Nat) (r : Nat),
      sdWeight k (d1 ++ d2) r = sdWeight k d1 r + sdWeight k d2 r
  | 0, d1, d2, r => cdfWeight_append d1 d2 r
  | k + 1, d1, d2, r => by
    show prefixSum (sdWeight k (d1 ++ d2)) r = _
    rw [prefixSum_ext (fun t => sdWeight_append k d1 d2 t) r]
    exact prefixSum_add (sdWeight k d1) (sdWeight k d2) r

theorem sdWeight_scale :
    ∀ (k : Nat) (d : Dist Nat) (r c : Nat),
      sdWeight k (dscale c d) r = c * sdWeight k d r
  | 0, d, r, c => cdfWeight_scale d r c
  | k + 1, d, r, c => by
    show prefixSum (sdWeight k (dscale c d)) r = _
    rw [prefixSum_ext (fun t => sdWeight_scale k d t c) r]
    exact prefixSum_mul c (sdWeight k d) r

/-- T9b: closure of the whole hierarchy under mixture and scaling. -/
theorem FOSD_append {mu1 nu1 mu2 nu2 : Dist Nat}
    (h1 : FOSDle mu1 nu1) (h2 : FOSDle mu2 nu2) :
    FOSDle (mu1 ++ mu2) (nu1 ++ nu2) := by
  intro r
  rw [cdfWeight_append, cdfWeight_append]
  exact Nat.add_le_add (h1 r) (h2 r)

theorem FOSD_scale (k : Nat) {mu nu : Dist Nat} (h : FOSDle mu nu) :
    FOSDle (dscale k mu) (dscale k nu) := by
  intro r
  rw [cdfWeight_scale, cdfWeight_scale]
  exact Nat.mul_le_mul_left k (h r)

theorem SD_append (k : Nat) {mu1 nu1 mu2 nu2 : Dist Nat}
    (h1 : SDle k mu1 nu1) (h2 : SDle k mu2 nu2) :
    SDle k (mu1 ++ mu2) (nu1 ++ nu2) := by
  intro r
  rw [sdWeight_append, sdWeight_append]
  exact Nat.add_le_add (h1 r) (h2 r)

theorem SD_scale (k c : Nat) {mu nu : Dist Nat} (h : SDle k mu nu) :
    SDle k (dscale c mu) (dscale c nu) := by
  intro r
  rw [sdWeight_scale, sdWeight_scale]
  exact Nat.mul_le_mul_left c (h r)

end CSHRL
