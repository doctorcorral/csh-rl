/-
CSHRL portability kernel, Lean 4 port.
T10: FOSD and SD[k] are closed under convolution (independent sum), the
composition law for product MDPs with additive rewards (Agda reference
src/CSHRL/Probability/Convolution.agda).

Proof structure (discrete Abel summation):
1. the CDF of a convolution decomposes as a generalized weighted sum
   (gws) over the first distribution, of shifted CDFs of the second;
2. kernel direction: gws is monotone in the summand (gws_mono);
3. base direction: FOSD implies gws dominance for every non-increasing
   eventually-zero summand, by induction on the support bound (gws_split
   peels off the last level: Abel's identity);
4. FOSD_conv chains both directions; FOSD_SD_conv lifts the result to the
   whole hierarchy.
-/

import CSHRL.SDHierarchy

namespace CSHRL

/-- Convolution: independent sum of two distributions. -/
def conv (d1 d2 : Dist Nat) : Dist Nat :=
  dbind d1 (fun v => dmap (fun u => v + u) d2)

/-- Generalized weighted sum: sum over (v, w) in d of w * h v. -/
def gws : Dist Nat → (Nat → Nat) → Nat
  | [], _ => 0
  | (v, w) :: rest, h => w * h v + gws rest h

/-- The CDF of a convolution decomposes as a gws of shifted CDFs. -/
theorem cdf_conv :
    ∀ (d1 d2 : Dist Nat) (r : Nat),
      cdfWeight (conv d1 d2) r
      = gws d1 (fun v => cdfWeight (dmap (fun u => v + u) d2) r)
  | [], _, _ => rfl
  | (v, w) :: d1, d2, r => by
    show cdfWeight (dscale w (dmap (fun u => v + u) d2) ++ conv d1 d2) r = _
    rw [cdfWeight_append, cdfWeight_scale, cdf_conv d1 d2 r]
    rfl

/-- Kernel direction: gws is monotone in the summand. -/
theorem gws_mono :
    ∀ (d : Dist Nat) {h1 h2 : Nat → Nat},
      (∀ v, h1 v ≤ h2 v) → gws d h1 ≤ gws d h2
  | [], _, _, _ => Nat.le_refl 0
  | (v, w) :: d, h1, h2, h => by
    show w * h1 v + gws d h1 ≤ w * h2 v + gws d h2
    exact Nat.add_le_add (Nat.mul_le_mul_left w (h v)) (gws_mono d h)

/-- Shifted CDFs. -/
theorem cdf_dmap_add (k : Nat) :
    ∀ (d : Dist Nat) (r : Nat), k ≤ r →
      cdfWeight (dmap (fun u => k + u) d) r = cdfWeight d (r - k)
  | [], _, _ => rfl
  | (u, w) :: d, r, hkr => by
    rw [dmap_cons, cdfWeight_cons, cdfWeight_cons, cdf_dmap_add k d r hkr]
    have : (k + u ≤ r) ↔ (u ≤ r - k) := by omega
    by_cases h : u ≤ r - k
    · rw [if_pos h, if_pos (this.mpr h)]
    · rw [if_neg h, if_neg (fun hh => h (this.mp hh))]

theorem cdf_dmap_zero (k : Nat) :
    ∀ (d : Dist Nat) (r : Nat), r < k →
      cdfWeight (dmap (fun u => k + u) d) r = 0
  | [], _, _ => rfl
  | (u, w) :: d, r, hrk => by
    rw [dmap_cons, cdfWeight_cons, cdf_dmap_zero k d r hrk,
        if_neg (by omega : ¬ k + u ≤ r)]

/-- FOSD is preserved by shifting. -/
theorem FOSD_shift (k : Nat) {mu nu : Dist Nat} (h : FOSDle mu nu) :
    FOSDle (dmap (fun u => k + u) mu) (dmap (fun u => k + u) nu) := by
  intro r
  by_cases hkr : k ≤ r
  · rw [cdf_dmap_add k mu r hkr, cdf_dmap_add k nu r hkr]
    exact h (r - k)
  · rw [cdf_dmap_zero k mu r (by omega), cdf_dmap_zero k nu r (by omega)]
    exact Nat.le_refl 0

/-- The shifted CDF is non-increasing in the shift and eventually zero. -/
theorem shift_cdf_mono :
    ∀ (d : Dist Nat) (v r : Nat),
      cdfWeight (dmap (fun u => v + 1 + u) d) r
      ≤ cdfWeight (dmap (fun u => v + u) d) r
  | [], _, _ => Nat.le_refl 0
  | (u, w) :: d, v, r => by
    rw [dmap_cons, dmap_cons, cdfWeight_cons, cdfWeight_cons]
    have ih := shift_cdf_mono d v r
    by_cases h1 : v + 1 + u ≤ r <;> by_cases h2 : v + u ≤ r <;>
      simp [h1, h2] <;> omega

theorem shift_cdf_zero (d : Dist Nat) (r : Nat) :
    cdfWeight (dmap (fun u => r + 1 + u) d) r = 0 :=
  cdf_dmap_zero (r + 1) d r (by omega)

/-- Non-increasing summands vanish beyond their support bound. -/
theorem h_vanish (h : Nat → Nat) (mono : ∀ v, h (v + 1) ≤ h v)
    (M : Nat) (h0 : h M = 0) : ∀ n, h (n + M) = 0
  | 0 => by rw [Nat.zero_add]; exact h0
  | n + 1 => by
    have h1 := mono (n + M)
    have h2 := h_vanish h mono M h0 n
    rw [(by omega : n + 1 + M = n + M + 1)]
    omega

theorem mono_chain (h : Nat → Nat) (mono : ∀ v, h (v + 1) ≤ h v) :
    ∀ m n, h (m + n) ≤ h n
  | 0, n => by rw [Nat.zero_add]; exact Nat.le_refl _
  | m + 1, n => by
    have h1 := mono (m + n)
    have h2 := mono_chain h mono m n
    rw [(by omega : m + 1 + n = m + n + 1)]
    omega

/-- Base of the Abel induction: h nonzero only at 0. -/
theorem gws_base :
    ∀ (d : Dist Nat) (h : Nat → Nat),
      (∀ v, h (v + 1) ≤ h v) → h 1 = 0 →
      gws d h = h 0 * cdfWeight d 0
  | [], h, _, _ => by simp [gws, cdfWeight]
  | (v, w) :: d, h, mono, h1 => by
    rw [gws, gws_base d h mono h1, cdfWeight_cons]
    match v with
    | 0 =>
      rw [if_pos (Nat.le_refl 0), Nat.mul_add, Nat.mul_comm w (h 0)]
    | v' + 1 =>
      have hv : h (v' + 1) = 0 := h_vanish h mono 1 h1 v'
      rw [hv, if_neg (by omega : ¬ v' + 1 ≤ 0)]
      simp

/-- Abel's identity: peel the last level off a non-increasing summand. -/
theorem gws_split :
    ∀ (d : Dist Nat) (h : Nat → Nat) (M : Nat),
      (∀ v, h (v + 1) ≤ h v) → h (M + 1) = 0 →
      gws d h = gws d (fun v => h v - h M) + h M * cdfWeight d M
  | [], h, M, _, _ => by simp [gws, cdfWeight]
  | (v, w) :: d, h, M, mono, hsM => by
    rw [gws, gws_split d h M mono hsM, cdfWeight_cons]
    show w * h v + (gws d (fun v => h v - h M) + h M * cdfWeight d M) = _
    by_cases E : v ≤ M
    · have HM : h M ≤ h v := by
        have := mono_chain h mono (M - v) v
        rw [(by omega : M - v + v = M)] at this
        exact this
      rw [if_pos E]
      have hsplit : w * h v = w * (h v - h M) + w * h M := by
        rw [← Nat.mul_add, Nat.sub_add_cancel HM]
      have hdist : h M * (w + cdfWeight d M)
          = w * h M + h M * cdfWeight d M := by
        rw [Nat.mul_add, Nat.mul_comm (h M) w]
      show w * h v + ((gws d fun t => h t - h M) + h M * cdfWeight d M)
        = ((w * (h v - h M) + gws d fun t => h t - h M)
           + h M * (w + cdfWeight d M))
      omega
    · have Hv : h v = 0 := by
        have := h_vanish h mono (M + 1) hsM (v - (M + 1))
        rw [(by omega : v - (M + 1) + (M + 1) = v)] at this
        exact this
      rw [if_neg E]
      show w * h v + ((gws d fun t => h t - h M) + h M * cdfWeight d M)
        = ((w * (h v - h M) + gws d fun t => h t - h M)
           + h M * (0 + cdfWeight d M))
      rw [Hv]
      simp

/-- Base direction: FOSD implies gws dominance for every non-increasing
summand vanishing beyond M.  Induction on M via Abel's identity. -/
theorem fosd_gws :
    ∀ (M : Nat) (mu nu : Dist Nat) (h : Nat → Nat),
      totalWeight mu = totalWeight nu →
      FOSDle mu nu →
      (∀ v, h (v + 1) ≤ h v) →
      h (M + 1) = 0 →
      gws nu h ≤ gws mu h
  | 0, mu, nu, h, _, fosd, mono, hM => by
    rw [gws_base nu h mono hM, gws_base mu h mono hM]
    exact Nat.mul_le_mul_left (h 0) (fosd 0)
  | M + 1, mu, nu, h, tw, fosd, mono, hM => by
    rw [gws_split nu h (M + 1) mono hM, gws_split mu h (M + 1) mono hM]
    have ih : gws nu (fun v => h v - h (M + 1))
        ≤ gws mu (fun v => h v - h (M + 1)) := by
      apply fosd_gws M mu nu _ tw fosd
      · intro v
        show h (v + 1) - h (M + 1) ≤ h v - h (M + 1)
        have := mono v
        omega
      · show h (M + 1) - h (M + 1) = 0
        omega
    exact Nat.add_le_add ih (Nat.mul_le_mul_left _ (fosd (M + 1)))

/-- T10: FOSD closed under convolution. -/
theorem FOSD_conv {mu1 nu1 mu2 nu2 : Dist Nat}
    (tw : totalWeight mu1 = totalWeight nu1)
    (f1 : FOSDle mu1 nu1) (f2 : FOSDle mu2 nu2) :
    FOSDle (conv mu1 mu2) (conv nu1 nu2) := by
  intro r
  rw [cdf_conv, cdf_conv]
  apply Nat.le_trans
    (gws_mono nu1 (fun v => FOSD_shift v f2 r))
  exact fosd_gws r mu1 nu1
    (fun v => cdfWeight (dmap (fun u => v + u) mu2) r) tw f1
    (fun v => shift_cdf_mono mu2 v r)
    (shift_cdf_zero mu2 r)

/-- T10 corollary: the closure lifts to every level of the hierarchy. -/
theorem FOSD_SD_conv :
    ∀ (k : Nat) {mu1 nu1 mu2 nu2 : Dist Nat},
      totalWeight mu1 = totalWeight nu1 →
      FOSDle mu1 nu1 → FOSDle mu2 nu2 →
      SDle k (conv mu1 mu2) (conv nu1 nu2)
  | 0, _, _, _, _, tw, f1, f2 => FOSD_conv tw f1 f2
  | k + 1, _, _, _, _, tw, f1, f2 =>
    SD_subsumes k (FOSD_SD_conv k tw f1 f2)

end CSHRL
