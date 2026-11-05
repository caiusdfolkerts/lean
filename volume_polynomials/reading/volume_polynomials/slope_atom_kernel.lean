module

public import VolumePolynomials.ExponentialKernel

@[expose] public section

/-! # Exact weighted exponential kernels for arbitrary nonnegative atom data -/

noncomputable section

namespace VolumePolynomials.HalfZonotope

theorem exponential_half_log_sq {q : ℝ} (hq : 0 < q) :
    Real.exp (Real.log q / 2) ^ 2 = q := by
  first
  | rw [pow_two, ← Real.exp_add]
    have h : Real.log q / 2 + Real.log q / 2 = Real.log q := by ring
    rw [h, Real.exp_log hq]

theorem atom_exponential_moments {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt (a * b) * Real.exp (-Real.log (b / a) / 2) = a ∧
      Real.sqrt (a * b) * Real.exp (Real.log (b / a) / 2) = b := by
  first
  | have hab : 0 ≤ a * b := (mul_pos ha hb).le
    have hplus : Real.sqrt (a * b) * Real.exp (Real.log (b / a) / 2) = b := by
      have hsquare : (Real.sqrt (a * b) * Real.exp (Real.log (b / a) / 2)) ^ 2 = b ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hab, exponential_half_log_sq (div_pos hb ha)]
        field_simp [ha.ne']
      have hnonneg := mul_nonneg (Real.sqrt_nonneg (a * b))
        (Real.exp_pos (Real.log (b / a) / 2)).le
      nlinarith
    refine ⟨?_, hplus⟩
    have hproduct :
        (Real.sqrt (a * b) * Real.exp (-Real.log (b / a) / 2)) *
          (Real.sqrt (a * b) * Real.exp (Real.log (b / a) / 2)) = a * b := by
      calc
        _ = Real.sqrt (a * b) ^ 2 *
            Real.exp (-Real.log (b / a) / 2 + Real.log (b / a) / 2) := by
          rw [Real.exp_add]
          ring
        _ = a * b := by
          rw [Real.sq_sqrt hab,
            show -Real.log (b / a) / 2 + Real.log (b / a) / 2 = 0 by ring,
            Real.exp_zero, mul_one]
    rw [hplus] at hproduct
    exact mul_right_cancel₀ hb.ne' hproduct

theorem weighted_cornerKernel_of_positive {a b c d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    Real.sqrt (a * b) * Real.sqrt (c * d) *
        cornerKernel (Real.log (b / a)) (Real.log (d / c)) = min (a * d) (c * b) := by
  first
  | have hm := atom_exponential_moments ha hb
    have hn := atom_exponential_moments hc hd
    rcases le_total (Real.log (b / a)) (Real.log (d / c)) with hxy | hyx
    · have hratio : b / a ≤ d / c := by
        simpa only [Real.exp_log (div_pos hb ha), Real.exp_log (div_pos hd hc)] using
          Real.exp_le_exp.mpr hxy
      have hmin : c * b ≤ a * d := by
        have h := (div_le_div_iff₀ ha hc).mp hratio
        nlinarith
      rw [min_eq_right hmin, cornerKernel_of_le hxy]
      have he : Real.exp ((Real.log (b / a) - Real.log (d / c)) / 2) =
          Real.exp (Real.log (b / a) / 2) * Real.exp (-Real.log (d / c) / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = (Real.sqrt (a * b) * Real.exp (Real.log (b / a) / 2)) *
            (Real.sqrt (c * d) * Real.exp (-Real.log (d / c) / 2)) := by
          rw [he]
          ring
        _ = c * b := by rw [hm.2, hn.1]; ring
    · have hratio : d / c ≤ b / a := by
        simpa only [Real.exp_log (div_pos hd hc), Real.exp_log (div_pos hb ha)] using
          Real.exp_le_exp.mpr hyx
      have hmin : a * d ≤ c * b := by
        have h := (div_le_div_iff₀ hc ha).mp hratio
        nlinarith
      rw [min_eq_left hmin, cornerKernel_of_ge hyx]
      have he : Real.exp ((Real.log (d / c) - Real.log (b / a)) / 2) =
          Real.exp (-Real.log (b / a) / 2) * Real.exp (Real.log (d / c) / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = (Real.sqrt (a * b) * Real.exp (-Real.log (b / a) / 2)) *
            (Real.sqrt (c * d) * Real.exp (Real.log (d / c) / 2)) := by
          rw [he]
          ring
        _ = a * d := by rw [hm.1, hn.2]

theorem weighted_cornerKernel {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    Real.sqrt (a * b) * Real.sqrt (c * d) *
        cornerKernel (Real.log (b / a)) (Real.log (d / c)) = min (a * d) (c * b) := by
  first
  | by_cases ha0 : a = 0
    · subst a
      simp [mul_nonneg hc hb]
    by_cases hb0 : b = 0
    · subst b
      simp [mul_nonneg ha hd]
    by_cases hc0 : c = 0
    · subst c
      simp [mul_nonneg ha hd]
    by_cases hd0 : d = 0
    · subst d
      simp [mul_nonneg hc hb]
    exact weighted_cornerKernel_of_positive (lt_of_le_of_ne ha (Ne.symm ha0))
      (lt_of_le_of_ne hb (Ne.symm hb0)) (lt_of_le_of_ne hc (Ne.symm hc0))
      (lt_of_le_of_ne hd (Ne.symm hd0))

end VolumePolynomials.HalfZonotope
