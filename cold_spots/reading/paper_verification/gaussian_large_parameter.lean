module
public import PaperVerification.Gaussian
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds
@[expose] public section
noncomputable section

open scoped BigOperators

namespace PaperVerification.ColdSpots

lemma cosh_quadratic_lower (x : ℝ) : 1 + x ^ 2 / 2 ≤ Real.cosh x := by
  have h := (Real.hasSum_cosh x).summable.sum_le_tsum (Finset.range 2)
    (fun n _ ↦ show 0 ≤ x ^ (2 * n) / (Nat.factorial (2 * n) : ℝ) by
      apply div_nonneg
      · rw [Nat.mul_comm 2 n, pow_mul]
        exact sq_nonneg _
      · positivity)
  rw [(Real.hasSum_cosh x).tsum_eq] at h
  norm_num [Finset.sum_range_succ] at h
  exact h

lemma exp_lt_one_add_two_mul {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    Real.exp s < 1 + 2 * s := by
  have hconv := convexOn_exp.2
  have h := hconv (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
    (a := 1 - s) (b := s) (sub_nonneg.mpr hs1) hs.le (by ring)
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add, Real.exp_zero] at h
  nlinarith [Real.exp_one_lt_three]

/-- An elementary estimate covering the large Gaussian parameter regime. -/
lemma cosh_alpha_mul_gt_exp_sq {α u : ℝ} (hα : 4 ≤ α) (hu : 0 < u)
    (hu2 : u ≤ 1 / 2) : Real.exp (α * u ^ 2) < Real.cosh (α * u) := by
  have hα0 : 0 < α := by linarith
  have hx : 0 < α * u := mul_pos hα0 hu
  by_cases hx2 : α * u ≤ 2
  · have hs0 : 0 < (α * u) ^ 2 / 4 := div_pos (sq_pos_of_pos hx) (by norm_num)
    have hs1 : (α * u) ^ 2 / 4 ≤ 1 := by nlinarith
    have he := exp_lt_one_add_two_mul hs0 hs1
    have hq := cosh_quadratic_lower (α * u)
    have harg : α * u ^ 2 ≤ (α * u) ^ 2 / 4 := by
      nlinarith [mul_nonneg (show 0 ≤ α * u ^ 2 by positivity) (sub_nonneg.mpr hα)]
    have he' := Real.exp_le_exp.mpr harg
    nlinarith
  · have hx2' : 2 ≤ α * u := le_of_lt (lt_of_not_ge hx2)
    have he1 : 2 < Real.exp (α * u / 2) :=
      lt_of_lt_of_le Real.exp_one_gt_two (Real.exp_le_exp.mpr (by linarith))
    have harg : α * u ^ 2 ≤ α * u / 2 := by nlinarith
    have hearg := Real.exp_le_exp.mpr harg
    have hex : Real.exp (α * u) = Real.exp (α * u / 2) ^ 2 := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [Real.cosh_eq, hex]
    nlinarith [Real.exp_pos (-(α * u))]

lemma cosh_alpha_mul_ge_exp_sq {α u : ℝ} (hα : 4 ≤ α) (hu : 0 ≤ u)
    (hu2 : u ≤ 1 / 2) : Real.exp (α * u ^ 2) ≤ Real.cosh (α * u) := by
  rcases eq_or_lt_of_le hu with rfl | hu
  · simp
  · exact (cosh_alpha_mul_gt_exp_sq hα hu hu2).le

lemma gaussian_pair_centered (α d u : ℝ) :
    Real.exp (-α * (d - u) ^ 2) + Real.exp (-α * (d + u) ^ 2) =
      2 * Real.exp (-α * d ^ 2) * Real.exp (-α * u ^ 2) * Real.cosh (2 * α * d * u) := by
  have h₁ : Real.exp (-α * (d - u) ^ 2) =
      Real.exp (-α * d ^ 2) * Real.exp (-α * u ^ 2) * Real.exp (2 * α * d * u) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have h₂ : Real.exp (-α * (d + u) ^ 2) =
      Real.exp (-α * d ^ 2) * Real.exp (-α * u ^ 2) * Real.exp (-(2 * α * d * u)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [h₁, h₂, Real.cosh_eq]
  ring

lemma gaussian_pair_min {α d u : ℝ} (hα : 4 ≤ α) (hd : 1 / 2 ≤ d)
    (hu : 0 ≤ u) (hu2 : u ≤ 1 / 2) :
    2 * Real.exp (-α * d ^ 2) ≤
      Real.exp (-α * (d - u) ^ 2) + Real.exp (-α * (d + u) ^ 2) := by
  have hα0 : 0 ≤ α := le_trans (by norm_num) hα
  have harg : α * u ≤ 2 * α * d * u := by
    nlinarith [mul_nonneg (mul_nonneg hα0 hu) (show 0 ≤ 2 * d - 1 by linarith)]
  have hc : Real.cosh (α * u) ≤ Real.cosh (2 * α * d * u) := by
    apply Real.cosh_le_cosh.mpr
    rw [abs_of_nonneg (mul_nonneg hα0 hu), abs_of_nonneg (by positivity)]
    exact harg
  have he := le_trans (cosh_alpha_mul_ge_exp_sq hα hu hu2) hc
  have hex : Real.exp (-α * u ^ 2) * Real.exp (α * u ^ 2) = 1 := by
    rw [← Real.exp_add]
    simp
  have hm := mul_le_mul_of_nonneg_left he (Real.exp_pos (-α * u ^ 2)).le
  rw [hex] at hm
  rw [gaussian_pair_centered]
  nlinarith [mul_nonneg (show 0 ≤ 2 * Real.exp (-α * d ^ 2) by positivity) (sub_nonneg.mpr hm)]

lemma gaussian_pair_min_strict {α d u : ℝ} (hα : 4 ≤ α) (hd : 1 / 2 ≤ d)
    (hu : 0 < u) (hu2 : u ≤ 1 / 2) :
    2 * Real.exp (-α * d ^ 2) <
      Real.exp (-α * (d - u) ^ 2) + Real.exp (-α * (d + u) ^ 2) := by
  have hα0 : 0 ≤ α := le_trans (by norm_num) hα
  have harg : α * u ≤ 2 * α * d * u := by
    nlinarith [mul_nonneg (mul_nonneg hα0 hu.le) (show 0 ≤ 2 * d - 1 by linarith)]
  have hc : Real.cosh (α * u) ≤ Real.cosh (2 * α * d * u) := by
    apply Real.cosh_le_cosh.mpr
    rw [abs_of_nonneg (mul_nonneg hα0 hu.le), abs_of_nonneg (by positivity)]
    exact harg
  have he := lt_of_lt_of_le (cosh_alpha_mul_gt_exp_sq hα hu hu2) hc
  have hex : Real.exp (-α * u ^ 2) * Real.exp (α * u ^ 2) = 1 := by
    rw [← Real.exp_add]
    simp
  have hm := mul_lt_mul_of_pos_left he (Real.exp_pos (-α * u ^ 2))
  rw [hex] at hm
  rw [gaussian_pair_centered]
  nlinarith [mul_pos (show 0 < 2 * Real.exp (-α * d ^ 2) by positivity) (sub_pos.mpr hm)]

lemma gaussian_neg_half_pair_sum {α : ℝ} (hα : 0 < α) (t : ℝ) :
    HasSum (fun n : ℕ ↦ Real.exp (-α * ((n : ℝ) + t) ^ 2) +
      Real.exp (-α * ((n : ℝ) + 1 - t) ^ 2)) (gaussian α t) := by
  have h := (hasSum_gaussian hα (-t)).nat_add_neg_add_one
  rw [gaussian_even] at h
  convert h using 1
  funext n
  simp only [Int.cast_natCast, Int.cast_neg, Int.cast_add, Int.cast_one, sub_neg_eq_add]
  congr 1
  congr 1
  ring

theorem gaussian_min_large_parameter {α t : ℝ} (hα : 4 ≤ α) (ht : 0 ≤ t)
    (ht2 : t ≤ 1 / 2) : gaussian α (1 / 2) ≤ gaussian α t := by
  have hα0 : 0 < α := lt_of_lt_of_le (by norm_num) hα
  have h₀ := gaussian_neg_half_pair_sum hα0 (1 / 2)
  have ht' := gaussian_neg_half_pair_sum hα0 t
  apply hasSum_le _ h₀ ht'
  intro n
  have h := gaussian_pair_min hα
    (show (1 / 2 : ℝ) ≤ (n : ℝ) + 1 / 2 by linarith [Nat.cast_nonneg (α := ℝ) n])
    (show 0 ≤ (1 / 2 : ℝ) - t by linarith) (show (1 / 2 : ℝ) - t ≤ 1 / 2 by linarith)
  rw [show (n : ℝ) + 1 / 2 - (1 / 2 - t) = n + t by ring,
    show (n : ℝ) + 1 / 2 + (1 / 2 - t) = n + 1 - t by ring, two_mul] at h
  simpa only [show (n : ℝ) + 1 - 1 / 2 = n + 1 / 2 by ring] using h

theorem gaussian_min_large_parameter_strict {α t : ℝ} (hα : 4 ≤ α) (ht : 0 ≤ t)
    (ht2 : t < 1 / 2) : gaussian α (1 / 2) < gaussian α t := by
  have hα0 : 0 < α := lt_of_lt_of_le (by norm_num) hα
  have h₀ := gaussian_neg_half_pair_sum hα0 (1 / 2)
  have ht' := gaussian_neg_half_pair_sum hα0 t
  apply hasSum_lt (i := (0 : ℕ)) ?_ ?_ h₀ ht'
  · intro n
    have h := gaussian_pair_min hα
      (show (1 / 2 : ℝ) ≤ (n : ℝ) + 1 / 2 by linarith [Nat.cast_nonneg (α := ℝ) n])
      (show 0 ≤ (1 / 2 : ℝ) - t by linarith) (show (1 / 2 : ℝ) - t ≤ 1 / 2 by linarith)
    rw [show (n : ℝ) + 1 / 2 - (1 / 2 - t) = n + t by ring,
      show (n : ℝ) + 1 / 2 + (1 / 2 - t) = n + 1 - t by ring, two_mul] at h
    simpa only [show (n : ℝ) + 1 - 1 / 2 = n + 1 / 2 by ring] using h
  · have h := gaussian_pair_min_strict hα (show (1 / 2 : ℝ) ≤ 1 / 2 by rfl)
      (show 0 < (1 / 2 : ℝ) - t by linarith) (show (1 / 2 : ℝ) - t ≤ 1 / 2 by linarith)
    rw [show (1 / 2 : ℝ) - (1 / 2 - t) = t by ring,
      show (1 / 2 : ℝ) + (1 / 2 - t) = 1 - t by ring, two_mul] at h
    simpa only [Nat.cast_zero, zero_add, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] using h

end PaperVerification.ColdSpots
