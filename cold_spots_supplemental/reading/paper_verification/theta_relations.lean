module
public import PaperVerification.GaussianIdentities
public import PaperVerification.GaussianExtrema
public import Mathlib.Tactic.IntervalCases
@[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

lemma gaussian_sub_one (α t : ℝ) : gaussian α (t - 1) = gaussian α t := by
  have h := gaussian_int_period α (t - 1) 1
  simpa only [Int.cast_one, sub_add_cancel] using h.symm

lemma gaussian_four_duplications {α : ℝ} (hα : 0 < α) (t : ℝ) :
    gaussian α t ^ 2 =
      gaussian (2 * α) 0 * gaussian (2 * α) t +
        gaussian (2 * α) (1 / 2) * gaussian (2 * α) (t - 1 / 2) ∧
    alternatingGaussian α t ^ 2 =
      gaussian (2 * α) 0 * gaussian (2 * α) t -
        gaussian (2 * α) (1 / 2) * gaussian (2 * α) (t - 1 / 2) ∧
    gaussian α (t - 1 / 2) ^ 2 =
      gaussian (2 * α) 0 * gaussian (2 * α) (t - 1 / 2) +
        gaussian (2 * α) (1 / 2) * gaussian (2 * α) t ∧
    alternatingGaussian α (t - 1 / 2) ^ 2 =
      gaussian (2 * α) 0 * gaussian (2 * α) (t - 1 / 2) -
        gaussian (2 * α) (1 / 2) * gaussian (2 * α) t := by
  refine ⟨gaussian_duplication hα t, alternatingGaussian_duplication hα t, ?_, ?_⟩
  · simpa only [show t - 1 / 2 - 1 / 2 = t - 1 by ring, gaussian_sub_one] using
      gaussian_duplication hα (t - 1 / 2)
  · simpa only [show t - 1 / 2 - 1 / 2 = t - 1 by ring, gaussian_sub_one] using
      alternatingGaussian_duplication hα (t - 1 / 2)

/-- Both quadratic relations in Equation (2), with the actual series as their arguments. -/
theorem gaussian_quadratic_relations {α : ℝ} (hα : 0 < α) (t : ℝ) :
    gaussian α 0 ^ 2 * gaussian α t ^ 2 =
      alternatingGaussian α 0 ^ 2 * alternatingGaussian α t ^ 2 +
        gaussian α (1 / 2) ^ 2 * gaussian α (t - 1 / 2) ^ 2 ∧
    gaussian α 0 ^ 2 * gaussian α (t - 1 / 2) ^ 2 =
      gaussian α (1 / 2) ^ 2 * gaussian α t ^ 2 +
        alternatingGaussian α 0 ^ 2 * alternatingGaussian α (t - 1 / 2) ^ 2 := by
  obtain ⟨ha, hb, hc⟩ := gaussian_constant_quadratics hα
  obtain ⟨hA, hB, hC, hD⟩ := gaussian_four_duplications hα t
  constructor <;> simp only [ha, hb, hc, hA, hB, hC, hD] <;> ring

theorem gaussian_quadratic_relation_reverse {α : ℝ} (hα : 0 < α) (t : ℝ) :
    alternatingGaussian α 0 ^ 2 * gaussian α t ^ 2 =
      gaussian α 0 ^ 2 * alternatingGaussian α t ^ 2 +
        gaussian α (1 / 2) ^ 2 * alternatingGaussian α (t - 1 / 2) ^ 2 := by
  obtain ⟨ha, hb, hc⟩ := gaussian_constant_quadratics hα
  obtain ⟨hA, hB, hC, hD⟩ := gaussian_four_duplications hα t
  simp only [ha, hb, hc, hA, hB, hC, hD]
  ring

def thetaScale (α t : ℝ) : ℝ := gaussian α t ^ 4 - alternatingGaussian α t ^ 4

lemma fourth_difference_algebra (A B P Q U W : ℝ)
    (hA : A ^ 2 = P * U + Q * W) (hB : B ^ 2 = P * U - Q * W) :
    A ^ 4 - B ^ 4 = 4 * P * Q * U * W := by
  calc A ^ 4 - B ^ 4 = (A ^ 2) ^ 2 - (B ^ 2) ^ 2 := by ring
    _ = 4 * P * Q * U * W := by rw [hA, hB]; ring

lemma thetaScale_product {α : ℝ} (hα : 0 < α) (t : ℝ) :
    thetaScale α t = 4 * gaussian (2 * α) 0 * gaussian (2 * α) (1 / 2) *
      gaussian (2 * α) t * gaussian (2 * α) (t - 1 / 2) :=
  fourth_difference_algebra _ _ _ _ _ _ (gaussian_duplication hα t)
    (alternatingGaussian_duplication hα t)

lemma thetaScale_shift {α : ℝ} (hα : 0 < α) (t : ℝ) :
    thetaScale α (t - 1 / 2) = thetaScale α t := by
  rw [thetaScale_product hα, thetaScale_product hα]
  rw [show t - 1 / 2 - 1 / 2 = t - 1 by ring, gaussian_sub_one]
  ring

theorem thetaScale_pos {α : ℝ} (hα : 0 < α) (t : ℝ) : 0 < thetaScale α t := by
  rw [thetaScale_product hα]
  have h2 : 0 < 2 * α := by positivity
  exact mul_pos (mul_pos (mul_pos (mul_pos (by norm_num)
    (gaussian_pos h2 0)) (gaussian_pos h2 (1 / 2)))
    (gaussian_pos h2 t)) (gaussian_pos h2 (t - 1 / 2))

/-- First quartic identity in Equation (4). -/
theorem thetaScale_identity {α : ℝ} (hα : 0 < α) (t : ℝ) :
    thetaScale α t = gaussian α (1 / 2) ^ 3 * gaussian α (2 * t - 1 / 2) := by
  have h2 : 0 < 2 * α := by positivity
  have hc := (gaussian_constant_quadratics hα).2.2
  have hc1 := gaussian_half_eq_twice_quarter hα
  calc
    thetaScale α t = (2 * gaussian α (1 / 2) ^ 2) *
        (gaussian (2 * α) t * gaussian (2 * α) (t - 1 / 2)) := by
      rw [thetaScale_product hα, hc]
      ring
    _ = (2 * gaussian α (1 / 2) ^ 2) *
        (gaussian (4 * α) (1 / 4) * gaussian α (2 * t - 1 / 2)) := by
      rw [gaussian_shift_product h2]
      rw [show 2 * (2 * α) = 4 * α by ring, show (2 * α) / 2 = α by ring]
    _ = gaussian α (1 / 2) ^ 3 * gaussian α (2 * t - 1 / 2) := by
      rw [hc1]
      ring

/-- Second quartic identity in Equation (4). -/
theorem gaussian_quartic_diagonal {α : ℝ} (hα : 0 < α) (t : ℝ) :
    gaussian α t ^ 4 + alternatingGaussian α (t - 1 / 2) ^ 4 =
      gaussian α 0 ^ 3 * gaussian α (2 * t) := by
  obtain ⟨hA, hB, hC, hD⟩ := gaussian_four_duplications hα t
  have ha := (gaussian_constant_quadratics hα).1
  have hd : gaussian (2 * α) t ^ 2 + gaussian (2 * α) (t - 1 / 2) ^ 2 =
      gaussian α 0 * gaussian α (2 * t) := by
    simpa only [show (2 * α) / 2 = α by ring] using
      gaussian_diagonal_sum (show 0 < 2 * α by positivity) t
  calc
    gaussian α t ^ 4 + alternatingGaussian α (t - 1 / 2) ^ 4 =
        (gaussian α t ^ 2) ^ 2 + (alternatingGaussian α (t - 1 / 2) ^ 2) ^ 2 := by ring
    _ = (gaussian (2 * α) 0 ^ 2 + gaussian (2 * α) (1 / 2) ^ 2) *
        (gaussian (2 * α) t ^ 2 + gaussian (2 * α) (t - 1 / 2) ^ 2) := by
      rw [hA, hD]
      ring
    _ = gaussian α 0 ^ 3 * gaussian α (2 * t) := by rw [← ha, hd]; ring

theorem gaussian_shift_product_min {α : ℝ} (hα : 0 < α) (t : ℝ) :
    gaussian α 0 * gaussian α (1 / 2) ≤ gaussian α t * gaussian α (t - 1 / 2) := by
  have hzero := gaussian_shift_product hα 0
  simp only [zero_sub, zero_mul, mul_zero, gaussian_even] at hzero
  rw [gaussian_shift_product hα, hzero]
  exact mul_le_mul_of_nonneg_left (gaussian_minimum (half_pos hα) (2 * t - 1 / 2))
    (gaussian_pos (show 0 < 2 * α by positivity) (1 / 4)).le

theorem gaussian_shift_product_min_iff {α : ℝ} (hα : 0 < α) (t : ℝ) :
    gaussian α t * gaussian α (t - 1 / 2) = gaussian α 0 * gaussian α (1 / 2) ↔
      ∃ z : ℤ, 2 * t = (z : ℝ) := by
  have hzero := gaussian_shift_product hα 0
  simp only [zero_sub, zero_mul, mul_zero, gaussian_even] at hzero
  rw [gaussian_shift_product hα, hzero,
    mul_right_inj' (gaussian_pos (show 0 < 2 * α by positivity) (1 / 4)).ne',
    gaussian_minimum_iff (half_pos hα)]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z + 1, ?_⟩
    push_cast
    linarith
  · rintro ⟨z, hz⟩
    refine ⟨z - 1, ?_⟩
    push_cast
    linarith

def thetaDiagonal (α t : ℝ) : ℝ :=
  (1 / 2) * (gaussian α t ^ 8 + gaussian α (t - 1 / 2) ^ 8 -
    alternatingGaussian α t ^ 8 - alternatingGaussian α (t - 1 / 2) ^ 8)

theorem thetaDiagonal_scale {α : ℝ} (hα : 0 < α) (t : ℝ) :
    thetaDiagonal α t = thetaScale α t *
      (gaussian α t ^ 4 + alternatingGaussian α (t - 1 / 2) ^ 4) := by
  have hB : alternatingGaussian α t ^ 4 = gaussian α t ^ 4 - thetaScale α t := by
    unfold thetaScale
    ring
  have hC : gaussian α (t - 1 / 2) ^ 4 =
      alternatingGaussian α (t - 1 / 2) ^ 4 + thetaScale α t := by
    rw [← thetaScale_shift hα t]
    unfold thetaScale
    ring
  calc
    thetaDiagonal α t = (1 / 2) * ((gaussian α t ^ 4) ^ 2 +
        (gaussian α (t - 1 / 2) ^ 4) ^ 2 - (alternatingGaussian α t ^ 4) ^ 2 -
        (alternatingGaussian α (t - 1 / 2) ^ 4) ^ 2) := by unfold thetaDiagonal; ring
    _ = _ := by rw [hB, hC]; ring

theorem thetaDiagonal_identity {α : ℝ} (hα : 0 < α) (t : ℝ) :
    thetaDiagonal α t = (gaussian α 0 * gaussian α (1 / 2)) ^ 3 *
      (gaussian α (2 * t) * gaussian α (2 * t - 1 / 2)) := by
  have hB : alternatingGaussian α t ^ 4 = gaussian α t ^ 4 - thetaScale α t := by
    unfold thetaScale
    ring
  have hC : gaussian α (t - 1 / 2) ^ 4 =
      alternatingGaussian α (t - 1 / 2) ^ 4 + thetaScale α t := by
    rw [← thetaScale_shift hα t]
    unfold thetaScale
    ring
  calc
    thetaDiagonal α t = (1 / 2) * ((gaussian α t ^ 4) ^ 2 +
        (gaussian α (t - 1 / 2) ^ 4) ^ 2 - (alternatingGaussian α t ^ 4) ^ 2 -
        (alternatingGaussian α (t - 1 / 2) ^ 4) ^ 2) := by unfold thetaDiagonal; ring
    _ = thetaScale α t *
        (gaussian α t ^ 4 + alternatingGaussian α (t - 1 / 2) ^ 4) := by rw [hB, hC]; ring
    _ = (gaussian α 0 * gaussian α (1 / 2)) ^ 3 *
        (gaussian α (2 * t) * gaussian α (2 * t - 1 / 2)) := by
      rw [thetaScale_identity hα, gaussian_quartic_diagonal hα]
      ring

theorem thetaDiagonal_min {α : ℝ} (hα : 0 < α) (t : ℝ) :
    (gaussian α 0 * gaussian α (1 / 2)) ^ 4 ≤ thetaDiagonal α t := by
  rw [thetaDiagonal_identity hα]
  have hp := gaussian_shift_product_min hα (2 * t)
  have hmul := mul_le_mul_of_nonneg_left hp
    (pow_nonneg (mul_nonneg (gaussian_pos hα 0).le (gaussian_pos hα (1 / 2)).le) 3)
  nlinarith only [hmul]

theorem thetaDiagonal_min_iff {α : ℝ} (hα : 0 < α) (t : ℝ) :
    thetaDiagonal α t = (gaussian α 0 * gaussian α (1 / 2)) ^ 4 ↔
      ∃ z : ℤ, 4 * t = (z : ℝ) := by
  have hp : 0 < gaussian α 0 * gaussian α (1 / 2) :=
    mul_pos (gaussian_pos hα 0) (gaussian_pos hα (1 / 2))
  rw [thetaDiagonal_identity hα, show (gaussian α 0 * gaussian α (1 / 2)) ^ 4 =
    (gaussian α 0 * gaussian α (1 / 2)) ^ 3 *
      (gaussian α 0 * gaussian α (1 / 2)) by ring,
    mul_right_inj' (pow_pos hp 3).ne', gaussian_shift_product_min_iff hα]
  simp only [show 2 * (2 * t) = 4 * t by ring]

theorem thetaDiagonal_equality_points {α t : ℝ} (hα : 0 < α) (ht : 0 ≤ t)
    (ht2 : t ≤ 1 / 2) :
    thetaDiagonal α t = (gaussian α 0 * gaussian α (1 / 2)) ^ 4 ↔
      t = 0 ∨ t = 1 / 4 ∨ t = 1 / 2 := by
  rw [thetaDiagonal_min_iff hα]
  constructor
  · rintro ⟨z, hz⟩
    have hz0 : (0 : ℤ) ≤ z := by exact_mod_cast (show (0 : ℝ) ≤ z by linarith)
    have hz2 : z ≤ (2 : ℤ) := by exact_mod_cast (show (z : ℝ) ≤ 2 by linarith)
    interval_cases z
    · left; norm_num at hz; linarith
    · right; left; norm_num at hz; linarith
    · right; right; norm_num at hz; linarith
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, by norm_num⟩
    · exact ⟨1, by norm_num⟩
    · exact ⟨2, by norm_num⟩

end PaperVerification.ColdSpots
