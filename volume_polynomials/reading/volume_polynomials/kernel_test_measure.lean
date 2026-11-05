module

public import VolumePolynomials.ExponentialKernel
public import Mathlib.Tactic.NormNum

@[expose] public section

/-! # Exact test potential and its energy, equation (5.1) -/

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace VolumePolynomials

theorem integral_exp_half_sub (a b x : ℝ) :
    (∫ t in a..b, Real.exp ((t - x) / 2)) =
      2 * (Real.exp ((b - x) / 2) - Real.exp ((a - x) / 2)) := by
  simp_rw [sub_div]
  rw [intervalIntegral.integral_comp_div_sub Real.exp (by norm_num : (2 : ℝ) ≠ 0),
    integral_exp]
  rfl

theorem integral_exp_sub_half (a b x : ℝ) :
    (∫ t in a..b, Real.exp ((x - t) / 2)) =
      2 * (Real.exp ((x - a) / 2) - Real.exp ((x - b) / 2)) := by
  simp_rw [sub_div]
  rw [intervalIntegral.integral_comp_sub_div Real.exp (by norm_num : (2 : ℝ) ≠ 0),
    integral_exp]
  rfl

theorem integral_cornerKernel_left {a b x : ℝ} (hab : a ≤ b) (hbx : b ≤ x) :
    (∫ t in a..b, cornerKernel x t) =
      2 * (Real.exp ((b - x) / 2) - Real.exp ((a - x) / 2)) := by
  rw [← integral_exp_half_sub a b x]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hab] at ht
  exact cornerKernel_of_ge (ht.2.trans hbx)

theorem integral_cornerKernel_right {a b x : ℝ} (hab : a ≤ b) (hxa : x ≤ a) :
    (∫ t in a..b, cornerKernel x t) =
      2 * (Real.exp ((x - a) / 2) - Real.exp ((x - b) / 2)) := by
  rw [← integral_exp_sub_half a b x]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hab] at ht
  exact cornerKernel_of_le (hxa.trans ht.1)

noncomputable def cornerTestPotential (R x : ℝ) : ℝ :=
  (1 / 4) * (∫ t in -R..R, cornerKernel x t) +
    (1 / 2) * (cornerKernel x (-R) + cornerKernel x R)

theorem cornerTestPotential_inside {R x : ℝ} (hRx : -R ≤ x) (hxR : x ≤ R) :
    cornerTestPotential R x = 1 := by
  have hleft : IntervalIntegrable (cornerKernel x) volume (-R) x :=
    (continuous_cornerKernel x).intervalIntegrable (-R) x
  have hright : IntervalIntegrable (cornerKernel x) volume x R :=
    (continuous_cornerKernel x).intervalIntegrable x R
  unfold cornerTestPotential
  rw [← intervalIntegral.integral_add_adjacent_intervals hleft hright,
    integral_cornerKernel_left hRx le_rfl,
    integral_cornerKernel_right hxR le_rfl,
    cornerKernel_of_ge hRx, cornerKernel_of_le hxR]
  simp only [sub_self, zero_div, Real.exp_zero]
  ring

theorem cornerTestPotential_right {R x : ℝ} (hR : 0 ≤ R) (hx : R ≤ x) :
    cornerTestPotential R x = Real.exp (-(|x| - R) / 2) := by
  have hnegR : -R ≤ R := by linarith
  unfold cornerTestPotential
  rw [integral_cornerKernel_left hnegR hx,
    cornerKernel_of_ge (hnegR.trans hx), cornerKernel_of_ge hx,
    abs_of_nonneg (hR.trans hx)]
  have heq : -(x - R) / 2 = (R - x) / 2 := by ring
  rw [heq]
  ring

theorem cornerTestPotential_left {R x : ℝ} (hR : 0 ≤ R) (hx : x ≤ -R) :
    cornerTestPotential R x = Real.exp (-(|x| - R) / 2) := by
  have hnegR : -R ≤ R := by linarith
  unfold cornerTestPotential
  rw [integral_cornerKernel_right hnegR hx,
    cornerKernel_of_le hx, cornerKernel_of_le (hx.trans hnegR),
    abs_of_nonpos (hx.trans (by linarith : -R ≤ 0))]
  have heq : -(-x - R) / 2 = (x - -R) / 2 := by ring
  rw [heq]
  ring

theorem cornerTestPotential_eq {R : ℝ} (hR : 0 ≤ R) (x : ℝ) :
    cornerTestPotential R x =
      if |x| ≤ R then 1 else Real.exp (-(|x| - R) / 2) := by
  by_cases hx : |x| ≤ R
  · rw [ite_eq_left hx]
    exact cornerTestPotential_inside (abs_le.mp hx).1 (abs_le.mp hx).2
  · rw [ite_eq_right hx]
    by_cases hxr : R ≤ x
    · exact cornerTestPotential_right hR hxr
    · apply cornerTestPotential_left hR
      by_contra hn
      exact hx (abs_lt.mpr ⟨lt_of_not_ge hn, lt_of_not_ge hxr⟩).le

theorem cornerTestPotential_eq_exp_max {R : ℝ} (hR : 0 ≤ R) (x : ℝ) :
    cornerTestPotential R x = Real.exp (-max (|x| - R) 0 / 2) := by
  rw [cornerTestPotential_eq hR]
  split_ifs with hx
  · rw [max_eq_right (sub_nonpos.mpr hx)]
    simp
  · rw [max_eq_left (sub_nonneg.mpr (le_of_not_ge hx))]

theorem continuous_cornerTestPotential {R : ℝ} (hR : 0 ≤ R) :
    Continuous (cornerTestPotential R) := by
  have heq := funext (cornerTestPotential_eq_exp_max hR)
  rw [heq]
  fun_prop

theorem cornerTestPotential_pos {R : ℝ} (hR : 0 ≤ R) (x : ℝ) :
    0 < cornerTestPotential R x := by
  rw [cornerTestPotential_eq_exp_max hR]
  exact Real.exp_pos _

theorem cornerTestPotential_le_one {R : ℝ} (hR : 0 ≤ R) (x : ℝ) :
    cornerTestPotential R x ≤ 1 := by
  rw [cornerTestPotential_eq_exp_max hR]
  apply Real.exp_le_one_iff.mpr
  linarith [le_max_right (|x| - R) 0]

theorem integrable_cornerTestPotential {R : ℝ} (hR : 0 ≤ R)
    (μ : Measure ℝ) [IsFiniteMeasure μ] : Integrable (cornerTestPotential R) μ := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
    (continuous_cornerTestPotential hR).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  simpa only [Real.norm_eq_abs, abs_of_pos (cornerTestPotential_pos hR x)] using
    cornerTestPotential_le_one hR x

/-- The measure used literally in equation (5.1). -/
noncomputable def cornerTestMeasure (R : ℝ) : Measure ℝ :=
  (1 / 4 : ℝ≥0) • volume.restrict (Icc (-R) R) +
    (1 / 2 : ℝ≥0) • Measure.dirac (-R) +
    (1 / 2 : ℝ≥0) • Measure.dirac R

instance cornerTestMeasure_finite (R : ℝ) : IsFiniteMeasure (cornerTestMeasure R) := by
  unfold cornerTestMeasure
  infer_instance

theorem integral_cornerTestMeasure {R : ℝ} (hR : 0 ≤ R) (x : ℝ) :
    (∫ y, cornerKernel x y ∂cornerTestMeasure R) = cornerTestPotential R x := by
  unfold cornerTestMeasure
  rw [integral_add_measure, integral_add_measure]
  · rw [integral_smul_nnreal_measure, integral_smul_nnreal_measure, integral_smul_nnreal_measure,
      integral_dirac, integral_dirac, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -R ≤ R)]
    norm_num [cornerTestPotential, NNReal.smul_def, smul_eq_mul]
    ring
  all_goals exact integrable_cornerKernel _ x

theorem integral_cornerTestPotential {R : ℝ} (hR : 0 ≤ R) :
    (∫ x, cornerTestPotential R x ∂cornerTestMeasure R) = 1 + R / 2 := by
  have hinterval : (∫ x in Icc (-R) R, cornerTestPotential R x) = 2 * R := by
    calc
      _ = ∫ _x in Icc (-R) R, (1 : ℝ) := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro x hx
        exact cornerTestPotential_inside hx.1 hx.2
      _ = 2 * R := by
        rw [integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le (by linarith : -R ≤ R)]
        simp only [intervalIntegral.integral_const, smul_eq_mul]
        ring
  unfold cornerTestMeasure
  rw [integral_add_measure, integral_add_measure]
  · rw [integral_smul_nnreal_measure, integral_smul_nnreal_measure, integral_smul_nnreal_measure,
      integral_dirac, integral_dirac, hinterval,
      cornerTestPotential_inside le_rfl (by linarith : -R ≤ R),
      cornerTestPotential_inside (by linarith : -R ≤ R) le_rfl]
    norm_num [NNReal.smul_def, smul_eq_mul]
    ring
  all_goals exact integrable_cornerTestPotential hR _

/-- The exact energy of the actual positive test measure. -/
theorem norm_cornerMean_test_sq {R : ℝ} (hR : 0 ≤ R) :
    ‖cornerMean (cornerTestMeasure R)‖ ^ 2 = 1 + R / 2 := by
  rw [norm_cornerMean_sq]
  simp_rw [integral_cornerTestMeasure hR]
  exact integral_cornerTestPotential hR

end VolumePolynomials
