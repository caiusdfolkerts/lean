module

public import VolumePolynomials.KernelTestMeasure
public import Mathlib.MeasureTheory.Group.Convolution

@[expose] public section

/-! # The exact compact-support mass test used by the lower witnesses -/

open MeasureTheory Set Filter
open scoped Topology InnerProductSpace RealInnerProductSpace MeasureTheory

namespace VolumePolynomials

theorem inner_cornerMean_test_eq_mass {R : ℝ} (hR : 0 ≤ R)
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hSupport : ∀ᵐ x ∂μ, x ∈ Icc (-R) R) :
    ⟪cornerMean μ, cornerMean (cornerTestMeasure R)⟫_ℝ = μ.real univ := by
  first
  | rw [real_inner_comm]
    change ⟪cornerMean (cornerTestMeasure R), ∫ x, cornerFeature x ∂μ⟫_ℝ = _
    rw [← integral_inner (integrable_cornerFeature μ)]
    calc
      _ = ∫ _x, (1 : ℝ) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hSupport] with x hx
        rw [real_inner_comm, inner_cornerFeature_mean, integral_cornerTestMeasure hR]
        exact cornerTestPotential_inside hx.1 hx.2
      _ = μ.real univ := by simp

/-- A measure supported on an interval has energy at least its squared mass
divided by the exact energy of the test measure. -/
theorem compact_mass_sq_le_energy {R : ℝ} (hR : 0 ≤ R)
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hSupport : ∀ᵐ x ∂μ, x ∈ Icc (-R) R) :
    (μ.real univ) ^ 2 ≤ (1 + R / 2) * ‖cornerMean μ‖ ^ 2 := by
  first
  | have hCS := abs_real_inner_le_norm (cornerMean μ) (cornerMean (cornerTestMeasure R))
    have hsq := (sq_le_sq₀ (abs_nonneg _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hCS
    rw [inner_cornerMean_test_eq_mass hR μ hSupport, sq_abs, mul_pow,
      norm_cornerMean_test_sq hR] at hsq
    simpa only [mul_comm] using hsq

theorem convolution_real_mass (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (μ ∗ ν).real univ = μ.real univ * ν.real univ := by
  first
  | have hadd : Measurable (fun p : ℝ × ℝ => p.1 + p.2) := by fun_prop
    simp [Measure.conv, measureReal_def, Measure.map_apply hadd MeasurableSet.univ,
      ENNReal.toReal_mul]
    rw [← Set.univ_prod_univ, Measure.prod_prod, ENNReal.toReal_mul]

theorem convolution_interval_support {R S : ℝ} (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc (-R) R) (hν : ∀ᵐ y ∂ν, y ∈ Icc (-S) S) :
    ∀ᵐ z ∂(μ ∗ ν), z ∈ Icc (-(R + S)) (R + S) := by
  first
  | rw [Measure.conv]
    have hadd : Measurable (fun p : ℝ × ℝ => p.1 + p.2) := by fun_prop
    apply (ae_map_iff (μ := μ.prod ν) (f := fun p : ℝ × ℝ => p.1 + p.2)
      (p := fun z : ℝ => z ∈ Icc (-(R + S)) (R + S))
      hadd.aemeasurable measurableSet_Icc).mpr
    apply (Measure.ae_prod_iff_ae_ae (μ := μ) (ν := ν)
      (measurableSet_Icc.preimage hadd)).mpr
    filter_upwards [hμ] with x hx
    filter_upwards [hν] with y hy
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- The convolution lower bound used in Proposition5.4, for every finite
positive measure supported in the stated interval. -/
theorem compact_convolution_mass_fourth_le_energy {R : ℝ} (hR : 0 ≤ R)
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hSupport : ∀ᵐ x ∂μ, x ∈ Icc (-R) R) :
    (μ.real univ) ^ 4 ≤ (1 + R) * ‖cornerMean (μ ∗ μ)‖ ^ 2 := by
  first
  | have h := compact_mass_sq_le_energy (add_nonneg hR hR) (μ ∗ μ)
      (convolution_interval_support μ μ hSupport hSupport)
    rw [convolution_real_mass] at h
    convert h using 1 <;> ring

end VolumePolynomials
