module
public import PaperVerification.GeometricMeanLog
@[expose] public section
/-! # Explicit extended-integral semantics

A logarithmic upper bound converts the extended logarithmic integral to the
Lebesgue integral of a nonnegative ENNReal function.  This file proves that
the regularized geometric mean is exactly its exponential, with the required
value zero when that integral is infinite.
-/

noncomputable section

namespace PaperVerification.Hyperbolic

open Real Set MeasureTheory Filter Topology
open scoped ENNReal

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [CompactSpace X] [OpensMeasurableSpace X]

theorem log_integral_of_finite_extended_loss
    (f : C(X, ℝ)) (μ : ProbabilityMeasure X) (hf : ∀ x, 0 ≤ f x)
    {M : ℝ} (hM : 1 ≤ M) (hfM : ∀ x, f x ≤ M)
    (hfinite : (∫⁻ x, extendedLogarithmicLoss f M x ∂μ) ≠ ∞) :
    (∀ᵐ x ∂(μ : Measure X), 0 < f x) ∧
      Integrable (fun x => Real.log (f x)) (μ : Measure X) ∧
      (∫ x, Real.log (f x) ∂μ) = Real.log M - (∫⁻ x, extendedLogarithmicLoss f M x ∂μ).toReal := by
  have hae := ae_lt_top (measurable_extendedLogarithmicLoss f M) hfinite
  have hpos : ∀ᵐ x ∂(μ : Measure X), 0 < f x := by
    filter_upwards [hae] with x hx
    by_contra hn
    have hz : f x = 0 := le_antisymm (le_of_not_gt hn) (hf x)
    rw [extendedLogarithmicLoss_of_zero f hM x hz] at hx
    exact lt_irrefl _ hx
  have hI := integrable_toReal_of_lintegral_ne_top
    (measurable_extendedLogarithmicLoss f M).aemeasurable hfinite
  have hrep : (fun x => Real.log M - (extendedLogarithmicLoss f M x).toReal) =ᵐ[(μ : Measure X)]
      (fun x => Real.log (f x)) := by
    filter_upwards [hpos] with x hx
    rw [extendedLogarithmicLoss_of_pos f M x hx,
      ENNReal.toReal_ofReal (sub_nonneg.mpr (Real.log_le_log hx (hfM x)))]
    ring
  refine ⟨hpos, ((integrable_const _).sub hI).congr hrep, ?_⟩
  rw [← integral_congr_ae hrep, integral_sub (integrable_const _) hI,
    integral_toReal (measurable_extendedLogarithmicLoss f M).aemeasurable hae]
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]

/-- Exact agreement with `exp(integral log f)`, including the extended value
`exp(-infinity)=0`.  The upper bound `M` is arbitrary. -/
theorem geometricMean_eq_extended_integral
    (f : C(X, ℝ)) (μ : ProbabilityMeasure X) (hf : ∀ x, 0 ≤ f x)
    {M : ℝ} (hM : 1 ≤ M) (hfM : ∀ x, f x ≤ M) :
    geometricMean f μ =
      if (∫⁻ x, extendedLogarithmicLoss f M x ∂μ) = ∞ then 0
      else Real.exp (Real.log M - (∫⁻ x, extendedLogarithmicLoss f M x ∂μ).toReal) := by
  split_ifs with hinfinite
  · apply le_antisymm _ (geometricMean_nonneg f μ)
    by_contra hn
    have hG : 0 < geometricMean f μ := lt_of_not_ge hn
    have hbound := lintegral_extendedLogarithmicLoss_le 1 zero_lt_one f μ hM hfM hG
    rw [hinfinite] at hbound
    exact (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound) rfl
  · obtain ⟨hpos, hlog, heq⟩ := log_integral_of_finite_extended_loss f μ hf hM hfM hinfinite
    change geometricMoment 1 f μ = _
    rw [geometricMoment_eq_exp_integral_of_integrable_log 1 zero_le_one f μ hpos hlog,
      one_mul, heq]

end PaperVerification.Hyperbolic

#print axioms PaperVerification.Hyperbolic.geometricMean_eq_extended_integral
