module

public import VolumePolynomials.FourierGeneratingSeries
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Analytic.ChangeOrigin

@[expose] public section
noncomputable section

namespace VolumePolynomials

open Set Metric
open scoped NNReal ENNReal

/-- The full coefficient sequence; its constant coefficient is zero. -/
noncomputable def sineCoefficient (θ : ℝ) (n : ℕ) : ℂ :=
  ((|Real.sin ((n : ℝ) * θ)| : ℝ) : ℂ)

theorem sineCoefficient_norm_le (θ : ℝ) (n : ℕ) : ‖sineCoefficient θ n‖ ≤ 1 := by
  first
  | simpa [sineCoefficient, Complex.norm_real, Real.norm_eq_abs] using
      Real.abs_sin_le_one ((n : ℝ) * θ)

theorem sine_powerSeries_norm_summable (θ : ℝ) (z : ℂ) (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => ‖sineCoefficient θ n * z ^ n‖) := by
  first
  | apply (summable_geometric_of_lt_one (norm_nonneg z) hz).of_nonneg_of_le
      (fun n => norm_nonneg _)
    intro n
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_left (pow_nonneg (norm_nonneg z) n) (sineCoefficient_norm_le θ n)

theorem sine_powerSeries_summable (θ : ℝ) (z : ℂ) (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => sineCoefficient θ n * z ^ n) :=
  (sine_powerSeries_norm_summable θ z hz).of_norm

theorem sineGeneratingFunction_eq_full_series (θ : ℝ) (z : ℂ) (hz : ‖z‖ < 1) :
    sineGeneratingFunction θ z = ∑' n : ℕ, sineCoefficient θ n * z ^ n := by
  first
  | rw [(sine_powerSeries_summable θ z hz).tsum_eq_zero_add]
    simp [sineCoefficient, sineGeneratingFunction]

/-- Holomorphy of the actual series in the open unit disk follows from its uniformly bounded
coefficients, with the radius bound proved for the actual formal multilinear series. -/
theorem sineGeneratingFunction_analyticOnNhd (θ : ℝ) :
    AnalyticOnNhd ℂ (sineGeneratingFunction θ) (ball 0 1) := by
  first
  | let p := FormalMultilinearSeries.ofScalars ℂ (sineCoefficient θ)
    have hr : (1 : ℝ≥0∞) ≤ p.radius := by
      apply p.le_radius_of_bound (r := (1 : ℝ≥0)) 1
      intro n
      simpa [p, FormalMultilinearSeries.ofScalars_norm] using sineCoefficient_norm_le θ n
    have hp : AnalyticOnNhd ℂ p.sum (ball 0 1) := by
      intro z hz
      apply p.analyticOnNhd z
      apply lt_of_lt_of_le _ hr
      simpa only [mem_ball, dist_zero_right, mem_eball, edist_dist,
        ENNReal.ofReal_lt_one] using hz
    apply (analyticOnNhd_congr isOpen_ball ?_).mp hp
    intro z hz
    have hznorm : ‖z‖ < 1 := by simpa using hz
    rw [sineGeneratingFunction_eq_full_series θ z hznorm]
    exact FormalMultilinearSeries.ofScalars_sum_eq (sineCoefficient θ) z

end VolumePolynomials
