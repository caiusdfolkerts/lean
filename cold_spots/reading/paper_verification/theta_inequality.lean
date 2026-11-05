module
public import PaperVerification.ThetaGeometricTransfer
public import PaperVerification.HyperbolicTheorem
@[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

open MeasureTheory Set Filter
open PaperVerification.Hyperbolic

lemma centeredCoshMap_eq (R : ℝ) : centeredCoshMap R = intervalCenteredCosh R := rfl

/-- The inequality in Proposition 3.2, for every Borel probability measure,
including endpoint atoms and vanishing alternating geometric means. -/
theorem theta_geometric_mean_inequality {α : ℝ} (hα : 0 < α)
    (μ : ProbabilityMeasure HalfInterval) :
    2 * (gaussian α 0 * gaussian α (1 / 2)) ^ 4 ≤ thetaMomentNumerator hα μ := by
  apply thetaMoment_bound_from_hyperbolic hα μ
  rw [centeredCoshMap_eq]
  exact hyperbolic_geometric_mean_inequality (thetaR α) (thetaR_pos hα) (thetaPush hα μ)

theorem theta_geometric_mean_inequality_literal {α : ℝ} (hα : 0 < α)
    (μ : ProbabilityMeasure HalfInterval) :
    2 * (gaussian α 0 * gaussian α (1 / 2)) ^ 4 ≤
      geometricMean (thetaAMap hα) μ ^ 8 + geometricMean (thetaCMap hα) μ ^ 8 -
      geometricMean (thetaBMap hα) μ ^ 8 - geometricMean (thetaDMap hα) μ ^ 8 := by
  have h := theta_geometric_mean_inequality hα μ
  unfold thetaMomentNumerator at h
  erw [geometricMoment_nat 8 (thetaAMap hα) μ,
    geometricMoment_nat 8 (thetaCMap hα) μ,
    geometricMoment_nat 8 (thetaBMap hα) μ,
    geometricMoment_nat 8 (thetaDMap hα) μ] at h
  exact h

/-- Exact equality before converting the three-point support into the paper's
four displayed measures. The conversion is a separate measure-theoretic lemma. -/
theorem theta_geometric_mean_equality_conditions {α : ℝ} (hα : 0 < α)
    (μ : ProbabilityMeasure HalfInterval) :
    thetaMomentNumerator hα μ = 2 * (gaussian α 0 * gaussian α (1 / 2)) ^ 4 ↔
      (∀ᵐ (t : HalfInterval) ∂(μ : Measure HalfInterval),
        (t : ℝ) = 0 ∨ (t : ℝ) = 1 / 4 ∨ (t : ℝ) = 1 / 2) ∧
      HyperbolicEquality (thetaR α) (thetaPush hα μ) := by
  have hH : 2 * Real.cosh (thetaR α) *
      geometricMean (centeredCoshMap (thetaR α)) (thetaPush hα μ) ≤
        hyperbolicNumerator (thetaR α) (thetaPush hα μ) := by
    rw [centeredCoshMap_eq]
    exact hyperbolic_geometric_mean_inequality (thetaR α) (thetaR_pos hα) (thetaPush hα μ)
  rw [thetaMoment_equality_from_hyperbolic hα μ hH,
    thetaDiagonal_geometric_eq_iff hα μ, centeredCoshMap_eq,
    hyperbolic_geometric_mean_equality_iff (thetaR α) (thetaR_pos hα)]

end PaperVerification.ColdSpots
