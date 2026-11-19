module
public import PaperVerification.HyperbolicAtomic
public import PaperVerification.GeometricMeanExtended
@[expose] public section
/-! # The full hyperbolic geometric-mean inequality

Theorem 3.1 is stated for every Borel probability measure on the entire closed
interval.  Geometric means at zero, endpoint atoms, and nonintegrable negative
logarithms are included by the previously verified truncation definition.
The equality condition is exactly a point mass or a balanced reflected pair.
-/

noncomputable section

namespace PaperVerification.Hyperbolic

open Real Set MeasureTheory

def intervalCenteredCosh (R : ℝ) : C(Interval R, ℝ) :=
  ⟨fun p => Real.cosh (2 * (p : ℝ) - R),
    Real.continuous_cosh.comp ((continuous_const.mul continuous_subtype_val).sub continuous_const)⟩

theorem geometricMean_centered_eq_exp_integral (R : ℝ) (μ : ProbabilityMeasure (Interval R)) :
    geometricMean (intervalCenteredCosh R) μ =
      Real.exp (∫ p, intervalCenteredLogCosh R p ∂μ) := by
  unfold geometricMean
  rw [geometricMoment_eq_exp_integral_of_lower_bound 1 zero_le_one _ μ
    (by norm_num : (0 : ℝ) < 1) (fun p => Real.one_le_cosh (2 * (p : ℝ) - R)), one_mul]
  rfl

/-- The unrestricted variational objective is nonnegative. -/
theorem hyperbolicObjective_nonneg (R : ℝ) (hR : 0 < R)
    (μ : ProbabilityMeasure (Interval R)) : 0 ≤ hyperbolicObjective R μ := by
  obtain ⟨ν, hmin⟩ := exists_minimizer_hyperbolicObjective R hR
  obtain ⟨p, q, hpq, t, ht, hν⟩ := ordered_pair_mixture_of_minimizer R hR ν hmin
  have hν0 : 0 ≤ hyperbolicObjective R ν := by
    rw [hν]
    exact hyperbolicObjective_pair_nonneg R p q hpq t ht
  exact hν0.trans (hmin μ)

/-- Equality in the unrestricted variational problem has exactly the two
measure-theoretic forms stated in the paper. -/
theorem hyperbolicObjective_eq_zero_iff_equality (R : ℝ) (hR : 0 < R)
    (μ : ProbabilityMeasure (Interval R)) :
    hyperbolicObjective R μ = 0 ↔ HyperbolicEquality R μ := by
  constructor
  · intro hzero
    have hmin : ∀ ν : ProbabilityMeasure (Interval R), hyperbolicObjective R μ ≤ hyperbolicObjective R ν := by
      intro ν
      rw [hzero]
      exact hyperbolicObjective_nonneg R hR ν
    obtain ⟨p, q, hpq, t, ht, hμ⟩ := ordered_pair_mixture_of_minimizer R hR μ hmin
    rw [hμ] at hzero ⊢
    exact equality_of_pair_objective_zero R p q hpq t ht hzero
  · rintro (⟨p, rfl⟩ | ⟨p, rfl⟩)
    · exact hyperbolicObjective_dirac_zero R p
    · exact hyperbolicObjective_balanced_zero R p

/-- The logarithmic normalization preserves the literal equality statement. -/
theorem hyperbolicObjective_eq_zero_iff (R : ℝ) (hR : 0 < R)
    (μ : ProbabilityMeasure (Interval R)) :
    hyperbolicObjective R μ = 0 ↔
      hyperbolicNumerator R μ = 2 * Real.cosh R * geometricMean (intervalCenteredCosh R) μ := by
  have hK : 0 < 2 * Real.cosh R := mul_pos (by norm_num) (Real.cosh_pos R)
  have hN := hyperbolicNumerator_pos R hR μ
  rw [geometricMean_centered_eq_exp_integral]
  constructor
  · intro hzero
    have hlog : Real.log (hyperbolicNumerator R μ) = Real.log (2 * Real.cosh R) +
        ∫ p, intervalCenteredLogCosh R p ∂μ := by
      unfold hyperbolicObjective at hzero
      linarith
    have h := congrArg Real.exp hlog
    simpa only [Real.exp_log hN, Real.exp_add, Real.exp_log hK] using h
  · intro heq
    unfold hyperbolicObjective
    rw [heq, Real.log_mul hK.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring

/-- Theorem 3.1, in the moment notation used by the theta transfer. -/
theorem hyperbolic_geometric_mean_inequality (R : ℝ) (hR : 0 < R)
    (μ : ProbabilityMeasure (Interval R)) :
    2 * Real.cosh R * geometricMean (intervalCenteredCosh R) μ ≤ hyperbolicNumerator R μ := by
  have hobj := hyperbolicObjective_nonneg R hR μ
  have hK : 0 < 2 * Real.cosh R := mul_pos (by norm_num) (Real.cosh_pos R)
  have hlog : Real.log (2 * Real.cosh R) + (∫ p, intervalCenteredLogCosh R p ∂μ) ≤
      Real.log (hyperbolicNumerator R μ) := by
    unfold hyperbolicObjective at hobj
    linarith
  have h := Real.exp_le_exp.mpr hlog
  rw [Real.exp_add, Real.exp_log hK, Real.exp_log (hyperbolicNumerator_pos R hR μ)] at h
  rw [geometricMean_centered_eq_exp_integral]
  exact h

/-- Theorem 3.1, with all four fourth powers written literally. -/
theorem hyperbolic_geometric_mean_inequality_literal (R : ℝ) (hR : 0 < R)
    (μ : ProbabilityMeasure (Interval R)) :
    2 * Real.cosh R * geometricMean (intervalCenteredCosh R) μ ≤
      geometricMean (intervalCosh R) μ ^ 4 + geometricMean (intervalReflectedCosh R) μ ^ 4 -
        geometricMean (intervalSinh R) μ ^ 4 - geometricMean (intervalReflectedSinh R) μ ^ 4 := by
  have h := hyperbolic_geometric_mean_inequality R hR μ
  unfold hyperbolicNumerator at h
  erw [geometricMoment_nat 4 (intervalCosh R) μ,
    geometricMoment_nat 4 (intervalReflectedCosh R) μ,
    geometricMoment_nat 4 (intervalSinh R) μ,
    geometricMoment_nat 4 (intervalReflectedSinh R) μ] at h
  exact h

/-- Theorem 3.1, exact equality for arbitrary probability measures. -/
theorem hyperbolic_geometric_mean_equality_iff (R : ℝ) (hR : 0 < R)
    (μ : ProbabilityMeasure (Interval R)) :
    hyperbolicNumerator R μ = 2 * Real.cosh R * geometricMean (intervalCenteredCosh R) μ ↔
      HyperbolicEquality R μ := by
  rw [← hyperbolicObjective_eq_zero_iff R hR μ]
  exact hyperbolicObjective_eq_zero_iff_equality R hR μ

theorem hyperbolic_geometric_mean_equality_literal_iff (R : ℝ) (hR : 0 < R)
    (μ : ProbabilityMeasure (Interval R)) :
    geometricMean (intervalCosh R) μ ^ 4 + geometricMean (intervalReflectedCosh R) μ ^ 4 -
        geometricMean (intervalSinh R) μ ^ 4 - geometricMean (intervalReflectedSinh R) μ ^ 4 =
      2 * Real.cosh R * geometricMean (intervalCenteredCosh R) μ ↔ HyperbolicEquality R μ := by
  have h := hyperbolic_geometric_mean_equality_iff R hR μ
  unfold hyperbolicNumerator at h
  erw [geometricMoment_nat 4 (intervalCosh R) μ,
    geometricMoment_nat 4 (intervalReflectedCosh R) μ,
    geometricMoment_nat 4 (intervalSinh R) μ,
    geometricMoment_nat 4 (intervalReflectedSinh R) μ] at h
  exact h

end PaperVerification.Hyperbolic

#print axioms PaperVerification.Hyperbolic.hyperbolic_geometric_mean_inequality_literal
#print axioms PaperVerification.Hyperbolic.hyperbolic_geometric_mean_equality_literal_iff
