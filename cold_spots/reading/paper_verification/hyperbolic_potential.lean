module
public import PaperVerification.HyperbolicLocalization
public import PaperVerification.MinimaLocalization
@[expose] public section
/-! # Localization for the exact hyperbolic first-variation potential

This file applies the general calculus lemma to the potential of Lemma 4.1,
including the finite endpoint cases B=0 and D=0. The measure-theoretic first
variation is separate; this file does not assume its conclusion as a theorem
about the Gaussian or hyperbolic inequality.
-/

noncomputable section

namespace PaperVerification.Hyperbolic

open Real Set

/-- Continuity on every interval on which the endpoint logarithms have finite
limits. A zero coefficient is handled before evaluating continuity of log sinh. -/
theorem continuousOn_variationPotential
    (R A C B D F a c : ℝ)
    (hB : B = 0 ∨ 0 < a) (hD : D = 0 ∨ c < R) :
    ContinuousOn (variationPotential R A C B D F) (Icc a c) := by
  have hcosh : Continuous (fun t : ℝ => Real.log (Real.cosh t)) :=
    Real.continuous_cosh.log (fun t => (Real.cosh_pos t).ne')
  have hcoshR : Continuous (fun t : ℝ => Real.log (Real.cosh (R - t))) :=
    hcosh.comp (continuous_const.sub continuous_id)
  have hcoshV : Continuous (fun t : ℝ => Real.log (Real.cosh (2 * t - R))) :=
    hcosh.comp ((continuous_const.mul continuous_id).sub continuous_const)
  have hBcont : ContinuousOn (fun t : ℝ => B * Real.log (Real.sinh t)) (Icc a c) := by
    rcases hB with rfl | ha
    · simpa only [zero_mul] using
        (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ))).continuousOn
    · exact continuousOn_const.mul (Real.continuous_sinh.continuousOn.log
        (fun t ht => Real.sinh_ne_zero.mpr (ne_of_gt (ha.trans_le ht.1))))
  have hDcont : ContinuousOn (fun t : ℝ => D * Real.log (Real.sinh (R - t))) (Icc a c) := by
    rcases hD with rfl | hc
    · simpa only [zero_mul] using
        (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ))).continuousOn
    · exact continuousOn_const.mul
        ((Real.continuous_sinh.comp (continuous_const.sub continuous_id)).continuousOn.log
          (fun t ht => Real.sinh_ne_zero.mpr (ne_of_gt (sub_pos.mpr (ht.2.trans_lt hc)))))
  exact (continuousOn_const.mul
    ((((continuousOn_const.mul hcosh.continuousOn).add
      (continuousOn_const.mul hcoshR.continuousOn)).sub hBcont).sub hDcont)).sub
        hcoshV.continuousOn

theorem differentiableOn_variationPotential (R A C B D F : ℝ) :
    DifferentiableOn ℝ (variationPotential R A C B D F) (Ioo 0 R) :=
  fun p hp => (hasDerivAt_variationPotential R A C B D F p hp).differentiableAt.differentiableWithinAt

theorem differentiableOn_deriv_variationPotential (R A C B D F : ℝ) :
    DifferentiableOn ℝ (deriv (variationPotential R A C B D F)) (Ioo 0 R) := by
  have hdiff : DifferentiableOn ℝ (variationDerivative R A C B D F) (Ioo 0 R) :=
    fun p hp => (hasDerivAt_variationDerivative R A C B D F p hp).differentiableAt.differentiableWithinAt
  apply hdiff.congr
  intro p hp
  exact (hasDerivAt_variationPotential R A C B D F p hp).deriv

/-- The actual potential in Lemma 4.1 cannot have three global minima. The
admissibility alternatives explicitly retain all finite endpoint cases. -/
theorem no_three_minima_variationPotential
    (R A C B D F a b c : ℝ)
    (hA : 0 < A) (hC : 0 < C) (hB : 0 ≤ B) (hD : 0 ≤ D) (hF : 0 < F)
    (ha : 0 ≤ a) (hc : c ≤ R) (hab : a < b) (hbc : b < c)
    (hBa : B = 0 ∨ 0 < a) (hDc : D = 0 ∨ c < R)
    (hmin : ∀ x ∈ Icc a c,
      variationPotential R A C B D F a ≤ variationPotential R A C B D F x)
    (hb : variationPotential R A C B D F b = variationPotential R A C B D F a)
    (hend : variationPotential R A C B D F c = variationPotential R A C B D F a) :
    False := by
  have hsub : Ioo a c ⊆ Ioo 0 R := by
    intro x hx
    exact ⟨ha.trans_lt hx.1, hx.2.trans_le hc⟩
  apply no_three_global_minima_of_strictConvex_normalized_curvature
    (f := variationPotential R A C B D F)
    (h := curvatureModel R A C B D F)
    (w := fun p => 4 / Real.cosh (2 * p - R) ^ 2)
    hab hbc (continuousOn_variationPotential R A C B D F a c hBa hDc)
    ((differentiableOn_variationPotential R A C B D F).mono hsub)
    ((differentiableOn_deriv_variationPotential R A C B D F).mono hsub)
    (fun p hp => div_pos (by norm_num) (pow_pos (Real.cosh_pos _) 2))
    (fun p hp => (deriv2_variationPotential R A C B D F p (hsub hp)).trans
      (variationSecondDerivative_eq_curvatureModel R A C B D F p hF.ne' (hsub hp)))
    ((strictConvexOn_curvatureModel R A C B D F hA hC hB hD hF).subset hsub
      (convex_Ioo a c)) hmin hb hend

end PaperVerification.Hyperbolic

#print axioms PaperVerification.Hyperbolic.no_three_minima_variationPotential
