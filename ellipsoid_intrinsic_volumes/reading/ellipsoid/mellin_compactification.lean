module

public import Ellipsoid.CoefficientCompactification

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators ContDiff

namespace EllipsoidVerification

theorem compactified_mellin_integrand {n : ℕ} {e : Coefficients n}
    (he : e ∈ positiveCoefficientDomain n) (s r : ℝ) {u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    |(1 - u) ^ (-2 : ℤ)| *
      (positiveCompactification u ^ (r - 1) *
        coefficientPolynomial e (positiveCompactification u) ^ (-s)) =
      compactMellinWeight n s r u * homogeneousCoefficientPolynomial e u ^ (-s) := by
  have hv : 0 < 1 - u := sub_pos.mpr hu.2
  have hq : 0 < homogeneousCoefficientPolynomial e u := he u ⟨hu.1.le, hu.2.le⟩
  have ht : 0 < positiveCompactification u := div_pos hu.1 hv
  have hQ : coefficientPolynomial e (positiveCompactification u) =
      homogeneousCoefficientPolynomial e u / (1 - u) ^ (2 * n) := by
    apply (eq_div_iff (pow_ne_zero _ hv.ne')).2
    simpa only [positiveCompactification, mul_comm] using
      (homogeneousCoefficientPolynomial_compactification e hu.2.ne).symm
  rw [hQ]
  have hlog : Real.log (homogeneousCoefficientPolynomial e u / (1 - u) ^ (2 * n)) =
      Real.log (homogeneousCoefficientPolynomial e u) - (2 * n : ℝ) * Real.log (1 - u) := by
    rw [Real.log_div hq.ne' (pow_ne_zero _ hv.ne'), Real.log_pow]
    norm_cast
  have hjac : |(1 - u) ^ (-2 : ℤ)| = Real.exp (-2 * Real.log (1 - u)) := by
    rw [abs_of_pos (zpow_pos hv _), ← Real.rpow_intCast]
    rw [Real.rpow_def_of_pos hv]
    congr 1
    push_cast
    ring
  rw [hjac, Real.rpow_def_of_pos ht,
    Real.rpow_def_of_pos (div_pos hq (pow_pos hv _)), hlog,
    show Real.log (positiveCompactification u) = Real.log u - Real.log (1 - u) by
      exact Real.log_div hu.1.ne' hv.ne']
  unfold compactMellinWeight
  rw [Real.rpow_def_of_pos hu.1, Real.rpow_def_of_pos hv, Real.rpow_def_of_pos hq]
  simp only [← Real.exp_add]
  congr 1
  push_cast
  ring

theorem coefficientMellinPower_eq_compactMellinPower {n : ℕ} {e : Coefficients n}
    (he : e ∈ positiveCoefficientDomain n) (s r : ℝ) :
    coefficientMellinPower e s r = compactMellinPower e s r := by
  rw [coefficientMellinPower, ← positiveCompactification_image,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
      (fun u hu => (hasDerivAt_positiveCompactification hu.2.ne).hasDerivWithinAt)
      positiveCompactification_injOn]
  rw [compactMellinPower, integral_compactUnitInterval
    (fun u : ℝ => compactMellinWeight n s r u *
      homogeneousCoefficientPolynomial e u ^ (-s)), integral_Icc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u hu
  exact compactified_mellin_integrand he s r hu

theorem integrable_coefficientMellinPower {n : ℕ} {e : Coefficients n}
    (he : e ∈ positiveCoefficientDomain n) {s r : ℝ}
    (hr : 0 < r) (hrn : r < 2 * n * s) :
    IntegrableOn (fun t : ℝ => t ^ (r - 1) * coefficientPolynomial e t ^ (-s)) (Ioi 0) := by
  let W : Set (Coefficients n × ℝ) := {z | 0 < homogeneousCoefficientPolynomial z.1 z.2}
  have hF : ContinuousOn
      (fun z : Coefficients n × ℝ => homogeneousCoefficientPolynomial z.1 z.2 ^ (-s)) W := by
    apply (contDiff_homogeneousCoefficientPolynomial (n := n) 0).continuous.continuousOn.rpow_const
    intro z hz
    exact Or.inl hz.ne'
  have hi := TauCeti.integrable_smul_of_continuousOn
    (compactMellinWeight_integrable hr hrn)
    (continuous_subtype_val : Continuous (fun u : CompactUnitInterval => (u : ℝ))) hF
    (fun u => he u u.property)
  have hic : IntegrableOn (fun u : ℝ => compactMellinWeight n s r u *
      homogeneousCoefficientPolynomial e u ^ (-s)) (Icc (0 : ℝ) 1) := by
    apply (integrable_compactUnitInterval_iff _).1
    simpa only [smul_eq_mul] using hi
  rw [← positiveCompactification_image]
  apply (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
    (fun u hu => (hasDerivAt_positiveCompactification hu.2.ne).hasDerivWithinAt)
    positiveCompactification_injOn _).2
  apply (hic.mono_set Ioo_subset_Icc_self).congr_fun
  · intro u hu
    exact (compactified_mellin_integrand he s r hu).symm
  · exact measurableSet_Ioo

theorem contDiffOn_coefficientMellinPower {n : ℕ} {s r : ℝ}
    (hr : 0 < r) (hrn : r < 2 * n * s) :
    ContDiffOn ℝ ∞ (fun e : Coefficients n => coefficientMellinPower e s r)
      (positiveCoefficientDomain n) :=
  (contDiffOn_compactMellinPower hr hrn).congr
    (fun e he => coefficientMellinPower_eq_compactMellinPower he s r)

theorem integrable_mellinMoment {n : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) {r : ℝ} (hr : 0 < r) (hrn : r < 3 * n) :
    IntegrableOn (fun t : ℝ => t ^ (r - 1) * coefficientPolynomial e t ^ (-(3 / 2 : ℝ)))
      (Ioi 0) := by
  apply integrable_coefficientMellinPower (admissible_mem_positiveCoefficientDomain he) hr
  nlinarith

theorem contDiffOn_mellinMoment {n : ℕ} {r : ℝ} (hr : 0 < r) (hrn : r < 3 * n) :
    ContDiffOn ℝ ∞ (fun e : Coefficients n => mellinMoment e r) (positiveCoefficientDomain n) := by
  exact contDiffOn_coefficientMellinPower hr (by nlinarith)

end EllipsoidVerification
