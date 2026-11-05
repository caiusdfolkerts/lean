module

public import Ellipsoid.MellinCompactification
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace EllipsoidVerification

def homogeneousCoefficientEvaluation (n : ℕ) (u : ℝ) : Coefficients n →L[ℝ] ℝ :=
  ∑ j : Fin (n + 1), (u ^ (2 * j.val) * (1 - u) ^ (2 * n - 2 * j.val)) •
    ContinuousLinearMap.proj j

@[simp] theorem homogeneousCoefficientEvaluation_apply {n : ℕ} (u : ℝ)
    (e : Coefficients n) :
    homogeneousCoefficientEvaluation n u e = homogeneousCoefficientPolynomial e u := by
  simp [homogeneousCoefficientEvaluation, homogeneousCoefficientPolynomial,
    mul_comm, mul_left_comm, mul_assoc]

@[fun_prop] theorem continuous_homogeneousCoefficientEvaluation (n : ℕ) :
    Continuous (homogeneousCoefficientEvaluation n) := by
  unfold homogeneousCoefficientEvaluation
  fun_prop

theorem hasFDerivAt_homogeneousCoefficientPolynomial {n : ℕ}
    (e : Coefficients n) (u : ℝ) :
    HasFDerivAt (fun e : Coefficients n => homogeneousCoefficientPolynomial e u)
      (homogeneousCoefficientEvaluation n u) e := by
  have heq : (fun d : Coefficients n => homogeneousCoefficientPolynomial d u) =
      homogeneousCoefficientEvaluation n u := by
    funext d
    exact (homogeneousCoefficientEvaluation_apply u d).symm
  rw [heq]
  exact (homogeneousCoefficientEvaluation n u).hasFDerivAt

theorem fderiv_homogeneousCoefficient_rpow {n : ℕ} {e : Coefficients n} {u : ℝ}
    (hu : 0 < homogeneousCoefficientPolynomial e u) (s : ℝ) :
    fderiv ℝ (fun e : Coefficients n => homogeneousCoefficientPolynomial e u ^ (-s)) e =
      (-s * homogeneousCoefficientPolynomial e u ^ (-s - 1)) •
        homogeneousCoefficientEvaluation n u :=
  ((hasFDerivAt_homogeneousCoefficientPolynomial e u).rpow_const (Or.inl hu.ne')).fderiv

theorem hasFDerivAt_coefficientMellinPower {n : ℕ} {e : Coefficients n}
    (he : e ∈ positiveCoefficientDomain n) {s r : ℝ}
    (hr : 0 < r) (hrn : r < 2 * n * s) :
    HasFDerivAt (fun e : Coefficients n => coefficientMellinPower e s r)
      (∫ u : CompactUnitInterval, compactMellinWeight n s r u •
        ((-s * homogeneousCoefficientPolynomial e u ^ (-s - 1)) •
          homogeneousCoefficientEvaluation n u)) e := by
  let W : Set (Coefficients n × ℝ) :=
    {z | 0 < homogeneousCoefficientPolynomial z.1 z.2}
  have hW : IsOpen W := isOpen_lt continuous_const
    (contDiff_homogeneousCoefficientPolynomial (n := n) 0).continuous
  have hF : ContDiffOn ℝ 1
      (fun z : Coefficients n × ℝ => homogeneousCoefficientPolynomial z.1 z.2 ^ (-s)) W := by
    apply (contDiff_homogeneousCoefficientPolynomial (n := n) 1).contDiffOn.rpow_const_of_ne
    intro z hz
    exact hz.ne'
  have h := TauCeti.hasFDerivAt_integral_smul_of_contDiffOn
    (compactMellinWeight_integrable hr hrn)
    (continuous_subtype_val : Continuous (fun u : CompactUnitInterval => (u : ℝ))) hW hF
    (fun u => he u u.property)
  have hderiv :
      (∫ u : CompactUnitInterval, compactMellinWeight n s r u •
        fderiv ℝ (fun e : Coefficients n => homogeneousCoefficientPolynomial e u ^ (-s)) e) =
      ∫ u : CompactUnitInterval, compactMellinWeight n s r u •
        ((-s * homogeneousCoefficientPolynomial e u ^ (-s - 1)) •
          homogeneousCoefficientEvaluation n u) := by
    apply integral_congr_ae
    exact ae_of_all _ fun u => by
      dsimp only
      rw [fderiv_homogeneousCoefficient_rpow (he u u.property) s]
  rw [hderiv] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [(isOpen_positiveCoefficientDomain n).mem_nhds he] with e he
  exact coefficientMellinPower_eq_compactMellinPower he s r

set_option backward.isDefEq.respectTransparency false in
theorem compact_mellin_derivative_integrable {n : ℕ} {e : Coefficients n}
    (he : e ∈ positiveCoefficientDomain n) {s r : ℝ}
    (hr : 0 < r) (hrn : r < 2 * n * s) :
    Integrable (fun u : CompactUnitInterval => compactMellinWeight n s r u •
      ((-s * homogeneousCoefficientPolynomial e u ^ (-s - 1)) •
        homogeneousCoefficientEvaluation n u)) volume := by
  apply TauCeti.integrable_smul_of_continuousOn
    (compactMellinWeight_integrable hr hrn) continuous_subtype_val
    (W := {z : Coefficients n × ℝ | 0 < homogeneousCoefficientPolynomial z.1 z.2})
    (F := fun z : Coefficients n × ℝ =>
      (-s * homogeneousCoefficientPolynomial z.1 z.2 ^ (-s - 1)) •
        homogeneousCoefficientEvaluation n z.2)
    (x := e)
  · have hpow : ContinuousOn
        (fun z : Coefficients n × ℝ => homogeneousCoefficientPolynomial z.1 z.2 ^ (-s - 1))
        {z | 0 < homogeneousCoefficientPolynomial z.1 z.2} :=
      (contDiff_homogeneousCoefficientPolynomial (n := n) 0).continuous.continuousOn.rpow_const
        (fun z hz => Or.inl hz.ne')
    have hscalar : ContinuousOn
        (fun z : Coefficients n × ℝ => -s * homogeneousCoefficientPolynomial z.1 z.2 ^ (-s - 1))
        {z | 0 < homogeneousCoefficientPolynomial z.1 z.2} := by
      exact (continuousOn_const (c := -s)).fun_mul hpow
    have hlinear : ContinuousOn
        (fun z : Coefficients n × ℝ => homogeneousCoefficientEvaluation n z.2)
        {z | 0 < homogeneousCoefficientPolynomial z.1 z.2} :=
      ((continuous_homogeneousCoefficientEvaluation n).comp continuous_snd).continuousOn
    exact hscalar.fun_smul hlinear
  · intro u
    exact he u u.property

theorem compact_mellin_shift_identity (n : ℕ) (s r : ℝ) (j : Fin (n + 1))
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    compactMellinWeight n s r u *
      (u ^ (2 * j.val) * (1 - u) ^ (2 * n - 2 * j.val)) =
        compactMellinWeight n (s + 1) (r + 2 * j.val) u := by
  have hv : 0 < 1 - u := sub_pos.mpr hu.2
  unfold compactMellinWeight
  rw [← Real.rpow_natCast, ← Real.rpow_natCast]
  rw [show u ^ (r - 1) * (1 - u) ^ (2 * n * s - r - 1) *
      (u ^ ((2 * j.val : ℕ) : ℝ) * (1 - u) ^ ((2 * n - 2 * j.val : ℕ) : ℝ)) =
      (u ^ (r - 1) * u ^ ((2 * j.val : ℕ) : ℝ)) *
        ((1 - u) ^ (2 * n * s - r - 1) *
          (1 - u) ^ ((2 * n - 2 * j.val : ℕ) : ℝ)) by ring]
  rw [← Real.rpow_add hu.1, ← Real.rpow_add hv]
  rw [Nat.cast_sub (by omega : 2 * j.val ≤ 2 * n)]
  congr 1 <;> push_cast <;> ring

/-- Every partial derivative of the Mellin transform is another convergent
Mellin transform. The allowed range is precisely `0 < r < 2ns`. -/
theorem fderiv_coefficientMellinPower_single {n : ℕ} {e : Coefficients n}
    (he : e ∈ positiveCoefficientDomain n) {s r : ℝ}
    (hr : 0 < r) (hrn : r < 2 * n * s) (j : Fin (n + 1)) :
    fderiv ℝ (fun e : Coefficients n => coefficientMellinPower e s r) e (Pi.single j 1) =
      -s * coefficientMellinPower e (s + 1) (r + 2 * j.val) := by
  rw [(hasFDerivAt_coefficientMellinPower he hr hrn).fderiv,
    ContinuousLinearMap.integral_apply (compact_mellin_derivative_integrable he hr hrn),
    coefficientMellinPower_eq_compactMellinPower he, compactMellinPower, ← integral_const_mul]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul,
    homogeneousCoefficientEvaluation, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.proj_apply, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [integral_compactUnitInterval (fun u : ℝ =>
      compactMellinWeight n s r u *
        (-s * homogeneousCoefficientPolynomial e u ^ (-s - 1) *
          (u ^ (2 * j.val) * (1 - u) ^ (2 * n - 2 * j.val)))),
    integral_compactUnitInterval (fun u : ℝ =>
      -s * (compactMellinWeight n (s + 1) (r + 2 * j.val) u *
        homogeneousCoefficientPolynomial e u ^ (-(s + 1)))),
    integral_Icc_eq_integral_Ioo, integral_Icc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u hu
  dsimp only
  rw [show -(s + 1) = -s - 1 by ring,
    ← compact_mellin_shift_identity n s r j hu]
  ring

end EllipsoidVerification
