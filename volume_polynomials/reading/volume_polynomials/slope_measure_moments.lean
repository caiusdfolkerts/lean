module

public import VolumePolynomials.ExponentialKernel
public import VolumePolynomials.MatrixDeterminantReduction
public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure

@[expose] public section

/-!
# Exponential moment bounds for arbitrary finite slope measures

Admissibility uses nonnegative Lebesgue integrals. Thus an infinite exponential
moment cannot be mistaken for a vanishing Bochner integral. The real integrals
and the weighted contraction are derived only after integrability is proved.
-/

open MeasureTheory Set Matrix
open scoped ENNReal BigOperators MeasureTheory InnerProductSpace RealInnerProductSpace

namespace VolumePolynomials

/-- The exponential moment, with its genuine extended nonnegative value. -/
noncomputable def slopeExponentialMoment (μ : Measure ℝ) (a : ℝ) : ℝ≥0∞ :=
  ∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (a * x)) ∂μ

theorem slopeExponentialMoment_integrable {μ : Measure ℝ} {a : ℝ}
    (h : slopeExponentialMoment μ a < ∞) :
    Integrable (fun x : ℝ => Real.exp (a * x)) μ := by
  refine ⟨by fun_prop, (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)).mpr h⟩

theorem integral_exponential_eq_moment (μ : Measure ℝ) (a : ℝ) :
    (∫ x : ℝ, Real.exp (a * x) ∂μ) = (slopeExponentialMoment μ a).toReal := by
  exact integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le) (by fun_prop)

theorem integral_exponential_le_one {μ : Measure ℝ} {a : ℝ}
    (h : slopeExponentialMoment μ a ≤ 1) :
    (∫ x : ℝ, Real.exp (a * x) ∂μ) ≤ 1 := by
  rw [integral_exponential_eq_moment]
  simpa using ENNReal.toReal_mono (by norm_num : (1 : ℝ≥0∞) ≠ ∞) h

theorem slopeExponentialMoment_conv (μ ν : Measure ℝ) [SFinite ν] (a : ℝ) :
    slopeExponentialMoment (μ ∗ ν) a =
      slopeExponentialMoment μ a * slopeExponentialMoment ν a := by
  unfold slopeExponentialMoment
  rw [Measure.lintegral_conv (by fun_prop)]
  have hm : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (a * x))) := by fun_prop
  simp_rw [mul_add, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le,
    lintegral_const_mul _ hm]
  exact lintegral_mul_const _ hm

/-- Squared Cauchy--Schwarz with the actual real integrals. -/
theorem integral_mul_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * ∫ x, g x ^ 2 ∂μ := by
  let u := hf.toLp f
  let v := hg.toLp g
  have hu : (u : α → ℝ) =ᵐ[μ] f := hf.coeFn_toLp
  have hv : (v : α → ℝ) =ᵐ[μ] g := hg.coeFn_toLp
  have hinner : ⟪u, v⟫_ℝ = ∫ x, f x * g x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hu, hv] with x hux hvx
    simp [hux, hvx, mul_comm]
  have hnu : ‖u‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hu] with x hx
    simp [hx, pow_two]
  have hnv : ‖v‖ ^ 2 = ∫ x, g x ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hv] with x hx
    simp [hx, pow_two]
  have hCS := abs_real_inner_le_norm u v
  have hsquare := (sq_le_sq₀ (abs_nonneg ⟪u, v⟫_ℝ)
    (mul_nonneg (norm_nonneg u) (norm_nonneg v))).mpr hCS
  rw [sq_abs, mul_pow, hinner, hnu, hnv] at hsquare
  exact hsquare

/-- The mass is bounded by the geometric mean of the reciprocal exponential moments. -/
theorem slope_mass_sq_le_moments (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hp : slopeExponentialMoment μ (-1 / 2) < ∞)
    (hq : slopeExponentialMoment μ (1 / 2) < ∞) :
    (μ.real univ) ^ 2 ≤
      (∫ x : ℝ, Real.exp ((-1 / 2) * x) ∂μ) * ∫ x : ℝ, Real.exp ((1 / 2) * x) ∂μ := by
  have hf : MemLp (fun x : ℝ => Real.exp (-x / 4)) 2 μ := by
    apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
    convert slopeExponentialMoment_integrable hp using 1
    funext x
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hg : MemLp (fun x : ℝ => Real.exp (x / 4)) 2 μ := by
    apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
    convert slopeExponentialMoment_integrable hq using 1
    funext x
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hprod (x : ℝ) : Real.exp (-x / 4) * Real.exp (x / 4) = 1 := by
    have he : -x / 4 + x / 4 = 0 := by ring
    rw [← Real.exp_add, he, Real.exp_zero]
  have hfsq (x : ℝ) : Real.exp (-x / 4) ^ 2 = Real.exp ((-1 / 2) * x) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hgsq (x : ℝ) : Real.exp (x / 4) ^ 2 = Real.exp ((1 / 2) * x) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  simpa only [hprod, hfsq, hgsq, integral_const, smul_eq_mul, mul_one] using
    integral_mul_sq_le hf hg

/-- The measure-matrix hypothesis in Section 4.2, with its full measure semantics. -/
def IsAdmissibleSlopeMatrix (ρ : Matrix (Fin 2) (Fin 2) (Measure ℝ)) : Prop :=
  (∀ i, ∑ j, slopeExponentialMoment (ρ i j) (-1 / 2) ≤ 1) ∧
    (∀ j, ∑ i, slopeExponentialMoment (ρ i j) (1 / 2) ≤ 1)

noncomputable def slopeFourierMatrix (ρ : Matrix (Fin 2) (Fin 2) (Measure ℝ))
    (ξ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := fun i j => charFun (ρ i j) ξ

noncomputable def slopeMassMatrix (ρ : Matrix (Fin 2) (Fin 2) (Measure ℝ)) :
    Matrix (Fin 2) (Fin 2) ℝ := fun i j => (ρ i j).real univ

theorem admissible_entry_negative_moment {ρ : Matrix (Fin 2) (Fin 2) (Measure ℝ)}
    (hρ : IsAdmissibleSlopeMatrix ρ) (i j : Fin 2) :
    slopeExponentialMoment (ρ i j) (-1 / 2) ≤ 1 :=
  (Finset.single_le_sum (fun k _ => (zero_le : 0 ≤ slopeExponentialMoment (ρ i k) (-1 / 2)))
    (Finset.mem_univ j)).trans (hρ.1 i)

theorem admissible_entry_positive_moment {ρ : Matrix (Fin 2) (Fin 2) (Measure ℝ)}
    (hρ : IsAdmissibleSlopeMatrix ρ) (i j : Fin 2) :
    slopeExponentialMoment (ρ i j) (1 / 2) ≤ 1 :=
  (Finset.single_le_sum (fun k _ => (zero_le : 0 ≤ slopeExponentialMoment (ρ k j) (1 / 2)))
    (Finset.mem_univ i)).trans (hρ.2 j)

theorem normSq_slopeFourier_le_mass (ρ : Matrix (Fin 2) (Fin 2) (Measure ℝ))
    (ξ : ℝ) (i j : Fin 2) :
    Complex.normSq (slopeFourierMatrix ρ ξ i j) ≤ (slopeMassMatrix ρ i j) ^ 2 := by
  rw [Complex.normSq_eq_norm_sq]
  exact (sq_le_sq₀ (norm_nonneg _) measureReal_nonneg).mpr (norm_charFun_le ξ)

/-- Lemma 4.2, proved directly for the complete class of admissible finite measures. -/
theorem admissible_fourier_contraction
    (ρ : Matrix (Fin 2) (Fin 2) (Measure ℝ)) [∀ i j, IsFiniteMeasure (ρ i j)]
    (hρ : IsAdmissibleSlopeMatrix ρ) (ξ : ℝ) :
    IsEuclideanContraction (slopeFourierMatrix ρ ξ) := by
  let p : Matrix (Fin 2) (Fin 2) ℝ := fun i j => ∫ x : ℝ, Real.exp ((-1 / 2) * x) ∂ρ i j
  let q : Matrix (Fin 2) (Fin 2) ℝ := fun i j => ∫ x : ℝ, Real.exp ((1 / 2) * x) ∂ρ i j
  have hp0 : ∀ i j, 0 ≤ p i j := fun i j => integral_nonneg fun x => (Real.exp_pos _).le
  have hq0 : ∀ i j, 0 ≤ q i j := fun i j => integral_nonneg fun x => (Real.exp_pos _).le
  have hrow : ∀ i, ∑ j, p i j ≤ 1 := by
    intro i
    have hfinite : ∀ j ∈ (Finset.univ : Finset (Fin 2)),
        slopeExponentialMoment (ρ i j) (-1 / 2) ≠ ∞ := fun j _ =>
      ((admissible_entry_negative_moment hρ i j).trans_lt (by norm_num)).ne
    have hreal := ENNReal.toReal_mono (by norm_num : (1 : ℝ≥0∞) ≠ ∞) (hρ.1 i)
    simpa only [p, integral_exponential_eq_moment, ENNReal.toReal_sum hfinite,
      ENNReal.toReal_one] using hreal
  have hcol : ∀ j, ∑ i, q i j ≤ 1 := by
    intro j
    have hfinite : ∀ i ∈ (Finset.univ : Finset (Fin 2)),
        slopeExponentialMoment (ρ i j) (1 / 2) ≠ ∞ := fun i _ =>
      ((admissible_entry_positive_moment hρ i j).trans_lt (by norm_num)).ne
    have hreal := ENNReal.toReal_mono (by norm_num : (1 : ℝ≥0∞) ≠ ∞) (hρ.2 j)
    simpa only [q, integral_exponential_eq_moment, ENNReal.toReal_sum hfinite,
      ENNReal.toReal_one] using hreal
  apply isEuclideanContraction_of_weighted_entries _ p q hp0 hq0 _ hrow hcol
  intro i j
  exact (normSq_slopeFourier_le_mass ρ ξ i j).trans
    (slope_mass_sq_le_moments (ρ i j)
      ((admissible_entry_negative_moment hρ i j).trans_lt (by norm_num))
      ((admissible_entry_positive_moment hρ i j).trans_lt (by norm_num)))

/-- The literal operator-norm conclusion of Lemma 4.2. -/
theorem admissible_fourier_operatorNorm_le_one
    (ρ : Matrix (Fin 2) (Fin 2) (Measure ℝ)) [∀ i j, IsFiniteMeasure (ρ i j)]
    (hρ : IsAdmissibleSlopeMatrix ρ) (ξ : ℝ) :
    ‖(slopeFourierMatrix ρ ξ).toEuclideanLin.toContinuousLinearMap‖ ≤ 1 :=
  (isEuclideanContraction_iff_operatorNorm_le_one _).mp
    (admissible_fourier_contraction ρ hρ ξ)

theorem slopeFourierMatrix_zero (ρ : Matrix (Fin 2) (Fin 2) (Measure ℝ)) :
    slopeFourierMatrix ρ 0 = (slopeMassMatrix ρ).map Complex.ofReal := by
  ext i j
  simp only [slopeFourierMatrix, slopeMassMatrix, Matrix.map_apply, charFun_zero]

theorem admissible_mass_contraction
    (ρ : Matrix (Fin 2) (Fin 2) (Measure ℝ)) [∀ i j, IsFiniteMeasure (ρ i j)]
    (hρ : IsAdmissibleSlopeMatrix ρ) :
    IsEuclideanContraction ((slopeMassMatrix ρ).map Complex.ofReal) := by
  rw [← slopeFourierMatrix_zero]
  exact admissible_fourier_contraction ρ hρ 0

theorem admissible_fourier_domination
    (ρ : Matrix (Fin 2) (Fin 2) (Measure ℝ)) (ξ : ℝ) (i j : Fin 2) :
    Complex.normSq (slopeFourierMatrix ρ ξ i j) ≤
      Complex.normSq (((slopeMassMatrix ρ).map Complex.ofReal) i j) := by
  simpa only [Matrix.map_apply, Complex.normSq_ofReal, pow_two] using
    normSq_slopeFourier_le_mass ρ ξ i j

/-- The signed determinant measure uses actual additive convolution. -/
noncomputable def slopeDeterminantMeasure
    (ρ : Matrix (Fin 2) (Fin 2) (Measure ℝ))
    [∀ i j, IsFiniteMeasure (ρ i j)] : SignedMeasure ℝ :=
  (ρ 0 0 ∗ ρ 1 1).toSignedMeasure - (ρ 0 1 ∗ ρ 1 0).toSignedMeasure

/-- Total variation is bounded by the two positive convolution measures. -/
theorem slopeDeterminantMeasure_totalVariation_le
    (ρ : Matrix (Fin 2) (Fin 2) (Measure ℝ))
    [∀ i j, IsFiniteMeasure (ρ i j)] :
    (slopeDeterminantMeasure ρ).totalVariation ≤ (ρ 0 0 ∗ ρ 1 1) + (ρ 0 1 ∗ ρ 1 0) := by
  rw [SignedMeasure.totalVariation_eq_variation]
  simpa only [slopeDeterminantMeasure, Measure.variation_toSignedMeasure] using
    (VectorMeasure.variation_sub_le (μ := (ρ 0 0 ∗ ρ 1 1).toSignedMeasure)
      (ν := (ρ 0 1 ∗ ρ 1 0).toSignedMeasure))

/-- The determinant measure has the exact exponential-moment bound in Lemma 5.1. -/
theorem slopeDeterminantMeasure_exponential_moment
    (ρ : Matrix (Fin 2) (Fin 2) (Measure ℝ))
    [∀ i j, IsFiniteMeasure (ρ i j)] (hρ : IsAdmissibleSlopeMatrix ρ) :
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (|x| / 2))
      ∂(slopeDeterminantMeasure ρ).totalVariation) ≤ 4 := by
  have hconv (i j k l : Fin 2) :
      slopeExponentialMoment (ρ i j ∗ ρ k l) (-1 / 2) ≤ 1 ∧
        slopeExponentialMoment (ρ i j ∗ ρ k l) (1 / 2) ≤ 1 := by
    constructor
    · rw [slopeExponentialMoment_conv]
      exact (mul_le_mul' (admissible_entry_negative_moment hρ i j)
        (admissible_entry_negative_moment hρ k l)).trans_eq (one_mul 1)
    · rw [slopeExponentialMoment_conv]
      exact (mul_le_mul' (admissible_entry_positive_moment hρ i j)
        (admissible_entry_positive_moment hρ k l)).trans_eq (one_mul 1)
  have habs (x : ℝ) : Real.exp (|x| / 2) ≤ Real.exp ((-1 / 2) * x) + Real.exp ((1 / 2) * x) := by
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx]
      have heq : (1 / 2 : ℝ) * x = x / 2 := by ring
      rw [heq]
      linarith [Real.exp_pos ((-1 / 2) * x)]
    · rw [abs_of_neg (lt_of_not_ge hx)]
      have heq : (-1 / 2 : ℝ) * x = -x / 2 := by ring
      rw [heq]
      linarith [Real.exp_pos ((1 / 2) * x)]
  calc
    _ ≤ ∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (|x| / 2))
        ∂((ρ 0 0 ∗ ρ 1 1) + (ρ 0 1 ∗ ρ 1 0)) :=
      lintegral_mono' (slopeDeterminantMeasure_totalVariation_le ρ) (fun _ => le_rfl)
    _ ≤ ∫⁻ x : ℝ,
        ENNReal.ofReal (Real.exp ((-1 / 2) * x)) +
          ENNReal.ofReal (Real.exp ((1 / 2) * x))
        ∂((ρ 0 0 ∗ ρ 1 1) + (ρ 0 1 ∗ ρ 1 0)) := by
      apply lintegral_mono
      intro x
      dsimp only
      rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
      exact ENNReal.ofReal_mono (habs x)
    _ = (slopeExponentialMoment (ρ 0 0 ∗ ρ 1 1) (-1 / 2) +
          slopeExponentialMoment (ρ 0 0 ∗ ρ 1 1) (1 / 2)) +
        (slopeExponentialMoment (ρ 0 1 ∗ ρ 1 0) (-1 / 2) +
          slopeExponentialMoment (ρ 0 1 ∗ ρ 1 0) (1 / 2)) := by
      rw [lintegral_add_measure]
      have hm : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp ((-1 / 2) * x))) :=
        by fun_prop
      simp only [lintegral_add_left hm, slopeExponentialMoment]
    _ ≤ (1 + 1) + (1 + 1) := add_le_add
      (add_le_add (hconv 0 0 1 1).1 (hconv 0 0 1 1).2)
      (add_le_add (hconv 0 1 1 0).1 (hconv 0 1 1 0).2)
    _ = 4 := by norm_num

end VolumePolynomials
