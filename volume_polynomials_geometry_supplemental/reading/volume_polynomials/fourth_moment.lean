module

public import VolumePolynomials.KernelFourier
public import VolumePolynomials.KernelLogMass
public import VolumePolynomials.SlopeEntryEnergy

@[expose] public section

/-!
# The full fourth-moment estimate for admissible Fourier matrices

The entry measures are arbitrary finite Borel measures on the real line.
Every matrix, energy, mass and moment in this statement is computed from those
measures. The proof uses the actual signed determinant measure and the proved
logarithmic energy estimate; no singular-value or spectral representation is
assumed as an additional hypothesis.
-/

open MeasureTheory Set Matrix
open scoped ENNReal BigOperators InnerProductSpace RealInnerProductSpace

namespace VolumePolynomials

theorem signedSlopeFourier_zero (ν : SignedMeasure ℝ) :
    signedSlopeFourier ν 0 = (ν univ : ℂ) := by
  rw [signedSlopeFourier_jordan, charFun_zero, charFun_zero,
    SignedMeasure.apply_eq_posPart_real_sub_negPart_real ν MeasurableSet.univ,
    Complex.ofReal_sub]

theorem slopeDeterminantMeasure_mass
    (ρ : Matrix (Fin 2) (Fin 2) (Measure ℝ)) [∀ i j, IsFiniteMeasure (ρ i j)] :
    slopeDeterminantMeasure ρ univ = (slopeMassMatrix ρ).det := by
  have h := signedSlopeFourier_determinant ρ 0
  rw [signedSlopeFourier_zero, slopeFourierMatrix_zero] at h
  apply Complex.ofReal_injective
  simpa only [Matrix.det_fin_two, Matrix.map_apply, Complex.ofReal_sub,
    Complex.ofReal_mul] using h

/-- The exact second moment in Section 4.2. -/
noncomputable def slopeSecondMoment (ρ : Matrix (Fin 2) (Fin 2) (Measure ℝ)) : ℝ :=
  ∫ ξ : ℝ, matrixSecondTrace (slopeFourierMatrix ρ ξ) ∂cornerSpectralMeasure

/-- The exact fourth moment in Section 5.2. -/
noncomputable def slopeFourthMoment (ρ : Matrix (Fin 2) (Fin 2) (Measure ℝ)) : ℝ :=
  ∫ ξ : ℝ, matrixFourthTrace (slopeFourierMatrix ρ ξ) ∂cornerSpectralMeasure

theorem integrable_slopeSecondTrace
    (ρ : Matrix (Fin 2) (Fin 2) (Measure ℝ)) [∀ i j, IsFiniteMeasure (ρ i j)] :
    Integrable (fun ξ : ℝ => matrixSecondTrace (slopeFourierMatrix ρ ξ))
      cornerSpectralMeasure := by
  simp only [matrixSecondTrace_eq_sum, Fin.sum_univ_two, slopeFourierMatrix]
  exact ((integrable_spectral_normSq (ρ 0 0)).add (integrable_spectral_normSq (ρ 0 1))).add
    ((integrable_spectral_normSq (ρ 1 0)).add (integrable_spectral_normSq (ρ 1 1)))

theorem slopeSecondMoment_eq_entry_energies
    (ρ : Matrix (Fin 2) (Fin 2) (Measure ℝ)) [∀ i j, IsFiniteMeasure (ρ i j)] :
    slopeSecondMoment ρ = ∑ i, ∑ j, ‖cornerMean (ρ i j)‖ ^ 2 := by
  simp only [slopeSecondMoment, matrixSecondTrace_eq_sum, Fin.sum_univ_two, slopeFourierMatrix]
  erw [integral_add
      ((integrable_spectral_normSq (ρ 0 0)).add (integrable_spectral_normSq (ρ 0 1)))
      ((integrable_spectral_normSq (ρ 1 0)).add (integrable_spectral_normSq (ρ 1 1))),
    integral_add (integrable_spectral_normSq (ρ 0 0)) (integrable_spectral_normSq (ρ 0 1)),
    integral_add (integrable_spectral_normSq (ρ 1 0)) (integrable_spectral_normSq (ρ 1 1))]
  simp only [corner_spectral_energy]

theorem integrable_slopeDeterminantEnergy
    (ρ : Matrix (Fin 2) (Fin 2) (Measure ℝ)) [∀ i j, IsFiniteMeasure (ρ i j)]
    (hρ : IsAdmissibleSlopeMatrix ρ) :
    Integrable (fun ξ : ℝ => matrixDeterminantEnergy (slopeFourierMatrix ρ ξ))
      cornerSpectralMeasure := by
  apply (integrable_const (1 : ℝ)).mono' ?_ ?_
  · dsimp [matrixDeterminantEnergy, slopeFourierMatrix]
    simp only [Matrix.det_fin_two, slopeFourierMatrix, ← Complex.sq_norm]
    fun_prop
  · exact Filter.Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (matrixDeterminantEnergy_nonneg _)]
      exact contraction_determinant_le_one _ (admissible_fourier_contraction ρ hρ ξ)

theorem integrable_slopeFourthTrace
    (ρ : Matrix (Fin 2) (Fin 2) (Measure ℝ)) [∀ i j, IsFiniteMeasure (ρ i j)]
    (hρ : IsAdmissibleSlopeMatrix ρ) :
    Integrable (fun ξ : ℝ => matrixFourthTrace (slopeFourierMatrix ρ ξ))
      cornerSpectralMeasure := by
  apply (integrable_const (4 : ℝ)).mono' ?_ ?_
  · simp_rw [matrixFourthTrace_eq]
    exact ((integrable_slopeSecondTrace ρ).aestronglyMeasurable.pow 2).sub
      ((integrable_slopeDeterminantEnergy ρ hρ).aestronglyMeasurable.const_mul 2)
  · apply Filter.Eventually.of_forall
    intro ξ
    rw [Real.norm_eq_abs, abs_of_nonneg (matrixFourthTrace_nonneg _), matrixFourthTrace_eq]
    have ht := matrixSecondTrace_nonneg (slopeFourierMatrix ρ ξ)
    have hd := matrixDeterminantEnergy_nonneg (slopeFourierMatrix ρ ξ)
    have hF := admissible_fourier_contraction ρ hρ ξ
    have hlow := contraction_determinant_lower _ hF
    have hupp := contraction_determinant_le_one _ hF
    have ht2 : matrixSecondTrace (slopeFourierMatrix ρ ξ) ≤ 2 := by linarith
    nlinarith [mul_nonneg ht (sub_nonneg.mpr ht2)]

/-- Both integrated matrix inequalities use the actual spectral probability measure. -/
theorem slopeFourthMoment_determinant_bounds
    (ρ : Matrix (Fin 2) (Fin 2) (Measure ℝ)) [∀ i j, IsFiniteMeasure (ρ i j)]
    (hρ : IsAdmissibleSlopeMatrix ρ) :
    slopeFourthMoment ρ ≤ 1 + (slopeMassMatrix ρ).det ^ 2 * (slopeSecondMoment ρ - 1) ∧
      (1 - (slopeMassMatrix ρ).det ^ 2) * cornerSignedEnergy (slopeDeterminantMeasure ρ) ≤
        slopeSecondMoment ρ - slopeFourthMoment ρ := by
  have hpoint (ξ : ℝ) := matrixFourthTrace_bounds (slopeFourierMatrix ρ ξ)
    ((slopeMassMatrix ρ).map Complex.ofReal)
    (admissible_fourier_contraction ρ hρ ξ) (admissible_mass_contraction ρ hρ)
    (admissible_fourier_domination ρ ξ)
  simp only [matrixDeterminantEnergy_ofReal] at hpoint
  constructor
  · have h := integral_mono (integrable_slopeFourthTrace ρ hρ)
      ((integrable_const (1 : ℝ)).add
        (((integrable_slopeSecondTrace ρ).sub (integrable_const (1 : ℝ))).const_mul
          ((slopeMassMatrix ρ).det ^ 2))) (fun ξ => (hpoint ξ).1)
    dsimp only [Pi.add_apply, Pi.sub_apply] at h
    erw [integral_add (integrable_const (1 : ℝ))
        (((integrable_slopeSecondTrace ρ).sub (integrable_const (1 : ℝ))).const_mul
          ((slopeMassMatrix ρ).det ^ 2)), integral_const_mul,
      integral_sub (integrable_slopeSecondTrace ρ) (integrable_const (1 : ℝ)),
      integral_const, probReal_univ, one_smul] at h
    simpa only [slopeFourthMoment, slopeSecondMoment] using h
  · have h := integral_mono
      ((integrable_slopeDeterminantEnergy ρ hρ).const_mul (1 - (slopeMassMatrix ρ).det ^ 2))
      ((integrable_slopeSecondTrace ρ).sub (integrable_slopeFourthTrace ρ hρ))
      (fun ξ => (hpoint ξ).2)
    dsimp only [Pi.sub_apply] at h
    erw [integral_const_mul,
      ← determinant_measure_energy,
      integral_sub (integrable_slopeSecondTrace ρ) (integrable_slopeFourthTrace ρ hρ)] at h
    simpa only [slopeFourthMoment, slopeSecondMoment] using h

/-- A uniform gap for the genuine determinant mass when the second moment is small. -/
theorem admissible_determinant_gap
    (ρ : Matrix (Fin 2) (Fin 2) (Measure ℝ)) [∀ i j, IsFiniteMeasure (ρ i j)]
    (hρ : IsAdmissibleSlopeMatrix ρ) (hsmall : slopeSecondMoment ρ ≤ 3 / 2) :
    (slopeMassMatrix ρ).det ^ 2 ≤ 31 / 32 := by
  apply nonnegative_mass_matrix_determinant_gap (slopeMassMatrix ρ)
    (fun i j => ‖cornerMean (ρ i j)‖ ^ 2)
  · exact fun i j => measureReal_nonneg
  · exact fun i j => slope_mass_le_one (ρ i j)
      (admissible_entry_negative_moment hρ i j) (admissible_entry_positive_moment hρ i j)
  · exact fun i j => sq_nonneg _
  · exact fun i j => slope_entry_mass_fourth_le_energy (ρ i j)
      (admissible_entry_negative_moment hρ i j) (admissible_entry_positive_moment hρ i j)
  · rwa [← slopeSecondMoment_eq_entry_energies]

/-- Elementary monotonicity of the logarithmic energy scale, proved from log's
supporting-line inequality rather than a differentiability assumption. -/
theorem mul_log_exp_div_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ 1) :
    x * Real.log (Real.exp 1 / x) ≤ y * Real.log (Real.exp 1 / y) := by
  have hy0 : 0 < y := hx.trans_le hxy
  have hlog : Real.log (Real.exp 1 / x) =
      Real.log (Real.exp 1 / y) + Real.log (y / x) := by
    rw [Real.log_div (Real.exp_ne_zero _) hx.ne', Real.log_div (Real.exp_ne_zero _) hy0.ne',
      Real.log_div hy0.ne' hx.ne']
    ring
  have hLy : 1 ≤ Real.log (Real.exp 1 / y) := by
    rw [Real.log_div (Real.exp_ne_zero _) hy0.ne', Real.log_exp]
    linarith [Real.log_nonpos hy0.le hy]
  have hsec := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hy0 hx)) hx.le
  have hsec' : x * Real.log (y / x) ≤ y - x := by
    convert hsec using 1
    field_simp [hx.ne']
  rw [hlog, mul_add]
  nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hLy)]

theorem log_inverse_ge_one {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ Real.exp (-1)) :
    1 ≤ Real.log (1 / ε) := by
  have hlog := Real.log_le_log hε hsmall
  rw [Real.log_exp] at hlog
  rw [Real.log_div one_ne_zero hε.ne', Real.log_one]
  linarith

theorem logarithmic_energy_scale_bound {E ε : ℝ} (hE : 0 < E) (hε : 0 < ε)
    (hEε : E ≤ 32 * ε) (hsmall : ε ≤ 1 / 64) (hlog : 1 ≤ Real.log (1 / ε)) :
    E * Real.log (Real.exp 1 / E) ≤ 64 * ε * Real.log (1 / ε) := by
  have h32 : 0 < 32 * ε := by positivity
  have hmono := mul_log_exp_div_mono hE hEε (by linarith : 32 * ε ≤ 1)
  have hlog32 : Real.log (Real.exp 1 / (32 * ε)) ≤ 1 + Real.log (1 / ε) := by
    have harg : Real.exp 1 / (32 * ε) ≤ Real.exp 1 / ε := by
      apply div_le_div_of_nonneg_left (Real.exp_pos _).le hε
      linarith
    have h := Real.log_le_log (div_pos (Real.exp_pos _) h32) harg
    rw [Real.log_div (Real.exp_ne_zero _) hε.ne', Real.log_exp] at h
    rw [Real.log_div one_ne_zero hε.ne', Real.log_one]
    linarith
  have hmul := mul_le_mul_of_nonneg_left hlog32 h32.le
  nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hlog)]

/-- Lemma 5.2 with explicit universal constants and a concrete sufficiently-small
range. This retains every admissible finite slope measure, not just polygons or
atomic measures. -/
theorem lemma_5_2_fourth_moment
    (ρ : Matrix (Fin 2) (Fin 2) (Measure ℝ)) [∀ i j, IsFiniteMeasure (ρ i j)]
    (hρ : IsAdmissibleSlopeMatrix ρ) {ε : ℝ} (hε : 0 < ε)
    (hsmall : ε ≤ min (1 / 64) (Real.exp (-1)))
    (hsecond : slopeSecondMoment ρ = 1 + ε) :
    slopeFourthMoment ρ ≤ 1 + 2176 * ε ^ 2 * Real.log (1 / ε) := by
  have hε64 : ε ≤ 1 / 64 := hsmall.trans (min_le_left _ _)
  have hεexp : ε ≤ Real.exp (-1) := hsmall.trans (min_le_right _ _)
  have hlog : 1 ≤ Real.log (1 / ε) := log_inverse_ge_one hε hεexp
  have hL0 : 0 ≤ Real.log (1 / ε) := zero_le_one.trans hlog
  by_cases hfourth : slopeFourthMoment ρ ≤ 1
  · exact hfourth.trans (le_add_of_nonneg_right (by positivity))
  have hfourth' : 1 < slopeFourthMoment ρ := lt_of_not_ge hfourth
  let E := cornerSignedEnergy (slopeDeterminantMeasure ρ)
  let β := (slopeMassMatrix ρ).det ^ 2
  have hβ0 : 0 ≤ β := sq_nonneg _
  have hβgap : β ≤ 31 / 32 := admissible_determinant_gap ρ hρ (by rw [hsecond]; linarith)
  obtain ⟨hupper, hlower⟩ := slopeFourthMoment_determinant_bounds ρ hρ
  change slopeFourthMoment ρ ≤ 1 + β * (slopeSecondMoment ρ - 1) at hupper
  change (1 - β) * E ≤ slopeSecondMoment ρ - slopeFourthMoment ρ at hlower
  rw [hsecond] at hupper hlower
  have hE0 : 0 ≤ E := cornerSignedEnergy_nonneg _
  have hEε : E ≤ 32 * ε := by
    have hgapE := mul_le_mul_of_nonneg_right hβgap hE0
    nlinarith
  have hmoment := slopeDeterminantMeasure_exponential_moment ρ hρ
  have hmass := lemma_5_1_logarithmic_mass (slopeDeterminantMeasure ρ) hmoment
  have hEpos : 0 < E := by
    by_contra hn
    have hzero : E = 0 := le_antisymm (le_of_not_gt hn) hE0
    have hmzero := hmass.1 hzero
    rw [slopeDeterminantMeasure_mass] at hmzero
    have hβzero : β = 0 := by dsimp [β]; rw [hmzero]; norm_num
    rw [hβzero] at hupper
    linarith
  have hmassBound := hmass.2 hEpos (by change E ≤ 1 / 2; linarith)
  rw [slopeDeterminantMeasure_mass, sq_abs] at hmassBound
  change β ≤ 34 * E * Real.log (Real.exp 1 / E) at hmassBound
  have hscale := logarithmic_energy_scale_bound hEpos hε hEε hε64 hlog
  have hβ : β ≤ 2176 * ε * Real.log (1 / ε) := by nlinarith
  have hfinal := mul_le_mul_of_nonneg_right hβ hε.le
  nlinarith

end VolumePolynomials
