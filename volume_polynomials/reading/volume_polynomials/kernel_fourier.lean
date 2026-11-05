module

public import VolumePolynomials.SignedKernelEnergy
public import VolumePolynomials.CauchySpectralMeasure
public import VolumePolynomials.SlopeMeasureMoments

@[expose] public section

/-!
# The Fourier representation of the actual signed corner energy

This file connects the iterated signed-measure energy to the Cauchy spectral
integral. Fubini is applied to bounded characters on products of finite measures.
The determinant transform is then the actual signed convolution difference.
-/

open MeasureTheory Set Matrix
open scoped ENNReal InnerProductSpace RealInnerProductSpace ComplexConjugate MeasureTheory

namespace VolumePolynomials

theorem integrable_character (μ : Measure ℝ) [IsFiniteMeasure μ] (ξ : ℝ) :
    Integrable (fun x : ℝ => Complex.exp ((ξ : ℂ) * x * Complex.I)) μ := by
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  exact Filter.Eventually.of_forall fun x => by simp [Complex.norm_exp]

theorem character_product (ξ x y : ℝ) :
    conj (Complex.exp ((ξ : ℂ) * x * Complex.I)) *
      Complex.exp ((ξ : ℂ) * y * Complex.I) =
        Complex.exp (((y - x : ℝ) : ℂ) * ξ * Complex.I) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_sub]
  ring

/-- The exact complex bilinear Fourier/kernel identity for two finite positive measures. -/
theorem corner_spectral_pairing (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (∫ ξ : ℝ, conj (charFun μ ξ) * charFun ν ξ ∂cornerSpectralMeasure) =
      Complex.ofReal (∫ x : ℝ, ∫ y : ℝ, cornerKernel x y ∂ν ∂μ) := by
  have hproduct (ξ : ℝ) : conj (charFun μ ξ) * charFun ν ξ =
      ∫ p : ℝ × ℝ, Complex.exp (((p.2 - p.1 : ℝ) : ℂ) * ξ * Complex.I) ∂μ.prod ν := by
    rw [charFun_apply_real, charFun_apply_real, ← integral_conj, ← integral_prod_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun p => character_product ξ p.1 p.2
  have hint : Integrable (fun p : ℝ × (ℝ × ℝ) =>
      Complex.exp (((p.2.2 - p.2.1 : ℝ) : ℂ) * p.1 * Complex.I))
        (cornerSpectralMeasure.prod (μ.prod ν)) := by
    apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
    exact Filter.Eventually.of_forall fun p => by simp [Complex.norm_exp]
  simp_rw [hproduct]
  rw [integral_integral_swap hint]
  have hinner (p : ℝ × ℝ) :
      (∫ ξ : ℝ, Complex.exp (((p.2 - p.1 : ℝ) : ℂ) * ξ * Complex.I)
        ∂cornerSpectralMeasure) = (cornerKernel p.1 p.2 : ℂ) := by
    simpa only [charFun_apply_real, cornerKernel, abs_sub_comm] using
      charFun_cornerSpectralMeasure (p.2 - p.1)
  simp_rw [hinner]
  have hK : Integrable (fun p : ℝ × ℝ => cornerKernel p.1 p.2) (μ.prod ν) := by
    apply (integrable_const (1 : ℝ)).mono' (by unfold cornerKernel; fun_prop)
    exact Filter.Eventually.of_forall fun p => by
      simpa only [Real.norm_eq_abs, abs_of_pos (cornerKernel_pos _ _)] using
        cornerKernel_le_one p.1 p.2
  simpa only [integral_complex_ofReal] using
    congrArg Complex.ofReal (integral_prod (fun p : ℝ × ℝ => cornerKernel p.1 p.2) hK)

theorem integrable_spectral_pairing (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Integrable (fun ξ : ℝ => conj (charFun μ ξ) * charFun ν ξ) cornerSpectralMeasure := by
  apply (integrable_const (μ.real univ * ν.real univ)).mono' (by fun_prop)
  apply Filter.Eventually.of_forall
  intro ξ
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_mul (norm_charFun_le ξ) (norm_charFun_le ξ) (norm_nonneg _)
    measureReal_nonneg

theorem integrable_real_spectral_pairing (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Integrable (fun ξ : ℝ => (conj (charFun μ ξ) * charFun ν ξ).re)
      cornerSpectralMeasure := by
  exact Complex.reCLM.integrable_comp (integrable_spectral_pairing μ ν)

theorem real_corner_spectral_pairing (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (∫ ξ : ℝ, (conj (charFun μ ξ) * charFun ν ξ).re ∂cornerSpectralMeasure) =
      ∫ x : ℝ, ∫ y : ℝ, cornerKernel x y ∂ν ∂μ := by
  have h := Complex.reCLM.integral_comp_comm (integrable_spectral_pairing μ ν)
  change (∫ ξ : ℝ, (conj (charFun μ ξ) * charFun ν ξ).re ∂cornerSpectralMeasure) =
    (∫ ξ : ℝ, conj (charFun μ ξ) * charFun ν ξ ∂cornerSpectralMeasure).re at h
  rw [h, corner_spectral_pairing]
  rfl

theorem integrable_spectral_normSq (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (fun ξ : ℝ => Complex.normSq (charFun μ ξ)) cornerSpectralMeasure := by
  have h := integrable_real_spectral_pairing μ μ
  simpa only [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re] using h

theorem corner_spectral_energy (μ : Measure ℝ) [IsFiniteMeasure μ] :
    (∫ ξ : ℝ, Complex.normSq (charFun μ ξ) ∂cornerSpectralMeasure) =
      ‖cornerMean μ‖ ^ 2 := by
  rw [norm_cornerMean_sq]
  simpa only [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re] using
    real_corner_spectral_pairing μ μ

theorem inner_cornerMean_mean (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ⟪cornerMean μ, cornerMean ν⟫_ℝ = ∫ x : ℝ, ∫ y : ℝ, cornerKernel x y ∂ν ∂μ := by
  rw [real_inner_comm]
  change ⟪cornerMean ν, ∫ x : ℝ, cornerFeature x ∂μ⟫_ℝ = _
  rw [← integral_inner (integrable_cornerFeature μ)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [real_inner_comm, inner_cornerFeature_mean]

theorem complex_normSq_sub_eq (z w : ℂ) :
    Complex.normSq (z - w) = Complex.normSq z - 2 * (conj z * w).re + Complex.normSq w := by
  rw [Complex.normSq_sub]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- The energy of a difference uses the actual two positive measures, with no
assumption that they are mutually singular. -/
theorem corner_spectral_difference_energy (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (∫ ξ : ℝ, Complex.normSq (charFun μ ξ - charFun ν ξ) ∂cornerSpectralMeasure) =
      ‖cornerMean μ - cornerMean ν‖ ^ 2 := by
  simp_rw [complex_normSq_sub_eq]
  erw [integral_add ((integrable_spectral_normSq μ).sub
      ((integrable_real_spectral_pairing μ ν).const_mul 2)) (integrable_spectral_normSq ν),
    integral_sub (integrable_spectral_normSq μ)
      ((integrable_real_spectral_pairing μ ν).const_mul 2), integral_const_mul,
    corner_spectral_energy, corner_spectral_energy, real_corner_spectral_pairing,
    norm_sub_sq_real, inner_cornerMean_mean]

/-- Characteristic transform of an actual finite real signed measure. -/
noncomputable def signedSlopeFourier (ν : SignedMeasure ℝ) (ξ : ℝ) : ℂ :=
  ∫ᵛ x : ℝ, Complex.exp ((ξ : ℂ) * x * Complex.I) ∂<•ν

theorem signedSlopeFourier_sub (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (ξ : ℝ) :
    signedSlopeFourier (μ.toSignedMeasure - ν.toSignedMeasure) ξ =
      charFun μ ξ - charFun ν ξ := by
  have hp : μ.toSignedMeasure.Integrable
      (fun x : ℝ => Complex.exp ((ξ : ℂ) * x * Complex.I)) := by
    simpa only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure] using
      integrable_character μ ξ
  have hn : ν.toSignedMeasure.Integrable
      (fun x : ℝ => Complex.exp ((ξ : ℂ) * x * Complex.I)) := by
    simpa only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure] using
      integrable_character ν ξ
  rw [signedSlopeFourier, VectorMeasure.integral_sub_vectorMeasure hp hn,
    VectorMeasure.integral_toSignedMeasure, VectorMeasure.integral_toSignedMeasure,
    charFun_apply_real, charFun_apply_real]

theorem signedSlopeFourier_jordan (ν : SignedMeasure ℝ) (ξ : ℝ) :
    signedSlopeFourier ν ξ = charFun ν.toJordanDecomposition.posPart ξ -
      charFun ν.toJordanDecomposition.negPart ξ := by
  conv_lhs => rw [← ν.toSignedMeasure_toJordanDecomposition]
  rw [JordanDecomposition.toSignedMeasure, signedSlopeFourier_sub]

/-- The exact Fourier representation (4.1) for every finite real signed measure. -/
theorem cornerSignedEnergy_eq_spectral (ν : SignedMeasure ℝ) :
    cornerSignedEnergy ν =
      ∫ ξ : ℝ, Complex.normSq (signedSlopeFourier ν ξ) ∂cornerSpectralMeasure := by
  simp_rw [signedSlopeFourier_jordan]
  rw [corner_spectral_difference_energy, cornerSignedEnergy_eq_norm_sq, cornerSignedMean]

/-- Convolution makes the determinant transform an identity, not an assumption. -/
theorem signedSlopeFourier_determinant
    (ρ : Matrix (Fin 2) (Fin 2) (Measure ℝ))
    [∀ i j, IsFiniteMeasure (ρ i j)] (ξ : ℝ) :
    signedSlopeFourier (slopeDeterminantMeasure ρ) ξ = (slopeFourierMatrix ρ ξ).det := by
  rw [slopeDeterminantMeasure, signedSlopeFourier_sub, charFun_conv, charFun_conv,
    Matrix.det_fin_two]
  rfl

theorem determinant_measure_energy
    (ρ : Matrix (Fin 2) (Fin 2) (Measure ℝ))
    [∀ i j, IsFiniteMeasure (ρ i j)] :
    cornerSignedEnergy (slopeDeterminantMeasure ρ) =
      ∫ ξ : ℝ, matrixDeterminantEnergy (slopeFourierMatrix ρ ξ) ∂cornerSpectralMeasure := by
  rw [cornerSignedEnergy_eq_spectral]
  simp only [signedSlopeFourier_determinant, matrixDeterminantEnergy]

end VolumePolynomials
