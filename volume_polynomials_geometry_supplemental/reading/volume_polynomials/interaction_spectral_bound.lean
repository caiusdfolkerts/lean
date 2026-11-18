module

public import VolumePolynomials.FourthMoment

@[expose] public section
set_option autoImplicit false

/-! # The mixed Fourier interaction bound

Positivity of the squared Hilbert--Schmidt distance between the two Gram
matrices gives an arithmetic-mean bound. This proves the analytic estimate
used in Corollary 5.3 without adding a spectral-decomposition hypothesis.
-/

open MeasureTheory Matrix
open scoped BigOperators

namespace VolumePolynomials

theorem gram_difference_trace_identity (F G : Matrix (Fin 2) (Fin 2) ℂ) :
    matrixSecondTrace (F * Fᴴ - G * Gᴴ) =
      matrixFourthTrace F + matrixFourthTrace G - 2 * matrixSecondTrace (Fᴴ * G) := by
  first
  | simp [matrixSecondTrace, matrixFourthTrace, Matrix.trace, Matrix.diag_apply,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      Complex.mul_re, Complex.mul_im]
    ring

theorem mixed_matrix_trace_le_mean (F G : Matrix (Fin 2) (Fin 2) ℂ) :
    matrixSecondTrace (Fᴴ * G) ≤ (matrixFourthTrace F + matrixFourthTrace G) / 2 := by
  first
  | have h := matrixSecondTrace_nonneg (F * Fᴴ - G * Gᴴ)
    rw [gram_difference_trace_identity] at h
    linarith

noncomputable def slopeInteractionMoment
    (ρ σ : Matrix (Fin 2) (Fin 2) (Measure ℝ)) : ℝ :=
  ∫ ξ : ℝ, matrixSecondTrace ((slopeFourierMatrix ρ ξ)ᴴ * slopeFourierMatrix σ ξ)
    ∂cornerSpectralMeasure

theorem integrable_slopeInteractionTrace
    (ρ σ : Matrix (Fin 2) (Fin 2) (Measure ℝ))
    [∀ i j, IsFiniteMeasure (ρ i j)] [∀ i j, IsFiniteMeasure (σ i j)]
    (hρ : IsAdmissibleSlopeMatrix ρ) (hσ : IsAdmissibleSlopeMatrix σ) :
    Integrable (fun ξ : ℝ =>
      matrixSecondTrace ((slopeFourierMatrix ρ ξ)ᴴ * slopeFourierMatrix σ ξ))
      cornerSpectralMeasure := by
  first
  | apply (((integrable_slopeFourthTrace ρ hρ).add
      (integrable_slopeFourthTrace σ hσ)).div_const 2).mono' ?_ ?_
    · simp only [matrixSecondTrace_eq_sum, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fin.sum_univ_two, slopeFourierMatrix, ← Complex.sq_norm]
      fun_prop
    · exact Filter.Eventually.of_forall fun ξ => by
        dsimp only [Pi.add_apply]
        rw [Real.norm_eq_abs, abs_of_nonneg (matrixSecondTrace_nonneg _)]
        exact mixed_matrix_trace_le_mean _ _

theorem slopeInteractionMoment_le_mean
    (ρ σ : Matrix (Fin 2) (Fin 2) (Measure ℝ))
    [∀ i j, IsFiniteMeasure (ρ i j)] [∀ i j, IsFiniteMeasure (σ i j)]
    (hρ : IsAdmissibleSlopeMatrix ρ) (hσ : IsAdmissibleSlopeMatrix σ) :
    slopeInteractionMoment ρ σ ≤ (slopeFourthMoment ρ + slopeFourthMoment σ) / 2 := by
  first
  | have h := integral_mono (integrable_slopeInteractionTrace ρ σ hρ hσ)
      (((integrable_slopeFourthTrace ρ hρ).add (integrable_slopeFourthTrace σ hσ)).div_const 2)
      (fun ξ => mixed_matrix_trace_le_mean (slopeFourierMatrix ρ ξ) (slopeFourierMatrix σ ξ))
    dsimp only [Pi.add_apply] at h
    erw [integral_div, integral_add (integrable_slopeFourthTrace ρ hρ)
      (integrable_slopeFourthTrace σ hσ)] at h
    exact h

/-- The exact analytic consequence needed for Corollary 5.3. The actual
polygon-to-matrix area identities remain separate geometric theorems. -/
theorem slopeInteractionMoment_logarithmic_bound
    (ρ σ : Matrix (Fin 2) (Fin 2) (Measure ℝ))
    [∀ i j, IsFiniteMeasure (ρ i j)] [∀ i j, IsFiniteMeasure (σ i j)]
    (hρ : IsAdmissibleSlopeMatrix ρ) (hσ : IsAdmissibleSlopeMatrix σ)
    {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ min (1 / 64) (Real.exp (-1)))
    (hsecondρ : slopeSecondMoment ρ = 1 + ε)
    (hsecondσ : slopeSecondMoment σ = 1 + ε) :
    slopeInteractionMoment ρ σ ≤ 1 + 2176 * ε ^ 2 * Real.log (1 / ε) := by
  first
  | have hρ4 := lemma_5_2_fourth_moment ρ hρ hε hsmall hsecondρ
    have hσ4 := lemma_5_2_fourth_moment σ hσ hε hsmall hsecondσ
    have h := slopeInteractionMoment_le_mean ρ σ hρ hσ
    linarith

end VolumePolynomials
