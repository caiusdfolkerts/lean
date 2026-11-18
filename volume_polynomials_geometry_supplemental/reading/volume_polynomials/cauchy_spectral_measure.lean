/-
The two Fourier-pair proofs below are adapted from
TauCeti/Probability/Distributions/Cauchy/Basic.lean, commit
06d5bb4e3ebb737dc6538567f5c53bf8800b9362, lines 381–417.
Copyright (c) 2026 The Tau Ceti contributors and Kitware, Inc.
Released under the Apache 2.0 license; see audit/TauCeti-LICENSE.
-/
module

public import VolumePolynomials.ExponentialFourier
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Probability.Distributions.Cauchy
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

/-!
# The actual probability measure in the corner Fourier representation

The spectral measure is Mathlib's Cauchy probability measure with location zero
and scale one half. The density and characteristic function are proved, including
all normalizing constants. Fourier inversion is a theorem of the pinned Mathlib.
-/

open MeasureTheory ProbabilityTheory Set
open scoped FourierTransform Real ENNReal NNReal

namespace VolumePolynomials

theorem fourier_exponential_eq_cauchy_density {γ : ℝ≥0} (hγ : γ ≠ 0) (ξ : ℝ) :
    𝓕 (fun x : ℝ => (Real.exp (-(2 * Real.pi * γ * |x|)) : ℂ)) ξ =
      (cauchyPDFReal 0 γ ξ : ℂ) := by
  have hγ' : (0 : ℝ) < (γ : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hγ)
  have ha : (0 : ℝ) < 2 * Real.pi * γ := mul_pos (by positivity) hγ'
  rw [fourier_exp_neg_mul_abs ha, Complex.ofReal_inj, cauchyPDFReal_def]
  field_simp
  ring

theorem integral_character_cauchy_density {γ : ℝ≥0} (hγ : γ ≠ 0) (t : ℝ) :
    (∫ x : ℝ, Complex.exp ((t : ℂ) * x * Complex.I) * (cauchyPDFReal 0 γ x : ℂ)) =
      (Real.exp (-((γ : ℝ) * |t|)) : ℂ) := by
  have hγ' : (0 : ℝ) < (γ : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hγ)
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have ha : (0 : ℝ) < 2 * Real.pi * γ := mul_pos hπ hγ'
  have hcont : Continuous (fun x : ℝ => (Real.exp (-(2 * Real.pi * γ * |x|)) : ℂ)) := by
    fun_prop
  have hint : Integrable (fun x : ℝ => (Real.exp (-(2 * Real.pi * γ * |x|)) : ℂ)) :=
    (integrable_exp_neg_mul_abs ha).ofReal
  have hFf : 𝓕 (fun x : ℝ => (Real.exp (-(2 * Real.pi * γ * |x|)) : ℂ)) =
      fun ξ : ℝ => (cauchyPDFReal 0 γ ξ : ℂ) :=
    funext (fourier_exponential_eq_cauchy_density hγ)
  have hintF : Integrable (𝓕 (fun x : ℝ => (Real.exp (-(2 * Real.pi * γ * |x|)) : ℂ))) := by
    rw [hFf]
    exact (integrable_cauchyPDFReal 0).ofReal
  have hinv := congrFun (hcont.fourierInv_fourier_eq hint hintF) (t / (2 * Real.pi))
  rw [hFf, Real.fourierInv_eq'] at hinv
  have habs : 2 * Real.pi * (γ : ℝ) * |t / (2 * Real.pi)| = (γ : ℝ) * |t| := by
    rw [abs_div, abs_of_pos hπ]
    field_simp
  rw [← habs, ← hinv]
  refine integral_congr_ae (.of_forall fun v => ?_)
  dsimp only
  rw [smul_eq_mul]
  congr 2
  push_cast [RCLike.inner_apply, starRingEnd_apply, star_trivial]
  field_simp

/-- The spectral probability measure appearing in equations (4.1) and (4.7). -/
noncomputable def cornerSpectralMeasure : Measure ℝ := cauchyMeasure 0 (1 / 2)

instance : IsProbabilityMeasure cornerSpectralMeasure := by
  unfold cornerSpectralMeasure
  infer_instance

theorem cornerSpectralMeasure_density :
    cornerSpectralMeasure = volume.withDensity
      (fun ξ : ℝ => ENNReal.ofReal (1 / (2 * Real.pi * (ξ ^ 2 + 1 / 4)))) := by
  rw [cornerSpectralMeasure, cauchyMeasure_of_scale_ne_zero 0 (by norm_num)]
  congr 1
  funext ξ
  unfold cauchyPDF cauchyPDFReal
  congr 1
  norm_num
  field_simp [Real.pi_ne_zero, ne_of_gt (by positivity : 0 < ξ ^ 2 + (1 / 4 : ℝ))]

theorem integral_cornerSpectralMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) :
    (∫ x, f x ∂cornerSpectralMeasure) = ∫ x, cauchyPDFReal 0 (1 / 2) x • f x := by
  rw [cornerSpectralMeasure, cauchyMeasure_of_scale_ne_zero 0 (by norm_num),
    integral_withDensity_eq_integral_toReal_smul (measurable_cauchyPDF 0 (1 / 2))
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top) f]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  dsimp only
  rw [cauchyPDF_def, ENNReal.toReal_ofReal (cauchyPDF_pos 0 (by norm_num) x).le]

theorem charFun_cornerSpectralMeasure (t : ℝ) :
    charFun cornerSpectralMeasure t = (Real.exp (-|t| / 2) : ℂ) := by
  rw [charFun_apply_real, integral_cornerSpectralMeasure]
  simpa [Complex.real_smul, mul_comm, div_eq_mul_inv] using
    integral_character_cauchy_density (γ := (1 / 2 : ℝ≥0)) (by norm_num) t

end VolumePolynomials
