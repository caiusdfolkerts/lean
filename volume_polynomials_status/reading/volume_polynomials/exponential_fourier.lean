/-
Adapted from the three exact TauCeti sources recorded in
`audit/tauceti-exponential-fourier-provenance.json`, commit
06d5bb4e3ebb737dc6538567f5c53bf8800b9362.
Copyright (c) 2026 The Tau Ceti contributors.
Released under Apache 2.0; see audit/TauCeti-LICENSE.
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# The complete two-sided exponential Fourier pair

Only the four supporting theorems needed for the actual Cauchy spectral measure
are included. Their proofs are adapted without mathematical changes from the
recorded upstream sources. Compilation status is recorded separately in the audit.
-/

open MeasureTheory Set
open scoped FourierTransform Real

namespace VolumePolynomials

theorem integrable_comp_abs {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    (hf : IntegrableOn f (Set.Ioi 0)) : Integrable fun x : ℝ => f |x| := by
  have hIoi : IntegrableOn (fun x : ℝ => f |x|) (Set.Ioi 0) :=
    hf.congr_fun (fun x hx => by rw [abs_of_pos hx]) measurableSet_Ioi
  have hIic : IntegrableOn (fun x : ℝ => f |x|) (Set.Iic 0) := by
    have hIoi' : IntegrableOn (fun x : ℝ => f |x|) (Set.Ioi (-(0 : ℝ))) := by
      simpa only [neg_zero] using hIoi
    have hIio : IntegrableOn (fun x : ℝ => f |-x|) (Set.Iio 0) :=
      hIoi'.comp_neg_Iio (μ := volume) (c := 0)
    rw [integrableOn_Iic_iff_integrableOn_Iio]
    simpa only [abs_neg] using hIio
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ))]
  exact hIic.union hIoi

theorem integrable_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℝ ↦ Real.exp (-(a * |x|))) := by
  simpa only [neg_mul] using integrable_comp_abs
    (integrableOn_exp_mul_Ioi (a := -a) (by linarith) 0)

variable {a : ℝ}

/-- **The Lorentzian pairing of the two-sided exponential with a complex oscillation.** -/
theorem integral_exp_mul_I_mul_exp_neg_mul_abs (ha : 0 < a) (b : ℝ) :
    (∫ x : ℝ, Complex.exp ((b : ℂ) * x * Complex.I) * (Real.exp (-(a * |x|)) : ℂ))
      = ((2 * a / (a ^ 2 + b ^ 2) : ℝ) : ℂ) := by
  -- Rewrite the integrand as a single complex exponential on each half-line.
  have hre₁ : ((a : ℂ) + b * Complex.I).re = a := by simp
  have hre₂ : (-(a : ℂ) + b * Complex.I).re = -a := by simp
  have key : ∀ c x : ℝ, Complex.exp ((b : ℂ) * x * Complex.I) * (Real.exp (c * x) : ℂ)
      = Complex.exp (((c : ℂ) + b * Complex.I) * x) := by
    intro c x
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hm : EqOn (fun x : ℝ ↦ Complex.exp ((b : ℂ) * x * Complex.I) * (Real.exp (-(a * |x|)) : ℂ))
      (fun x : ℝ ↦ Complex.exp (((a : ℂ) + b * Complex.I) * x)) (Iic 0) := by
    intro x hx
    have hxa : -(a * |x|) = a * x := by rw [abs_of_nonpos (mem_Iic.mp hx)]; ring
    simpa only [hxa] using key a x
  have hp : EqOn (fun x : ℝ ↦ Complex.exp ((b : ℂ) * x * Complex.I) * (Real.exp (-(a * |x|)) : ℂ))
      (fun x : ℝ ↦ Complex.exp ((-(a : ℂ) + b * Complex.I) * x)) (Ioi 0) := by
    intro x hx
    have hxa : -(a * |x|) = -a * x := by rw [abs_of_pos (mem_Ioi.mp hx)]; ring
    simpa only [hxa, Complex.ofReal_neg] using key (-a) x
  -- Integrability comes from the real two-sided exponential, since the oscillation has norm one.
  have hint : Integrable
      (fun x : ℝ ↦ Complex.exp ((b : ℂ) * x * Complex.I) * (Real.exp (-(a * |x|)) : ℂ))
      := ((integrable_exp_neg_mul_abs ha).ofReal).bdd_mul (c := 1) (by fun_prop)
        (.of_forall fun x ↦ by simp [Complex.norm_exp])
  have hne₁ : (a : ℂ) + b * Complex.I ≠ 0 := by
    intro h
    rw [h] at hre₁
    exact ha.ne' (by simpa using hre₁.symm)
  have hne₂ : -(a : ℂ) + b * Complex.I ≠ 0 := by
    intro h
    rw [h] at hre₂
    simp only [Complex.zero_re] at hre₂
    exact ha.ne' (by linarith)
  have hsq : (0 : ℝ) < a ^ 2 + b ^ 2 := by positivity
  -- Evaluate the two half-line integrals and combine the resulting rational functions.
  rw [← intervalIntegral.integral_Iic_add_Ioi hint.integrableOn hint.integrableOn,
    setIntegral_congr_fun measurableSet_Iic hm, setIntegral_congr_fun measurableSet_Ioi hp,
    integral_exp_mul_complex_Iic (by rw [hre₁]; exact ha),
    integral_exp_mul_complex_Ioi (by rw [hre₂]; linarith)]
  have hprod : ((a : ℂ) + b * Complex.I) * (-(a : ℂ) + b * Complex.I)
      = -((a : ℂ) ^ 2 + (b : ℂ) ^ 2) := by
    linear_combination ((b : ℂ) ^ 2) * Complex.I_sq
  have hdenom : ((a : ℂ) ^ 2 + (b : ℂ) ^ 2) ≠ 0 := by
    have : ((a ^ 2 + b ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsq.ne'
    push_cast at this
    exact this
  rw [Complex.ofReal_div]
  push_cast
  simp only [mul_zero, Complex.exp_zero]
  field_simp
  linear_combination (-2 * (a : ℂ)) * hprod

/-- **The Fourier transform of the two-sided exponential.** With Mathlib's normalisation
`𝓕 f ξ = ∫ x, exp (-2 π i x ξ) f x`, the transform of `x ↦ exp (-(a * |x|))` is the Lorentzian
`2 * a / (a ^ 2 + (2 * π * ξ) ^ 2)`. -/
theorem fourier_exp_neg_mul_abs (ha : 0 < a) (ξ : ℝ) :
    𝓕 (fun x : ℝ ↦ (Real.exp (-(a * |x|)) : ℂ)) ξ
      = ((2 * a / (a ^ 2 + (2 * π * ξ) ^ 2) : ℝ) : ℂ) := by
  rw [Real.fourier_eq']
  -- Unfold the real inner product and scalar action to match the oscillatory-integral lemma.
  calc
    _ = ∫ x : ℝ, Complex.exp (((-(2 * π * ξ) : ℝ) : ℂ) * x * Complex.I) *
        (Real.exp (-(a * |x|)) : ℂ) := integral_congr_ae (.of_forall fun x ↦ by
      change Complex.exp ((↑(-2 * π * (inner ℝ x ξ : ℝ)) * Complex.I)) •
        (Real.exp (-(a * |x|)) : ℂ) = _
      rw [smul_eq_mul]
      congr 2
      push_cast [RCLike.inner_apply, starRingEnd_apply, star_trivial]
      ring)
    _ = _ := by
      rw [integral_exp_mul_I_mul_exp_neg_mul_abs ha]
      norm_num

end VolumePolynomials
