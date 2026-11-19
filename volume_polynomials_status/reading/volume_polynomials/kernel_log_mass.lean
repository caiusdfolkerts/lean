module

public import VolumePolynomials.SignedKernelEnergy
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

/-!
# The logarithmic mass estimate for finite signed measures

This is Lemma5.1 with the explicit absolute constant34. Its energy is the actual
double integral of `exp (-|x-y|/2)` against the signed measure, not an assumed
quadratic form. The proof uses the constructed Hilbert features and the exactly
integrated test measure.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace VolumePolynomials

theorem signed_mass_zero_of_energy_zero (ν : SignedMeasure ℝ)
    (hInt : Integrable (fun x : ℝ => Real.exp (|x| / 2)) ν.totalVariation)
    (hMoment : (∫ x : ℝ, Real.exp (|x| / 2) ∂ν.totalVariation) ≤ 4)
    (hEnergy : cornerSignedEnergy ν = 0) : ν univ = 0 := by
  have hnorm : ‖cornerSignedMean ν‖ = 0 := by
    rw [cornerSignedEnergy_eq_norm_sq] at hEnergy
    nlinarith [norm_nonneg (cornerSignedMean ν)]
  have hbound : ∀ᶠ R : ℝ in atTop, |ν univ| ≤ 4 * Real.exp (-R / 2) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    simpa only [hnorm, zero_mul, zero_add] using signed_mass_test_bound hR ν hInt hMoment
  have hlim : Tendsto (fun R : ℝ => 4 * Real.exp (-R / 2)) atTop (𝓝 0) := by
    have hdiv : Tendsto (fun R : ℝ => R / 2) atTop atTop :=
      Tendsto.atTop_div_const (by norm_num : (0 : ℝ) < 2) tendsto_id
    simpa only [Function.comp_def, neg_div, mul_zero] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp hdiv).const_mul 4
  exact abs_eq_zero.mp (le_antisymm (ge_of_tendsto hlim hbound) (abs_nonneg _))

/-- Lemma5.1, with no restriction to discrete measures and an explicit constant. -/
theorem signed_mass_sq_le_log_energy (ν : SignedMeasure ℝ)
    (hInt : Integrable (fun x : ℝ => Real.exp (|x| / 2)) ν.totalVariation)
    (hMoment : (∫ x : ℝ, Real.exp (|x| / 2) ∂ν.totalVariation) ≤ 4)
    (hEnergyPos : 0 < cornerSignedEnergy ν)
    (hEnergySmall : cornerSignedEnergy ν ≤ 1 / 2) :
    |ν univ| ^ 2 ≤ 34 * cornerSignedEnergy ν *
      Real.log (Real.exp 1 / cornerSignedEnergy ν) := by
  let E := cornerSignedEnergy ν
  let R := -Real.log E
  have hE : 0 < E := hEnergyPos
  have hEone : E ≤ 1 := by dsimp [E]; linarith
  have hR : 0 ≤ R := neg_nonneg.mpr (Real.log_nonpos hE.le hEone)
  let n := ‖cornerSignedMean ν‖
  let t := ‖cornerMean (cornerTestMeasure R)‖
  let q := Real.exp (-R / 2)
  have hn : 0 ≤ n := norm_nonneg _
  have ht : 0 ≤ t := norm_nonneg _
  have hq : 0 ≤ q := (Real.exp_pos _).le
  have hn2 : n ^ 2 = E := (cornerSignedEnergy_eq_norm_sq ν).symm
  have ht2 : t ^ 2 = 1 + R / 2 := norm_cornerMean_test_sq hR
  have hq2 : q ^ 2 = E := by
    dsimp [q]
    rw [pow_two, ← Real.exp_add]
    have he : -R / 2 + -R / 2 = Real.log E := by dsimp [R]; ring
    rw [he, Real.exp_log hE]
  have hnt2 : (n * t) ^ 2 = E * (1 + R / 2) := by
    rw [mul_pow, hn2, ht2]
  have hbound : |ν univ| ≤ n * t + 4 * q := signed_mass_test_bound hR ν hInt hMoment
  have hBnonneg : 0 ≤ n * t + 4 * q :=
    add_nonneg (mul_nonneg hn ht) (mul_nonneg (by norm_num) hq)
  have hsquare : |ν univ| ^ 2 ≤ (n * t + 4 * q) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg _) hBnonneg).mpr hbound
  have hupper : (n * t + 4 * q) ^ 2 ≤ E * (R + 34) := by
    have htwo : (n * t + 4 * q) ^ 2 ≤ 2 * (n * t) ^ 2 + 32 * q ^ 2 := by
      nlinarith [sq_nonneg (n * t - 4 * q)]
    rw [hnt2, hq2] at htwo
    nlinarith
  have hlog : Real.log (Real.exp 1 / E) = 1 + R := by
    rw [Real.log_div (Real.exp_ne_zero _) hE.ne', Real.log_exp]
    dsimp [R]
    ring
  change |ν univ| ^ 2 ≤ 34 * E * Real.log (Real.exp 1 / E)
  rw [hlog]
  nlinarith [mul_nonneg hE.le hR]

/-- The exponential-moment assumption stated as a nonnegative Lebesgue integral
automatically supplies the integrability needed in the preceding proofs. -/
theorem exponentialMoment_integrable_and_le (ν : SignedMeasure ℝ)
    (hMoment : (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (|x| / 2)) ∂ν.totalVariation) ≤ 4) :
    Integrable (fun x : ℝ => Real.exp (|x| / 2)) ν.totalVariation ∧
      (∫ x : ℝ, Real.exp (|x| / 2) ∂ν.totalVariation) ≤ 4 := by
  have hnonneg : ∀ᵐ x : ℝ ∂ν.totalVariation, 0 ≤ Real.exp (|x| / 2) :=
    Filter.Eventually.of_forall fun x => (Real.exp_pos _).le
  have hmeas : AEStronglyMeasurable (fun x : ℝ => Real.exp (|x| / 2)) ν.totalVariation := by
    fun_prop
  refine ⟨⟨hmeas, (hasFiniteIntegral_iff_ofReal hnonneg).mpr ?_⟩, ?_⟩
  · exact hMoment.trans_lt (by norm_num)
  · rw [integral_eq_lintegral_of_nonneg_ae hnonneg hmeas]
    simpa using ENNReal.toReal_mono (by norm_num : (4 : ℝ≥0∞) ≠ ∞) hMoment

/-- The paper's full Lemma5.1 for arbitrary finite real signed measures, in the
exact moment formulation and with the universal constant34. -/
theorem lemma_5_1_logarithmic_mass (ν : SignedMeasure ℝ)
    (hMoment : (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (|x| / 2)) ∂ν.totalVariation) ≤ 4) :
    (cornerSignedEnergy ν = 0 → ν univ = 0) ∧
      (0 < cornerSignedEnergy ν → cornerSignedEnergy ν ≤ 1 / 2 →
        |ν univ| ^ 2 ≤ 34 * cornerSignedEnergy ν *
          Real.log (Real.exp 1 / cornerSignedEnergy ν)) := by
  obtain ⟨hInt, hReal⟩ := exponentialMoment_integrable_and_le ν hMoment
  exact ⟨signed_mass_zero_of_energy_zero ν hInt hReal,
    signed_mass_sq_le_log_energy ν hInt hReal⟩

end VolumePolynomials
