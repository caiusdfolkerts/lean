module

public import Projection.QuantileLimit
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Lipschitz tests of centered quantiles

The centered quantile difference converges in L¹ after division by the ray
parameter. Every fixed Lipschitz test consequently has zero first variation.
Normalizing a nonzero Fourier frequency reduces it to a unit height direction,
so unit-direction quantile control supplies every characteristic-function test.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory Filter
open scoped Topology NNReal RealInnerProductSpace

namespace RankThreeProjection.QuantileStability

/-- A Lipschitz scalar test preserves integrability on a finite measure
space. The constant value at zero is kept explicitly. -/
theorem integrable_lipschitz_test
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    {f : X → ℝ} (hf : Integrable f μ)
    (ψ : ℝ → ℝ) (L : ℝ≥0) (hψ : LipschitzWith L ψ) :
    Integrable (fun x => ψ (f x)) μ := by
  have hi : Integrable (fun x => (L : ℝ) * ‖f x‖ + ‖ψ 0‖) μ :=
    (hf.norm.const_mul (L : ℝ)).add (integrable_const _)
  apply hi.mono' (hψ.continuous.comp_aestronglyMeasurable hf.aestronglyMeasurable)
  filter_upwards with x
  have hb : ‖ψ (f x) - ψ 0‖ ≤ (L : ℝ) * ‖f x‖ := by
    simpa only [dist_eq_norm, sub_zero] using hψ.dist_le_mul (f x) 0
  calc
    ‖ψ (f x)‖ ≤ ‖ψ (f x) - ψ 0‖ + ‖ψ 0‖ := by
      simpa only [sub_add_cancel] using norm_add_le (ψ (f x) - ψ 0) (ψ 0)
    _ ≤ (L : ℝ) * ‖f x‖ + ‖ψ 0‖ := add_le_add hb le_rfl

theorem integral_lipschitz_difference_quotient_le_mul
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f g : X → ℝ) (ψ : ℝ → ℝ) (L : ℝ≥0) (t : ℝ)
    (hψ : LipschitzWith L ψ)
    (hfi : Integrable (fun x => ψ (f x)) μ)
    (hgi : Integrable (fun x => ψ (g x)) μ)
    (hdi : Integrable (fun x => (g x - f x) / t) μ) :
    |((∫ x, ψ (g x) ∂μ) - ∫ x, ψ (f x) ∂μ) / t| ≤
      (L : ℝ) * ∫ x, |(g x - f x) / t| ∂μ := by
  rw [← integral_sub hgi hfi, ← integral_div, ← integral_const_mul]
  calc
    _ ≤ ∫ x, |(ψ (g x) - ψ (f x)) / t| ∂μ := by
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (fun x => (ψ (g x) - ψ (f x)) / t)
    _ ≤ _ := by
      apply integral_mono ((hgi.sub hfi).div_const t).norm (hdi.norm.const_mul (L : ℝ))
      intro x
      have h := div_le_div_of_nonneg_right (hψ.dist_le_mul (g x) (f x)) (abs_nonneg t)
      simpa only [Pi.sub_apply, Real.dist_eq, Real.norm_eq_abs, abs_div, mul_div_assoc] using h

theorem tendsto_lipschitz_test_difference_quotient_zero
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f g : ℝ → X → ℝ) (ψ : ℝ → ℝ) (L : ℝ≥0) (hψ : LipschitzWith L ψ)
    (hint : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      Integrable (fun x => ψ (f t x)) μ ∧ Integrable (fun x => ψ (g t x)) μ ∧
        Integrable (fun x => (g t x - f t x) / t) μ)
    (hL1 : Tendsto (fun t : ℝ => ∫ x, |(g t x - f t x) / t| ∂μ)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun t : ℝ =>
      ((∫ x, ψ (g t x) ∂μ) - ∫ x, ψ (f t x) ∂μ) / t)
      (𝓝[>] 0) (𝓝 0) := by
  have hbound : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      |((∫ x, ψ (g t x) ∂μ) - ∫ x, ψ (f t x) ∂μ) / t| ≤
        (L : ℝ) * ∫ x, |(g t x - f t x) / t| ∂μ := by
    filter_upwards [hint] with t ht
    exact integral_lipschitz_difference_quotient_le_mul μ (f t) (g t) ψ L t hψ
      ht.1 ht.2.1 ht.2.2
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [Real.norm_eq_abs] using
    squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) hbound
      (by simpa only [mul_zero] using tendsto_const_nhds.mul hL1)

/-- A direct zero first derivative, with no differentiation of the Lipschitz
test itself. The base quantiles only need to agree almost everywhere. -/
theorem hasDerivWithinAt_lipschitz_test_difference_zero
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f g : ℝ → X → ℝ) (ψ : ℝ → ℝ) (L : ℝ≥0) (hψ : LipschitzWith L ψ)
    (hbase : g 0 =ᵐ[μ] f 0)
    (hint : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      Integrable (fun x => ψ (f t x)) μ ∧ Integrable (fun x => ψ (g t x)) μ ∧
        Integrable (fun x => (g t x - f t x) / t) μ)
    (hL1 : Tendsto (fun t : ℝ => ∫ x, |(g t x - f t x) / t| ∂μ)
      (𝓝[>] 0) (𝓝 0)) :
    HasDerivWithinAt (fun t : ℝ =>
      (∫ x, ψ (g t x) ∂μ) - ∫ x, ψ (f t x) ∂μ) 0 (Ici 0) 0 := by
  have hzero : (∫ x, ψ (g 0 x) ∂μ) - ∫ x, ψ (f 0 x) ∂μ = 0 := by
    apply sub_eq_zero.mpr
    exact integral_congr_ae (hbase.fun_comp ψ)
  exact (hasDerivWithinAt_Ici_zero_iff_div hzero).mpr
    (tendsto_lipschitz_test_difference_quotient_zero μ f g ψ L hψ hint hL1)

section Frequency

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem exists_unit_frequency (ξ : E) (hξ : ξ ≠ 0) :
    ∃ e : E, ‖e‖ = 1 ∧ ∀ x : E, ⟪x, ξ⟫ = ‖ξ‖ * ⟪e, x⟫ := by
  have hp : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  refine ⟨‖ξ‖⁻¹ • ξ, ?_, ?_⟩
  · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hp.le), inv_mul_cancel₀ hp.ne']
  · intro x
    rw [real_inner_smul_left, ← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul, real_inner_comm]

variable [MeasurableSpace E]

/-- Unit height directions and arbitrary Lipschitz scalar tests provide all
Fourier frequencies. The zero frequency follows from the actual probability
normalization, and is not discarded. -/
theorem all_frequencies_of_unit_lipschitz_variations
    (μ ν : ℝ → Measure E)
    (hμ : ∀ t, IsProbabilityMeasure (μ t)) (hν : ∀ t, IsProbabilityMeasure (ν t))
    (hunit : ∀ e : E, ‖e‖ = 1 → ∀ (ψ : ℝ → ℝ) (L : ℝ≥0), LipschitzWith L ψ →
      HasDerivWithinAt (fun t : ℝ => (∫ x, ψ ⟪e, x⟫ ∂μ t) - ∫ x, ψ ⟪e, x⟫ ∂ν t)
        0 (Ici 0) 0)
    (ψ : ℝ → ℝ) (L : ℝ≥0) (hψ : LipschitzWith L ψ) (ξ : E) :
    HasDerivWithinAt (fun t : ℝ => (∫ x, ψ ⟪x, ξ⟫ ∂μ t) - ∫ x, ψ ⟪x, ξ⟫ ∂ν t)
      0 (Ici 0) 0 := by
  by_cases hξ : ξ = 0
  · subst ξ
    have he : (fun t : ℝ => (∫ x, ψ ⟪x, (0 : E)⟫ ∂μ t) -
        ∫ x, ψ ⟪x, (0 : E)⟫ ∂ν t) = fun _ => 0 := by
      funext t
      letI := hμ t
      letI := hν t
      simp
    rw [he]
    exact hasDerivWithinAt_const _ _ _
  · obtain ⟨e, he, hinner⟩ := exists_unit_frequency ξ hξ
    have hscaled : LipschitzWith (L * ‖(‖ξ‖ : ℝ)‖₊)
        (fun s : ℝ => ψ (‖ξ‖ * s)) := by
      simpa only [Function.comp_def, smul_eq_mul] using
        hψ.comp (lipschitzWith_smul (β := ℝ) ‖ξ‖)
    simpa only [← hinner] using hunit e he (fun s => ψ (‖ξ‖ * s)) _ hscaled

theorem fourier_variations_of_unit_lipschitz_variations
    (μ ν : ℝ → Measure E)
    (hμ : ∀ t, IsProbabilityMeasure (μ t)) (hν : ∀ t, IsProbabilityMeasure (ν t))
    (hunit : ∀ e : E, ‖e‖ = 1 → ∀ (ψ : ℝ → ℝ) (L : ℝ≥0), LipschitzWith L ψ →
      HasDerivWithinAt (fun t : ℝ => (∫ x, ψ ⟪e, x⟫ ∂μ t) - ∫ x, ψ ⟪e, x⟫ ∂ν t)
        0 (Ici 0) 0) :
    (∀ ξ : E, HasDerivWithinAt
      (fun t : ℝ => (∫ x, Real.cos ⟪x, ξ⟫ ∂μ t) - ∫ x, Real.cos ⟪x, ξ⟫ ∂ν t)
      0 (Ici 0) 0) ∧
    (∀ ξ : E, HasDerivWithinAt
      (fun t : ℝ => (∫ x, Real.sin ⟪x, ξ⟫ ∂μ t) - ∫ x, Real.sin ⟪x, ξ⟫ ∂ν t)
      0 (Ici 0) 0) :=
  ⟨all_frequencies_of_unit_lipschitz_variations μ ν hμ hν hunit
      Real.cos 1 Real.lipschitzWith_cos,
    all_frequencies_of_unit_lipschitz_variations μ ν hμ hν hunit
      Real.sin 1 Real.lipschitzWith_sin⟩

end Frequency
end RankThreeProjection.QuantileStability
