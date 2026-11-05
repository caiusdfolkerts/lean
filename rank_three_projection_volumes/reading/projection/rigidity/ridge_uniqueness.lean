module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Uniqueness from one-dimensional smooth tests

Sine and cosine tests suffice to determine a finite measure. Consequently, a
real integrable density on a compact parameter space is determined by these
tests after a continuous injective parametrization. This is the precise
measure-theoretic bridge from quantile variations to radial boundary data.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory Filter
open scoped RealInnerProductSpace

namespace RankThreeProjection.Rigidity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]

/-- Smooth one-dimensional ridge tests determine finite measures. -/
theorem measure_eq_of_cos_sin_integrals (μ ν : Measure E)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hcos : ∀ ξ : E, (∫ x, Real.cos ⟪x, ξ⟫ ∂μ) = ∫ x, Real.cos ⟪x, ξ⟫ ∂ν)
    (hsin : ∀ ξ : E, (∫ x, Real.sin ⟪x, ξ⟫ ∂μ) = ∫ x, Real.sin ⟪x, ξ⟫ ∂ν) :
    μ = ν := by
  apply Measure.ext_of_charFun
  funext ξ
  have hi (η : Measure E) [IsFiniteMeasure η] :
      Integrable (fun x : E => Complex.exp ((⟪x, ξ⟫ : ℂ) * Complex.I)) η := by
    apply (integrable_const (1 : ℝ)).mono (by fun_prop)
    filter_upwards with x
    simp only [Complex.norm_exp_ofReal_mul_I, norm_one, le_refl]
  have hre (η : Measure E) [IsFiniteMeasure η] :
      (∫ x : E, Complex.exp ((⟪x, ξ⟫ : ℂ) * Complex.I) ∂η).re =
        ∫ x : E, Real.cos ⟪x, ξ⟫ ∂η := by
    simpa only [Complex.reCLM_apply, Function.comp_def, Complex.exp_ofReal_mul_I_re] using
      (Complex.reCLM.integral_comp_comm (hi η)).symm
  have him (η : Measure E) [IsFiniteMeasure η] :
      (∫ x : E, Complex.exp ((⟪x, ξ⟫ : ℂ) * Complex.I) ∂η).im =
        ∫ x : E, Real.sin ⟪x, ξ⟫ ∂η := by
    simpa only [Complex.imCLM_apply, Function.comp_def, Complex.exp_ofReal_mul_I_im] using
      (Complex.imCLM.integral_comp_comm (hi η)).symm
  apply Complex.ext
  · simpa only [charFun_apply, hre μ, hre ν] using hcos ξ
  · simpa only [charFun_apply, him μ, him ν] using hsin ξ

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- A positive integrable density is recovered from its sine/cosine moments
under any measurable embedding. No differentiability of the embedding is
required. -/
theorem ae_eq_of_weighted_ridge_integrals {r : X → E} (hr : MeasurableEmbedding r)
    {f g : X → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hcos : ∀ ξ : E, (∫ x, f x * Real.cos ⟪r x, ξ⟫ ∂μ) =
      ∫ x, g x * Real.cos ⟪r x, ξ⟫ ∂μ)
    (hsin : ∀ ξ : E, (∫ x, f x * Real.sin ⟪r x, ξ⟫ ∂μ) =
      ∫ x, g x * Real.sin ⟪r x, ξ⟫ ∂μ) : f =ᵐ[μ] g := by
  let μf := μ.withDensity (fun x => ENNReal.ofReal (f x))
  let μg := μ.withDensity (fun x => ENNReal.ofReal (g x))
  have hfm : AEMeasurable (fun x => ENNReal.ofReal (f x)) μ :=
    hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hgm : AEMeasurable (fun x => ENNReal.ofReal (g x)) μ :=
    hg.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hfi : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≠ ⊤ :=
    (lintegral_ofReal_ne_top_iff_integrable hf.aestronglyMeasurable
      (Eventually.of_forall hf0)).mpr hf
  letI : IsFiniteMeasure μf := isFiniteMeasure_withDensity hfi
  letI : IsFiniteMeasure μg := isFiniteMeasure_withDensity
    ((lintegral_ofReal_ne_top_iff_integrable hg.aestronglyMeasurable
      (Eventually.of_forall hg0)).mpr hg)
  have hfint (φ : E → ℝ) (hφ : Measurable φ) :
      (∫ y, φ y ∂μf.map r) = ∫ x, f x * φ (r x) ∂μ := by
    rw [integral_map hr.measurable.aemeasurable hφ.aestronglyMeasurable,
      integral_withDensity_eq_integral_toReal_smul₀ hfm
        (Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (hf0 _), smul_eq_mul]
  have hgint (φ : E → ℝ) (hφ : Measurable φ) :
      (∫ y, φ y ∂μg.map r) = ∫ x, g x * φ (r x) ∂μ := by
    rw [integral_map hr.measurable.aemeasurable hφ.aestronglyMeasurable,
      integral_withDensity_eq_integral_toReal_smul₀ hgm
        (Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (hg0 _), smul_eq_mul]
  have he : μf.map r = μg.map r := by
    apply measure_eq_of_cos_sin_integrals
    · intro ξ
      rw [hfint _ (by fun_prop), hgint _ (by fun_prop)]
      exact hcos ξ
    · intro ξ
      rw [hfint _ (by fun_prop), hgint _ (by fun_prop)]
      exact hsin ξ
  have he' : μf = μg := hr.map_injective he
  have hae := (withDensity_eq_iff hfm hgm hfi).mp he'
  filter_upwards [hae] with x hx
  simpa only [ENNReal.toReal_ofReal (hf0 x), ENNReal.toReal_ofReal (hg0 x)] using
    congrArg ENNReal.toReal hx

/-- The signed-density form, used when the two comparison bodies differ by
a translation. It only requires sine and cosine moments, not every spatial
continuous test. -/
theorem ae_zero_of_weighted_ridge_integrals {r : X → E} (hr : MeasurableEmbedding r)
    {f : X → ℝ} (hf : Integrable f μ)
    (hcos : ∀ ξ : E, (∫ x, f x * Real.cos ⟪r x, ξ⟫ ∂μ) = 0)
    (hsin : ∀ ξ : E, (∫ x, f x * Real.sin ⟪r x, ξ⟫ ∂μ) = 0) :
    f =ᵐ[μ] 0 := by
  have hprod (g : X → ℝ) (hg : Integrable g μ) (φ : X → ℝ)
      (hφm : Measurable φ) (hφb : ∀ x, ‖φ x‖ ≤ 1) :
      Integrable (fun x => g x * φ x) μ := by
    apply hg.norm.mono (hg.aestronglyMeasurable.mul hφm.aestronglyMeasurable)
    filter_upwards with x
    rw [Pi.mul_apply, norm_mul, norm_norm]
    exact mul_le_of_le_one_right (norm_nonneg _) (hφb x)
  have hm (φ : X → ℝ) (hφm : Measurable φ) (hφb : ∀ x, ‖φ x‖ ≤ 1)
      (hzero : (∫ x, f x * φ x ∂μ) = 0) :
      (∫ x, max (f x) 0 * φ x ∂μ) = ∫ x, max (-f x) 0 * φ x ∂μ := by
    apply sub_eq_zero.mp
    rw [← integral_sub (hprod _ hf.pos_part _ hφm hφb)
      (hprod _ hf.neg_part _ hφm hφb)]
    convert hzero using 1
    congr 1
    funext x
    rw [← sub_mul, max_zero_sub_max_neg_zero_eq_self]
  have he := ae_eq_of_weighted_ridge_integrals hr hf.pos_part hf.neg_part
    (fun x => le_max_right (f x) 0) (fun x => le_max_right (-f x) 0)
    (fun ξ => hm _ (by fun_prop)
      (fun x => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one ⟪r x, ξ⟫)
      (hcos ξ))
    (fun ξ => hm _ (by fun_prop)
      (fun x => by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one ⟪r x, ξ⟫)
      (hsin ξ))
  filter_upwards [he] with x hx
  change f x = 0
  have hp := max_zero_sub_max_neg_zero_eq_self (f x)
  rw [hx, sub_self] at hp
  exact hp.symm

/-- A convenient topological version for compact radial parametrizations. -/
theorem ae_zero_of_continuous_injective_ridge_integrals
    [TopologicalSpace X] [CompactSpace X] [BorelSpace X]
    {r : X → E} (hrc : Continuous r) (hri : Function.Injective r)
    {f : X → ℝ} (hf : Integrable f μ)
    (hcos : ∀ ξ : E, (∫ x, f x * Real.cos ⟪r x, ξ⟫ ∂μ) = 0)
    (hsin : ∀ ξ : E, (∫ x, f x * Real.sin ⟪r x, ξ⟫ ∂μ) = 0) :
    f =ᵐ[μ] 0 :=
  ae_zero_of_weighted_ridge_integrals (hrc.isClosedEmbedding hri).measurableEmbedding
    hf hcos hsin

end RankThreeProjection.Rigidity
