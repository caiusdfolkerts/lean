module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# A Hilbert-space realization of the corner-energy kernel

The feature function `1_{t ≤ x} exp ((t-x)/2)` is an actual element of real L².
Its inner product with the feature at `y` is exactly `exp (-|x-y|/2)`.
This provides positivity and Cauchy–Schwarz for the kernel without assuming
a Fourier-transform formula.
-/

open MeasureTheory Set Filter
open scoped Topology InnerProductSpace RealInnerProductSpace

namespace VolumePolynomials

noncomputable def cornerKernel (x y : ℝ) : ℝ := Real.exp (-|x - y| / 2)

theorem cornerKernel_of_le {x y : ℝ} (hxy : x ≤ y) :
    cornerKernel x y = Real.exp ((x - y) / 2) := by
  unfold cornerKernel
  rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
  congr 1
  ring

theorem cornerKernel_of_ge {x y : ℝ} (hyx : y ≤ x) :
    cornerKernel x y = Real.exp ((y - x) / 2) := by
  unfold cornerKernel
  rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
  congr 1
  ring

theorem cornerKernel_pos (x y : ℝ) : 0 < cornerKernel x y := Real.exp_pos _

theorem cornerKernel_le_one (x y : ℝ) : cornerKernel x y ≤ 1 := by
  unfold cornerKernel
  apply Real.exp_le_one_iff.mpr
  linarith [abs_nonneg (x - y)]

theorem continuous_cornerKernel (x : ℝ) : Continuous (cornerKernel x) := by
  unfold cornerKernel
  fun_prop

theorem integrable_cornerKernel (μ : Measure ℝ) [IsFiniteMeasure μ] (x : ℝ) :
    Integrable (cornerKernel x) μ := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
    (continuous_cornerKernel x).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro y
  simpa only [Real.norm_eq_abs, abs_of_pos (cornerKernel_pos x y)] using
    cornerKernel_le_one x y

noncomputable def cornerFeatureFn (x : ℝ) : ℝ → ℝ :=
  (Iic x).indicator (fun t => Real.exp ((t - x) / 2))

theorem cornerFeatureFn_sq (x t : ℝ) :
    cornerFeatureFn x t ^ 2 = (Iic x).indicator (fun z => Real.exp (z - x)) t := by
  by_cases ht : t ≤ x
  · simp only [cornerFeatureFn, indicator_of_mem (show t ∈ Iic x from ht)]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  · simp [cornerFeatureFn, ht]

theorem cornerFeatureFn_measurable (x : ℝ) : Measurable (cornerFeatureFn x) := by
  apply Measurable.indicator _ measurableSet_Iic
  fun_prop

theorem cornerFeatureFn_memLp (x : ℝ) : MemLp (cornerFeatureFn x) 2 := by
  apply (memLp_two_iff_integrable_sq (cornerFeatureFn_measurable x).aestronglyMeasurable).mpr
  have hi : IntegrableOn (fun t : ℝ => Real.exp (t - x)) (Iic x) := by
    change Integrable (fun t : ℝ => Real.exp (t - x)) (volume.restrict (Iic x))
    apply Integrable.congr ((integrableOn_exp_Iic x).mul_const (Real.exp x)⁻¹)
    exact Filter.Eventually.of_forall fun t => by
      dsimp only
      rw [Real.exp_sub, div_eq_mul_inv]
  simpa only [cornerFeatureFn_sq] using hi.integrable_indicator measurableSet_Iic

noncomputable def cornerFeature (x : ℝ) : Lp ℝ 2 (volume : Measure ℝ) :=
  (cornerFeatureFn_memLp x).toLp (cornerFeatureFn x)

theorem cornerFeature_coe (x : ℝ) :
    (cornerFeature x : ℝ → ℝ) =ᵐ[volume] cornerFeatureFn x :=
  (cornerFeatureFn_memLp x).coeFn_toLp

theorem cornerFeatureFn_mul (x y t : ℝ) :
    cornerFeatureFn x t * cornerFeatureFn y t =
      (Iic (min x y)).indicator
        (fun z => Real.exp (-(x + y) / 2) * Real.exp z) t := by
  by_cases hx : t ≤ x <;> by_cases hy : t ≤ y
  · simp only [cornerFeatureFn, indicator_of_mem (show t ∈ Iic x from hx),
      indicator_of_mem (show t ∈ Iic y from hy),
      indicator_of_mem (show t ∈ Iic (min x y) from le_min hx hy)]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  · have hn : ¬t ≤ min x y := fun h => hy (h.trans (min_le_right _ _))
    simp [cornerFeatureFn, hx, hy, hn]
  · have hn : ¬t ≤ min x y := fun h => hx (h.trans (min_le_left _ _))
    simp [cornerFeatureFn, hx, hy, hn]
  · have hn : ¬t ≤ min x y := fun h => hx (h.trans (min_le_left _ _))
    simp [cornerFeatureFn, hx, hy, hn]

theorem integral_cornerFeatureFn_mul (x y : ℝ) :
    (∫ t : ℝ, cornerFeatureFn x t * cornerFeatureFn y t) = cornerKernel x y := by
  simp_rw [cornerFeatureFn_mul]
  rw [integral_indicator measurableSet_Iic, integral_const_mul, integral_exp_Iic,
    ← Real.exp_add]
  unfold cornerKernel
  congr 1
  rcases le_total x y with hxy | hyx
  · rw [min_eq_left hxy, abs_of_nonpos (sub_nonpos.mpr hxy)]
    ring
  · rw [min_eq_right hyx, abs_of_nonneg (sub_nonneg.mpr hyx)]
    ring

theorem inner_cornerFeature (x y : ℝ) :
    ⟪cornerFeature x, cornerFeature y⟫_ℝ = cornerKernel x y := by
  rw [L2.inner_def]
  apply Eq.trans _ (integral_cornerFeatureFn_mul x y)
  apply integral_congr_ae
  filter_upwards [cornerFeature_coe x, cornerFeature_coe y] with t hx hy
  simp only [Real.inner_apply, hx, hy]

theorem norm_cornerFeature (x : ℝ) : ‖cornerFeature x‖ = 1 := by
  have hsquare : ‖cornerFeature x‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, inner_cornerFeature]
    simp [cornerKernel]
  nlinarith [norm_nonneg (cornerFeature x)]

theorem norm_sub_cornerFeature (x y : ℝ) :
    ‖cornerFeature x - cornerFeature y‖ =
      Real.sqrt (2 - 2 * cornerKernel x y) := by
  rw [← Real.sqrt_sq (norm_nonneg (cornerFeature x - cornerFeature y)),
    norm_sub_sq_real, norm_cornerFeature, norm_cornerFeature, inner_cornerFeature]
  congr 1
  ring

theorem continuous_cornerFeature : Continuous cornerFeature := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp_rw [norm_sub_cornerFeature]
  have hcont : Continuous (fun y : ℝ => Real.sqrt (2 - 2 * cornerKernel y x)) := by
    unfold cornerKernel
    fun_prop
  simpa [cornerKernel] using hcont.tendsto x

theorem integrable_cornerFeature (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable cornerFeature μ := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
    continuous_cornerFeature.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => (norm_cornerFeature x).le

noncomputable def cornerMean (μ : Measure ℝ) : Lp ℝ 2 (volume : Measure ℝ) :=
  ∫ x, cornerFeature x ∂μ

theorem inner_cornerFeature_mean (μ : Measure ℝ) [IsFiniteMeasure μ] (x : ℝ) :
    ⟪cornerFeature x, cornerMean μ⟫_ℝ = ∫ y, cornerKernel x y ∂μ := by
  rw [cornerMean, ← integral_inner (integrable_cornerFeature μ)]
  simp_rw [inner_cornerFeature]

/-- The nonnegative Hilbert energy is the actual double integral of the kernel. -/
theorem norm_cornerMean_sq (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ‖cornerMean μ‖ ^ 2 = ∫ x, ∫ y, cornerKernel x y ∂μ ∂μ := by
  rw [← real_inner_self_eq_norm_sq, cornerMean, ← integral_inner (integrable_cornerFeature μ)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  dsimp only
  rw [real_inner_comm]
  exact inner_cornerFeature_mean μ x

end VolumePolynomials
