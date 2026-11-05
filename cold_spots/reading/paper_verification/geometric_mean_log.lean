module
public import PaperVerification.GeometricMean
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
@[expose] public section
/-! # Agreement of the truncated mean with extended logarithmic integration

For a bounded nonnegative continuous factor, the geometric mean is positive
exactly when the factor is positive almost everywhere and its logarithm is
integrable. In that case it equals exp(integral log); in every other case it is
zero. These facts justify the extended-logarithm convention used in the paper.
-/

noncomputable section

namespace PaperVerification.Hyperbolic

open MeasureTheory Set Filter Topology
open scoped ENNReal

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [CompactSpace X] [OpensMeasurableSpace X]

theorem truncatedLog_antitone (f : C(X, ℝ)) (x : X) :
    Antitone (fun n => truncatedLog f n x) := by
  intro n m hnm
  apply Real.log_le_log ((Real.exp_pos _).trans_le (le_max_left _ _))
  apply max_le_max_right
  exact Real.exp_le_exp.mpr (neg_le_neg (Nat.cast_le.mpr hnm))

/-- The positive loss below a fixed logarithmic upper bound. -/
def logarithmicLoss (f : C(X, ℝ)) (M : ℝ) (n : ℕ) (x : X) : ℝ :=
  Real.log M - truncatedLog f n x

/-- The possibly infinite negative part, after shifting by log M. -/
def extendedLogarithmicLoss (f : C(X, ℝ)) (M : ℝ) (x : X) : ℝ≥0∞ :=
  ⨆ n : ℕ, ENNReal.ofReal (logarithmicLoss f M n x)

theorem logarithmicLoss_nonneg (f : C(X, ℝ)) {M : ℝ} (hM : 1 ≤ M)
    (hfM : ∀ x, f x ≤ M) (n : ℕ) (x : X) : 0 ≤ logarithmicLoss f M n x := by
  apply sub_nonneg.mpr
  apply Real.log_le_log ((Real.exp_pos _).trans_le (le_max_left _ _))
  apply max_le
  · calc
      Real.exp (-(n : ℝ)) ≤ Real.exp 0 := Real.exp_le_exp.mpr (neg_nonpos.mpr (Nat.cast_nonneg _))
      _ = 1 := Real.exp_zero
      _ ≤ M := hM
  · exact hfM x

theorem logarithmicLoss_monotone (f : C(X, ℝ)) (M : ℝ) (x : X) :
    Monotone (fun n => logarithmicLoss f M n x) :=
  fun n m hnm => sub_le_sub_left (truncatedLog_antitone f x hnm) _

theorem measurable_extendedLogarithmicLoss (f : C(X, ℝ)) (M : ℝ) :
    Measurable (extendedLogarithmicLoss f M) := by
  apply Measurable.iSup
  intro n
  exact (continuous_const.sub (truncatedLog f n).continuous).measurable.ennreal_ofReal

theorem extendedLogarithmicLoss_of_pos (f : C(X, ℝ)) (M : ℝ) (x : X)
    (hx : 0 < f x) :
    extendedLogarithmicLoss f M x = ENNReal.ofReal (Real.log M - Real.log (f x)) := by
  apply le_antisymm
  · apply iSup_le
    intro n
    apply ENNReal.ofReal_le_ofReal
    apply sub_le_sub_left
    exact Real.log_le_log hx (le_max_right _ _)
  · obtain ⟨n, hn⟩ := exists_nat_gt (-Real.log (f x))
    have hc : Real.exp (-(n : ℝ)) ≤ f x := by
      calc Real.exp (-(n : ℝ)) ≤ Real.exp (Real.log (f x)) :=
             Real.exp_le_exp.mpr (by linarith)
           _ = f x := Real.exp_log hx
    have heq : logarithmicLoss f M n x = Real.log M - Real.log (f x) := by
      unfold logarithmicLoss truncatedLog
      simp only [ContinuousMap.coe_mk, max_eq_right hc]
    rw [← heq]
    exact le_iSup (fun n => ENNReal.ofReal (logarithmicLoss f M n x)) n

theorem extendedLogarithmicLoss_of_zero (f : C(X, ℝ)) {M : ℝ} (hM : 1 ≤ M)
    (x : X) (hx : f x = 0) : extendedLogarithmicLoss f M x = ∞ := by
  apply top_unique
  rw [← ENNReal.iSup_natCast]
  apply iSup_le
  intro n
  have hn : ENNReal.ofReal (n : ℝ) ≤ ENNReal.ofReal (logarithmicLoss f M n x) := by
    apply ENNReal.ofReal_le_ofReal
    unfold logarithmicLoss truncatedLog
    simp only [ContinuousMap.coe_mk, hx, max_eq_left (Real.exp_pos _).le, Real.log_exp]
    linarith only [Real.log_nonneg hM]
  calc
    (n : ℝ≥0∞) ≤ ENNReal.ofReal (logarithmicLoss f M n x) := by
      simpa only [ENNReal.ofReal_natCast] using hn
    _ ≤ extendedLogarithmicLoss f M x :=
      le_iSup (fun j => ENNReal.ofReal (logarithmicLoss f M j x)) n

/-- Positive geometric moment bounds the entire negative logarithmic part. -/
theorem lintegral_extendedLogarithmicLoss_le
    (k : ℝ) (hk : 0 < k) (f : C(X, ℝ)) (μ : ProbabilityMeasure X)
    {M : ℝ} (hM : 1 ≤ M) (hfM : ∀ x, f x ≤ M)
    (hG : 0 < geometricMoment k f μ) :
    (∫⁻ x, extendedLogarithmicLoss f M x ∂μ) ≤
      ENNReal.ofReal (Real.log M - Real.log (geometricMoment k f μ) / k) := by
  have hmeas : ∀ n, Measurable (fun x => ENNReal.ofReal (logarithmicLoss f M n x)) :=
    fun n => (continuous_const.sub (truncatedLog f n).continuous).measurable.ennreal_ofReal
  have hmono : Monotone (fun n x => ENNReal.ofReal (logarithmicLoss f M n x)) := by
    intro n m hnm x
    exact ENNReal.ofReal_le_ofReal (logarithmicLoss_monotone f M x hnm)
  change (∫⁻ x, ⨆ n : ℕ, ENNReal.ofReal (logarithmicLoss f M n x) ∂μ) ≤ _
  rw [lintegral_iSup hmeas hmono]
  apply iSup_le
  intro n
  have hlower : Real.log (geometricMoment k f μ) / k ≤ ∫ x, truncatedLog f n x ∂μ := by
    apply (div_le_iff₀ hk).mpr
    have hlog := Real.log_le_log hG (geometricMoment_le_truncated k f μ n)
    simpa only [truncatedGeometricMoment, Real.log_exp, mul_comm] using hlog
  have hint : Integrable (logarithmicLoss f M n) (μ : Measure X) :=
    (integrable_const _).sub (integrable_continuousMap (truncatedLog f n) μ)
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall (logarithmicLoss_nonneg f hM hfM n))]
  apply ENNReal.ofReal_le_ofReal
  unfold logarithmicLoss
  rw [integral_sub (integrable_const _) (integrable_continuousMap (truncatedLog f n) μ)]
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  linarith

/-- Positivity forces almost-everywhere positivity and genuine logarithmic integrability. -/
theorem ae_pos_and_integrable_log_of_geometricMoment_pos
    (k : ℝ) (hk : 0 < k) (f : C(X, ℝ)) (μ : ProbabilityMeasure X)
    (hf : ∀ x, 0 ≤ f x) (hG : 0 < geometricMoment k f μ) :
    (∀ᵐ x ∂(μ : Measure X), 0 < f x) ∧
      Integrable (fun x => Real.log (f x)) (μ : Measure X) := by
  let M : ℝ := 1 + ‖BoundedContinuousFunction.mkOfCompact f‖
  have hM : 1 ≤ M := le_add_of_nonneg_right (norm_nonneg (BoundedContinuousFunction.mkOfCompact f))
  have hfM : ∀ x, f x ≤ M := by
    intro x
    exact ((BoundedContinuousFunction.mkOfCompact f).apply_le_norm x).trans
      (le_add_of_nonneg_left zero_le_one)
  have hbound := lintegral_extendedLogarithmicLoss_le k hk f μ hM hfM hG
  have hfinite : (∫⁻ x, extendedLogarithmicLoss f M x ∂μ) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound
  have hae := ae_lt_top (measurable_extendedLogarithmicLoss f M) hfinite
  have hpos : ∀ᵐ x ∂(μ : Measure X), 0 < f x := by
    filter_upwards [hae] with x hx
    by_contra hn
    have hz : f x = 0 := le_antisymm (le_of_not_gt hn) (hf x)
    rw [extendedLogarithmicLoss_of_zero f hM x hz] at hx
    exact (lt_irrefl _ hx)
  refine ⟨hpos, ?_⟩
  have hI := integrable_toReal_of_lintegral_ne_top
    (measurable_extendedLogarithmicLoss f M).aemeasurable hfinite
  have hrep : (fun x => Real.log M - (extendedLogarithmicLoss f M x).toReal) =ᵐ[(μ : Measure X)]
      (fun x => Real.log (f x)) := by
    filter_upwards [hpos] with x hx
    rw [extendedLogarithmicLoss_of_pos f M x hx,
      ENNReal.toReal_ofReal (sub_nonneg.mpr (Real.log_le_log hx (hfM x)))]
    ring
  exact ((integrable_const _).sub hI).congr hrep

/-- Agreement with the ordinary integral whenever that integral is meaningful,
without requiring a uniform positive lower bound. -/
theorem geometricMoment_eq_exp_integral_of_integrable_log
    (k : ℝ) (hk : 0 ≤ k) (f : C(X, ℝ)) (μ : ProbabilityMeasure X)
    (hpos : ∀ᵐ x ∂(μ : Measure X), 0 < f x)
    (hlog : Integrable (fun x => Real.log (f x)) (μ : Measure X)) :
    geometricMoment k f μ = Real.exp (k * ∫ x, Real.log (f x) ∂μ) := by
  have hcut : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hconv : ∀ᵐ x ∂(μ : Measure X),
      Tendsto (fun n => truncatedLog f n x) atTop (𝓝 (Real.log (f x))) := by
    filter_upwards [hpos] with x hx
    have hm : Tendsto (fun n : ℕ => max (Real.exp (-(n : ℝ))) (f x)) atTop (𝓝 (f x)) := by
      simpa only [max_eq_right hx.le] using hcut.max
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => f x) atTop (𝓝 (f x)))
    exact hm.log hx.ne'
  have hI := integral_tendsto_of_tendsto_of_antitone
    (fun n => integrable_continuousMap (truncatedLog f n) μ) hlog
    (Filter.Eventually.of_forall (truncatedLog_antitone f)) hconv
  have hE := Real.continuous_exp.continuousAt.tendsto.comp (hI.const_mul k)
  exact tendsto_nhds_unique (tendsto_truncatedGeometricMoment k hk f μ) hE

/-- Full integrability criterion, including endpoint atoms and singular measures. -/
theorem geometricMoment_pos_iff
    (k : ℝ) (hk : 0 < k) (f : C(X, ℝ)) (μ : ProbabilityMeasure X)
    (hf : ∀ x, 0 ≤ f x) :
    0 < geometricMoment k f μ ↔
      (∀ᵐ x ∂(μ : Measure X), 0 < f x) ∧
        Integrable (fun x => Real.log (f x)) (μ : Measure X) := by
  constructor
  · exact ae_pos_and_integrable_log_of_geometricMoment_pos k hk f μ hf
  · rintro ⟨hpos, hlog⟩
    rw [geometricMoment_eq_exp_integral_of_integrable_log k hk.le f μ hpos hlog]
    exact Real.exp_pos _

/-- Vanishing is exactly the failure of the finite logarithmic-integral case. -/
theorem geometricMoment_eq_zero_iff
    (k : ℝ) (hk : 0 < k) (f : C(X, ℝ)) (μ : ProbabilityMeasure X)
    (hf : ∀ x, 0 ≤ f x) :
    geometricMoment k f μ = 0 ↔
      ¬ ((∀ᵐ x ∂(μ : Measure X), 0 < f x) ∧
        Integrable (fun x => Real.log (f x)) (μ : Measure X)) := by
  rw [← geometricMoment_pos_iff k hk f μ hf]
  constructor
  · intro hz
    rw [hz]
    exact lt_irrefl 0
  · intro hn
    exact le_antisymm (le_of_not_gt hn) (geometricMoment_nonneg k f μ)

/-- The coefficient-zero convention makes this weighted logarithm integrable
for every probability measure, even when log f itself is not integrable. -/
theorem integrable_geometricMoment_mul_log
    (k : ℝ) (hk : 0 < k) (f : C(X, ℝ)) (μ : ProbabilityMeasure X)
    (hf : ∀ x, 0 ≤ f x) :
    Integrable (fun x => geometricMoment k f μ * Real.log (f x)) (μ : Measure X) := by
  by_cases hzero : geometricMoment k f μ = 0
  · simpa only [hzero, zero_mul] using (integrable_const (0 : ℝ) :
      Integrable (fun _ : X => (0 : ℝ)) (μ : Measure X))
  · have hpos : 0 < geometricMoment k f μ :=
      lt_of_le_of_ne (geometricMoment_nonneg k f μ) (Ne.symm hzero)
    exact (ae_pos_and_integrable_log_of_geometricMoment_pos k hk f μ hf hpos).2.const_mul _

/-- Weighted logarithmic entropy identity, valid also at zero geometric moment. -/
theorem geometricMoment_mul_log_integral
    (k : ℝ) (hk : 0 < k) (f : C(X, ℝ)) (μ : ProbabilityMeasure X)
    (hf : ∀ x, 0 ≤ f x) :
    k * (∫ x, geometricMoment k f μ * Real.log (f x) ∂μ) =
      geometricMoment k f μ * Real.log (geometricMoment k f μ) := by
  by_cases hzero : geometricMoment k f μ = 0
  · simp only [hzero, zero_mul, integral_zero, mul_zero]
  · have hpos : 0 < geometricMoment k f μ :=
      lt_of_le_of_ne (geometricMoment_nonneg k f μ) (Ne.symm hzero)
    obtain ⟨hfae, hfint⟩ := ae_pos_and_integrable_log_of_geometricMoment_pos k hk f μ hf hpos
    have hlog : Real.log (geometricMoment k f μ) = k * ∫ x, Real.log (f x) ∂μ := by
      rw [geometricMoment_eq_exp_integral_of_integrable_log k hk.le f μ hfae hfint, Real.log_exp]
    rw [integral_const_mul, hlog]
    ring

end PaperVerification.Hyperbolic

#print axioms PaperVerification.Hyperbolic.geometricMoment_pos_iff
#print axioms PaperVerification.Hyperbolic.geometricMoment_eq_zero_iff
