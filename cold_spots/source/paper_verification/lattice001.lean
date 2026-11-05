module

public import Lean.Elab.BuiltinEvalCommand
public meta import Lean.Elab.BuiltinEvalCommand
public import Lean.Util.CollectAxioms
public meta import Lean.Util.CollectAxioms
public import Lean.Util.FoldConsts
public meta import Lean.Util.FoldConsts
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Topology.Semicontinuity.Basic

@[expose] public section


-- BEGIN ORIGINAL PaperVerification.GeometricMean
section Source_GeometricMean

-- original header: module
-- original header: public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
-- original header: public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
-- original header: public import Mathlib.Analysis.SpecialFunctions.Log.Basic
-- original header: public import Mathlib.Analysis.SpecialFunctions.Exp
-- original header: public import Mathlib.Topology.Semicontinuity.Basic
-- original header: public import Mathlib.Topology.Order.MonotoneConvergence
-- original header: public import Mathlib.Tactic.Linarith
-- original header: public import Mathlib.Tactic.NormNum
-- original header: @[expose] public section
/-! # Geometric means with vanishing factors and divergent logarithms

The logarithm is truncated continuously from below before integration. Taking
the decreasing limit of the exponentials retains the intended value zero when
the logarithmic integral is minus infinity. In particular, this definition does
not use Lean's default value for a nonintegrable Bochner integral as a substitute
for an extended logarithmic integral.
-/

noncomputable section

namespace PaperVerification.Hyperbolic

open MeasureTheory Set Filter Topology

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [CompactSpace X] [OpensMeasurableSpace X]

/-- Continuous truncation log(max(exp(-n),f)). -/
def truncatedLog (f : C(X, ℝ)) (n : ℕ) : C(X, ℝ) :=
  ⟨fun x => Real.log (max (Real.exp (-(n : ℝ))) (f x)),
    (continuous_const.max f.continuous).log
      (fun x => ne_of_gt ((Real.exp_pos _).trans_le (le_max_left _ _)))⟩

/-- Exponential of k times the truncated logarithmic integral. -/
def truncatedGeometricMoment (k : ℝ) (f : C(X, ℝ))
    (μ : ProbabilityMeasure X) (n : ℕ) : ℝ :=
  Real.exp (k * ∫ x, truncatedLog f n x ∂μ)

/-- exp(k integral log f), including exp(-infinity)=0 when k>0. -/
def geometricMoment (k : ℝ) (f : C(X, ℝ)) (μ : ProbabilityMeasure X) : ℝ :=
  ⨅ n : ℕ, truncatedGeometricMoment k f μ n

/-- Geometric mean under a probability measure, including zero values. -/
def geometricMean (f : C(X, ℝ)) (μ : ProbabilityMeasure X) : ℝ :=
  geometricMoment 1 f μ

theorem integrable_continuousMap (f : C(X, ℝ)) (μ : ProbabilityMeasure X) :
    Integrable f (μ : Measure X) :=
  (BoundedContinuousFunction.mkOfCompact f).integrable (μ : Measure X)

theorem truncatedGeometricMoment_pos (k : ℝ) (f : C(X, ℝ))
    (μ : ProbabilityMeasure X) (n : ℕ) : 0 < truncatedGeometricMoment k f μ n :=
  Real.exp_pos _

theorem truncatedGeometricMoment_bddBelow (k : ℝ) (f : C(X, ℝ))
    (μ : ProbabilityMeasure X) : BddBelow (range (truncatedGeometricMoment k f μ)) :=
  ⟨0, fun _ hx => by rcases hx with ⟨n, rfl⟩; exact (truncatedGeometricMoment_pos k f μ n).le⟩

theorem geometricMoment_nonneg (k : ℝ) (f : C(X, ℝ)) (μ : ProbabilityMeasure X) :
    0 ≤ geometricMoment k f μ := by
  apply le_ciInf
  intro n
  exact (truncatedGeometricMoment_pos k f μ n).le

theorem geometricMoment_le_truncated (k : ℝ) (f : C(X, ℝ))
    (μ : ProbabilityMeasure X) (n : ℕ) :
    geometricMoment k f μ ≤ truncatedGeometricMoment k f μ n :=
  ciInf_le (truncatedGeometricMoment_bddBelow k f μ) n

theorem continuous_truncatedGeometricMoment (k : ℝ) (f : C(X, ℝ)) (n : ℕ) :
    Continuous (fun μ : ProbabilityMeasure X => truncatedGeometricMoment k f μ n) :=
  Real.continuous_exp.comp
    ((ProbabilityMeasure.continuous_integral_continuousMap (truncatedLog f n)).const_mul k)

/-- Weak upper semicontinuity holds even when logarithmic integrability fails. -/
theorem upperSemicontinuous_geometricMoment (k : ℝ) (f : C(X, ℝ)) :
    UpperSemicontinuous (geometricMoment k f) := by
  apply upperSemicontinuous_ciInf (fun μ => truncatedGeometricMoment_bddBelow k f μ)
  intro n
  exact (continuous_truncatedGeometricMoment k f n).upperSemicontinuous

theorem truncatedGeometricMoment_antitone (k : ℝ) (hk : 0 ≤ k)
    (f : C(X, ℝ)) (μ : ProbabilityMeasure X) :
    Antitone (truncatedGeometricMoment k f μ) := by
  intro n m hnm
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ hk
  apply integral_mono (integrable_continuousMap (truncatedLog f m) μ)
    (integrable_continuousMap (truncatedLog f n) μ)
  intro x
  apply Real.log_le_log ((Real.exp_pos _).trans_le (le_max_left _ _))
  apply max_le_max_right
  apply Real.exp_le_exp.mpr
  exact neg_le_neg (Nat.cast_le.mpr hnm)

theorem tendsto_truncatedGeometricMoment (k : ℝ) (hk : 0 ≤ k)
    (f : C(X, ℝ)) (μ : ProbabilityMeasure X) :
    Tendsto (truncatedGeometricMoment k f μ) atTop (𝓝 (geometricMoment k f μ)) :=
  tendsto_atTop_ciInf (truncatedGeometricMoment_antitone k hk f μ)
    (truncatedGeometricMoment_bddBelow k f μ)

theorem geometricMoment_mono (k : ℝ) (hk : 0 ≤ k)
    {f g : C(X, ℝ)} (hfg : ∀ x, f x ≤ g x) (μ : ProbabilityMeasure X) :
    geometricMoment k f μ ≤ geometricMoment k g μ := by
  apply le_ciInf
  intro n
  apply (geometricMoment_le_truncated k f μ n).trans
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ hk
  apply integral_mono (integrable_continuousMap (truncatedLog f n) μ)
    (integrable_continuousMap (truncatedLog g n) μ)
  intro x
  apply Real.log_le_log ((Real.exp_pos _).trans_le (le_max_left _ _))
  exact max_le_max_left _ (hfg x)

/-- Agreement with the ordinary logarithmic integral whenever a positive
uniform lower bound is available. -/
theorem geometricMoment_eq_exp_integral_of_lower_bound
    (k : ℝ) (hk : 0 ≤ k) (f : C(X, ℝ)) (μ : ProbabilityMeasure X)
    {m : ℝ} (hm : 0 < m) (hf : ∀ x, m ≤ f x) :
    geometricMoment k f μ = Real.exp (k * ∫ x, Real.log (f x) ∂μ) := by
  let logf : C(X, ℝ) := ⟨fun x => Real.log (f x),
    f.continuous.log (fun x => (hm.trans_le (hf x)).ne')⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (-Real.log m)
  have hcut : Real.exp (-(n : ℝ)) ≤ m := by
    calc
      Real.exp (-(n : ℝ)) ≤ Real.exp (Real.log m) := Real.exp_le_exp.mpr (by linarith)
      _ = m := Real.exp_log hm
  apply le_antisymm
  · apply (geometricMoment_le_truncated k f μ n).trans_eq
    unfold truncatedGeometricMoment
    congr 2
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by
      change Real.log (max (Real.exp (-(n : ℝ))) (f x)) = Real.log (f x)
      rw [max_eq_right (hcut.trans (hf x))])
  · apply le_ciInf
    intro j
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hk
    apply integral_mono (integrable_continuousMap logf μ)
      (integrable_continuousMap (truncatedLog f j) μ)
    intro x
    exact Real.log_le_log (hm.trans_le (hf x)) (le_max_right _ _)

/-- The k=0 convention is one, including for zero functions. -/
theorem geometricMoment_zero (f : C(X, ℝ)) (μ : ProbabilityMeasure X) :
    geometricMoment 0 f μ = 1 := by
  simp only [geometricMoment, truncatedGeometricMoment, zero_mul, Real.exp_zero, ciInf_const]

/-- Natural powers commute with the geometric mean, including at zero. -/
theorem geometricMoment_nat (n : ℕ) (f : C(X, ℝ)) (μ : ProbabilityMeasure X) :
    geometricMoment (n : ℝ) f μ = geometricMean f μ ^ n := by
  have h₁ := (tendsto_truncatedGeometricMoment 1 (by norm_num) f μ).pow n
  have h₂ := tendsto_truncatedGeometricMoment (n : ℝ) (Nat.cast_nonneg _) f μ
  have heq : (fun j => truncatedGeometricMoment 1 f μ j ^ n) =
      truncatedGeometricMoment (n : ℝ) f μ := by
    funext j
    simp only [truncatedGeometricMoment, one_mul, Real.exp_nat_mul]
  rw [heq] at h₁
  exact (tendsto_nhds_unique h₂ h₁)

theorem geometricMean_nonneg (f : C(X, ℝ)) (μ : ProbabilityMeasure X) :
    0 ≤ geometricMean f μ := geometricMoment_nonneg 1 f μ

/-- A positive lower bound makes the geometric moment continuous in the measure. -/
theorem continuous_geometricMoment_of_lower_bound
    (k : ℝ) (hk : 0 ≤ k) (f : C(X, ℝ)) {m : ℝ} (hm : 0 < m)
    (hf : ∀ x, m ≤ f x) : Continuous (geometricMoment k f) := by
  let logf : C(X, ℝ) := ⟨fun x => Real.log (f x),
    f.continuous.log (fun x => (hm.trans_le (hf x)).ne')⟩
  have heq : geometricMoment k f = fun μ : ProbabilityMeasure X => Real.exp (k * ∫ x, logf x ∂μ) := by
    funext μ
    exact geometricMoment_eq_exp_integral_of_lower_bound k hk f μ hm hf
  rw [heq]
  exact Real.continuous_exp.comp ((ProbabilityMeasure.continuous_integral_continuousMap logf).const_mul k)

/-- Multiplication by a positive constant has the expected natural-power law
when the continuous factor has a positive lower bound. -/
theorem geometricMoment_nat_const_mul_of_lower_bound
    (n : ℕ) (f : C(X, ℝ)) (μ : ProbabilityMeasure X) {c m : ℝ}
    (hc : 0 < c) (hm : 0 < m) (hf : ∀ x, m ≤ f x) :
    geometricMoment (n : ℝ) (⟨fun x => c * f x, continuous_const.mul f.continuous⟩ : C(X, ℝ)) μ =
      c ^ n * geometricMoment (n : ℝ) f μ := by
  let logf : C(X, ℝ) := ⟨fun x => Real.log (f x),
    f.continuous.log (fun x => (hm.trans_le (hf x)).ne')⟩
  rw [geometricMoment_eq_exp_integral_of_lower_bound (n : ℝ) (Nat.cast_nonneg _) _ μ
    (mul_pos hc hm) (fun x => mul_le_mul_of_nonneg_left (hf x) hc.le)]
  rw [geometricMoment_eq_exp_integral_of_lower_bound (n : ℝ) (Nat.cast_nonneg _) f μ hm hf]
  have heq : (fun x => Real.log (c * f x)) = fun x => Real.log c + logf x := by
    funext x
    exact Real.log_mul hc.ne' (hm.trans_le (hf x)).ne'
  simp only [ContinuousMap.coe_mk] at *
  rw [heq, integral_add (integrable_const _) (integrable_continuousMap logf μ)]
  simp only [integral_const, MeasureTheory.ProbabilityMeasure.coeFn_univ, measureReal_def,
    measure_univ, ENNReal.toReal_one, one_smul]
  rw [mul_add, Real.exp_add, Real.exp_nat_mul, Real.exp_log hc]
  rfl

theorem one_le_geometricMoment_of_one_le
    (k : ℝ) (hk : 0 ≤ k) (f : C(X, ℝ)) (μ : ProbabilityMeasure X)
    (hf : ∀ x, 1 ≤ f x) : 1 ≤ geometricMoment k f μ := by
  rw [geometricMoment_eq_exp_integral_of_lower_bound k hk f μ (by norm_num) hf]
  apply Real.one_le_exp_iff.mpr
  apply mul_nonneg hk
  apply integral_nonneg
  intro x
  exact Real.log_nonneg (hf x)

end PaperVerification.Hyperbolic

#print axioms PaperVerification.Hyperbolic.upperSemicontinuous_geometricMoment
#print axioms PaperVerification.Hyperbolic.geometricMoment_eq_exp_integral_of_lower_bound
#print axioms PaperVerification.Hyperbolic.geometricMoment_nat
end
end Source_GeometricMean
-- END ORIGINAL PaperVerification.GeometricMean


-- BEGIN ORIGINAL PaperVerification.GeometricMeanLog
section Source_GeometricMeanLog

-- original header: module
-- original header: public import PaperVerification.GeometricMean
-- original header: public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
-- original header: public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
-- original header: public import Mathlib.Analysis.SpecialFunctions.Exp
-- original header: public import Mathlib.Topology.ContinuousMap.Bounded.Normed
-- original header: @[expose] public section
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
end
end Source_GeometricMeanLog
-- END ORIGINAL PaperVerification.GeometricMeanLog


-- BEGIN ORIGINAL PaperVerification.GeometricMeanExtended
section Source_GeometricMeanExtended

-- original header: module
-- original header: public import PaperVerification.GeometricMeanLog
-- original header: @[expose] public section
/-! # Explicit extended-integral semantics

A logarithmic upper bound converts the extended logarithmic integral to the
Lebesgue integral of a nonnegative ENNReal function.  This file proves that
the regularized geometric mean is exactly its exponential, with the required
value zero when that integral is infinite.
-/

noncomputable section

namespace PaperVerification.Hyperbolic

open Real Set MeasureTheory Filter Topology
open scoped ENNReal

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [CompactSpace X] [OpensMeasurableSpace X]

theorem log_integral_of_finite_extended_loss
    (f : C(X, ℝ)) (μ : ProbabilityMeasure X) (hf : ∀ x, 0 ≤ f x)
    {M : ℝ} (hM : 1 ≤ M) (hfM : ∀ x, f x ≤ M)
    (hfinite : (∫⁻ x, extendedLogarithmicLoss f M x ∂μ) ≠ ∞) :
    (∀ᵐ x ∂(μ : Measure X), 0 < f x) ∧
      Integrable (fun x => Real.log (f x)) (μ : Measure X) ∧
      (∫ x, Real.log (f x) ∂μ) = Real.log M - (∫⁻ x, extendedLogarithmicLoss f M x ∂μ).toReal := by
  have hae := ae_lt_top (measurable_extendedLogarithmicLoss f M) hfinite
  have hpos : ∀ᵐ x ∂(μ : Measure X), 0 < f x := by
    filter_upwards [hae] with x hx
    by_contra hn
    have hz : f x = 0 := le_antisymm (le_of_not_gt hn) (hf x)
    rw [extendedLogarithmicLoss_of_zero f hM x hz] at hx
    exact lt_irrefl _ hx
  have hI := integrable_toReal_of_lintegral_ne_top
    (measurable_extendedLogarithmicLoss f M).aemeasurable hfinite
  have hrep : (fun x => Real.log M - (extendedLogarithmicLoss f M x).toReal) =ᵐ[(μ : Measure X)]
      (fun x => Real.log (f x)) := by
    filter_upwards [hpos] with x hx
    rw [extendedLogarithmicLoss_of_pos f M x hx,
      ENNReal.toReal_ofReal (sub_nonneg.mpr (Real.log_le_log hx (hfM x)))]
    ring
  refine ⟨hpos, ((integrable_const _).sub hI).congr hrep, ?_⟩
  rw [← integral_congr_ae hrep, integral_sub (integrable_const _) hI,
    integral_toReal (measurable_extendedLogarithmicLoss f M).aemeasurable hae]
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]

/-- Exact agreement with `exp(integral log f)`, including the extended value
`exp(-infinity)=0`.  The upper bound `M` is arbitrary. -/
theorem geometricMean_eq_extended_integral
    (f : C(X, ℝ)) (μ : ProbabilityMeasure X) (hf : ∀ x, 0 ≤ f x)
    {M : ℝ} (hM : 1 ≤ M) (hfM : ∀ x, f x ≤ M) :
    geometricMean f μ =
      if (∫⁻ x, extendedLogarithmicLoss f M x ∂μ) = ∞ then 0
      else Real.exp (Real.log M - (∫⁻ x, extendedLogarithmicLoss f M x ∂μ).toReal) := by
  split_ifs with hinfinite
  · apply le_antisymm _ (geometricMean_nonneg f μ)
    by_contra hn
    have hG : 0 < geometricMean f μ := lt_of_not_ge hn
    have hbound := lintegral_extendedLogarithmicLoss_le 1 zero_lt_one f μ hM hfM hG
    rw [hinfinite] at hbound
    exact (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound) rfl
  · obtain ⟨hpos, hlog, heq⟩ := log_integral_of_finite_extended_loss f μ hf hM hfM hinfinite
    change geometricMoment 1 f μ = _
    rw [geometricMoment_eq_exp_integral_of_integrable_log 1 zero_le_one f μ hpos hlog,
      one_mul, heq]

end PaperVerification.Hyperbolic

#print axioms PaperVerification.Hyperbolic.geometricMean_eq_extended_integral
end
end Source_GeometricMeanExtended
-- END ORIGINAL PaperVerification.GeometricMeanExtended


-- BEGIN ORIGINAL PaperVerification.HyperbolicBoundary
section Source_HyperbolicBoundary

-- original header: module
-- original header: public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
-- original header: public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
-- original header: public import Mathlib.Tactic.FieldSimp
-- original header: public import Mathlib.Tactic.Linarith
-- original header: public import Mathlib.Tactic.Ring
-- original header: @[expose] public section
/-! # Boundary first variation

The algebra is stated with the one-sided condition on the scale derivative.
This is stronger than the stationary identity in Lemma 5.1 and permits compact
minimization over a bounded interval of scales, eliminating the asymptotic
compactness argument of Lemma 5.2.
-/

noncomputable section

namespace PaperVerification.Hyperbolic

open Real Set

def boundaryA (u z t : ℝ) : ℝ := (1 - u) ^ (1 - t) * (1 - u * z) ^ t

def boundaryB (u z t : ℝ) : ℝ := u * z ^ t

def boundaryK (u z : ℝ) : ℝ := u * z * (1 - z) / (1 - u * z)

def boundaryRatio (u z t : ℝ) : ℝ :=
  (1 + boundaryA u z t ^ 2 - boundaryB u z t ^ 2) /
    (2 * boundaryA u z t * (1 - boundaryK u z ^ 2) ^ (t / 2))

def boundaryUVariation (u z t X Y η : ℝ) : ℝ :=
  X * ((t - 1) / (1 - u) - t * z / (1 - u * z)) - Y / u +
    t * η / (u * (1 - u * z))

def boundaryZVariation (u z t X Y η : ℝ) : ℝ :=
  -X * t * u / (1 - u * z) - Y * t / z +
    t * η * (1 - 2 * z + u * z ^ 2) / (z * (1 - z) * (1 - u * z))

def boundaryQNormalized (u z t X Y : ℝ) : ℝ :=
  t * ((X + 1) * (1 - z) / (1 - u * z) - (1 - X + Y) * z +
    Y / (u * z) - (1 - 2 * z + u * z ^ 2) / (1 - 2 * u * z + u * z ^ 2))

def boundaryRNormalized (u z t X Y : ℝ) : ℝ :=
  (1 - X + Y) * ((2 - t) + t * z) - Y * ((2 - t) / u + t / (u * z)) -
    (2 - t / 2) + t / 2 * (1 - 2 * z + u * z ^ 2) / (1 - 2 * u * z + u * z ^ 2)

theorem boundary_cd_pos {u z : ℝ} (hu : u ∈ Ioo 0 1) (hz : z ∈ Ioo 0 1) :
    0 < 1 - 2 * u * z + u * z ^ 2 ∧ 0 < 1 - u * z ^ 2 := by
  have hc : 1 - 2 * u * z + u * z ^ 2 = (1 - u) + u * (1 - z) ^ 2 := by ring
  have hz2 : z ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one z).mpr (by rw [abs_of_pos hz.1]; exact hz.2)
  constructor
  · rw [hc]
    exact add_pos_of_pos_of_nonneg (sub_pos.mpr hu.2) (mul_nonneg hu.1.le (sq_nonneg _))
  · have h := mul_lt_mul_of_pos_left hz2 hu.1
    nlinarith only [h, hu.2]

/-- Elimination directly in the original `R,q` coordinates.  This identity
avoids any need to assume a reparametrization formula for the boundary ratio. -/
theorem boundary_direct_identity (u z t X Y : ℝ)
    (hu : u ≠ 0) (hz : z ≠ 0) (hb : 1 - u * z ≠ 0)
    (hc : 1 - 2 * u * z + u * z ^ 2 ≠ 0) (hd : 1 - u * z ^ 2 ≠ 0)
    (ht : t - 1 ≠ 0) :
    X + (1 - u) / u * Y =
      boundaryRNormalized u z t X Y / (2 * (t - 1)) +
        (1 + z) * (1 - u * z) / (2 * (t - 1) * (1 - u * z ^ 2)) *
          boundaryQNormalized u z t X Y -
        t * u * z ^ 3 * (1 - z) * (1 - u) /
          ((t - 1) * (1 - 2 * u * z + u * z ^ 2) * (1 - u * z ^ 2)) := by
  unfold boundaryRNormalized boundaryQNormalized
  have hc' : 1 - u * z * 2 + u * z ^ 2 ≠ 0 := by
    convert hc using 1 <;> ring
  field_simp [hu, hz, hb, hc, hc', hd, ht] <;>
    ring_nf <;> field_simp [hc'] <;> ring

theorem boundary_direct_inward_negative {u z t X Y : ℝ}
    (hu : u ∈ Ioo 0 1) (hz : z ∈ Ioo 0 1) (ht : 1 < t)
    (hR : boundaryRNormalized u z t X Y ≤ 0)
    (hQ : boundaryQNormalized u z t X Y = 0) :
    X + (1 - u) / u * Y < 0 := by
  have hb : 0 < 1 - u * z := by
    have h := mul_lt_mul_of_pos_left hz.2 hu.1
    nlinarith only [h, hu.2]
  obtain ⟨hc, hd⟩ := boundary_cd_pos hu hz
  rw [boundary_direct_identity u z t X Y hu.1.ne' hz.1.ne' hb.ne' hc.ne' hd.ne'
    (sub_pos.mpr ht).ne', hQ, mul_zero, add_zero]
  have hfirst : boundaryRNormalized u z t X Y / (2 * (t - 1)) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hR (mul_pos (by norm_num) (sub_pos.mpr ht)).le
  have hlast : 0 < t * u * z ^ 3 * (1 - z) * (1 - u) /
      ((t - 1) * (1 - 2 * u * z + u * z ^ 2) * (1 - u * z ^ 2)) :=
    div_pos (mul_pos (mul_pos (mul_pos (mul_pos (zero_lt_one.trans ht) hu.1)
      (pow_pos hz.1 3)) (sub_pos.mpr hz.2)) (sub_pos.mpr hu.2))
      (mul_pos (mul_pos (sub_pos.mpr ht) hc) hd)
  linarith

theorem boundary_parameters_pos {u z : ℝ} (hu : u ∈ Ioo 0 1) (hz : z ∈ Ioo 0 1) :
    0 < 1 - u ∧ 0 < 1 - u * z ∧ 0 < boundaryK u z ∧ boundaryK u z < 1 := by
  have huz : u * z < 1 := (mul_lt_mul_of_pos_left hz.2 hu.1).trans (by simpa using hu.2)
  have ha : 0 < 1 - u := sub_pos.mpr hu.2
  have hb : 0 < 1 - u * z := sub_pos.mpr huz
  refine ⟨ha, hb, div_pos (mul_pos (mul_pos hu.1 hz.1) (sub_pos.mpr hz.2)) hb, ?_⟩
  apply (div_lt_iff₀ hb).mpr
  have hsq := mul_nonneg hu.1.le (sq_nonneg (1 - z))
  nlinarith only [ha, hsq]

theorem boundaryA_pos {u z t : ℝ} (hu : u ∈ Ioo 0 1) (hz : z ∈ Ioo 0 1) :
    0 < boundaryA u z t := by
  obtain ⟨ha, hb, _⟩ := boundary_parameters_pos hu hz
  exact mul_pos (Real.rpow_pos_of_pos ha _) (Real.rpow_pos_of_pos hb _)

theorem boundaryB_mem {u z t : ℝ} (hu : u ∈ Ioo 0 1) (hz : z ∈ Ioo 0 1) (ht : 0 < t) :
    boundaryB u z t ∈ Ioo 0 1 := by
  have hzt : z ^ t < 1 := by
    simpa only [Real.one_rpow] using Real.rpow_lt_rpow hz.1.le hz.2 ht
  exact ⟨mul_pos hu.1 (Real.rpow_pos_of_pos hz.1 _),
    (mul_lt_mul_of_pos_left hzt hu.1).trans (by simpa only [mul_one] using hu.2)⟩

theorem boundaryRatio_pos {u z t : ℝ} (hu : u ∈ Ioo 0 1) (hz : z ∈ Ioo 0 1) (ht : 0 < t) :
    0 < boundaryRatio u z t := by
  have hA := boundaryA_pos (t := t) hu hz
  have hB := boundaryB_mem hu hz ht
  obtain ⟨_, _, hk0, hk1⟩ := boundary_parameters_pos hu hz
  have hB2 : boundaryB u z t ^ 2 < 1 :=
    (sq_lt_one_iff_abs_lt_one _).mpr (by rw [abs_of_pos hB.1]; exact hB.2)
  have hk2 : boundaryK u z ^ 2 < 1 :=
    (sq_lt_one_iff_abs_lt_one _).mpr (by rw [abs_of_pos hk0]; exact hk1)
  exact div_pos (by nlinarith only [hB2, sq_nonneg (boundaryA u z t)])
    (mul_pos (mul_pos (by norm_num) hA) (Real.rpow_pos_of_pos (sub_pos.mpr hk2) _))

/-- Exact elimination identity, retaining both derivative residuals. -/
theorem boundary_inward_identity (u z t X Y η : ℝ)
    (hu : u ≠ 0) (ha : 1 - u ≠ 0) (hb : 1 - u * z ≠ 0)
    (hz : z ≠ 0) (hz1 : 1 - z ≠ 0) (ht : t - 1 ≠ 0) :
    X + (1 - u) / u * Y =
      (1 - u) / (t - 1) * boundaryUVariation u z t X Y η -
        (1 - u) * z / (u * (t - 1)) * boundaryZVariation u z t X Y η -
          t * η * (1 - u) * z / (u * (t - 1) * (1 - z)) := by
  unfold boundaryUVariation boundaryZVariation
  field_simp [hu, ha, hb, hz, hz1, ht] <;> ring

/-- A minimum at the upper allowed scale still has a strictly decreasing
inward direction; equality of the scale derivative is not needed. -/
theorem boundary_inward_negative {u z t X Y η : ℝ}
    (hu : u ∈ Ioo 0 1) (hz : z ∈ Ioo 0 1) (ht : 1 < t) (hη : 0 < η)
    (hU : boundaryUVariation u z t X Y η ≤ 0)
    (hZ : boundaryZVariation u z t X Y η = 0) : X + (1 - u) / u * Y < 0 := by
  obtain ⟨ha, hb, _⟩ := boundary_parameters_pos hu hz
  rw [boundary_inward_identity u z t X Y η hu.1.ne' ha.ne' hb.ne' hz.1.ne'
    (sub_pos.mpr hz.2).ne' (sub_pos.mpr ht).ne', hZ, mul_zero, sub_zero]
  have hfirst : (1 - u) / (t - 1) * boundaryUVariation u z t X Y η ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (div_pos ha (sub_pos.mpr ht)).le hU
  have hlast : 0 < t * η * (1 - u) * z / (u * (t - 1) * (1 - z)) :=
    div_pos (mul_pos (mul_pos (mul_pos (zero_lt_one.trans ht) hη) ha) hz.1)
      (mul_pos (mul_pos hu.1 (sub_pos.mpr ht)) (sub_pos.mpr hz.2))
  linarith

end PaperVerification.Hyperbolic

#print axioms PaperVerification.Hyperbolic.boundary_inward_identity
#print axioms PaperVerification.Hyperbolic.boundary_inward_negative
end
end Source_HyperbolicBoundary
-- END ORIGINAL PaperVerification.HyperbolicBoundary


-- BEGIN ORIGINAL PaperVerification.HyperbolicDividedDifference
section Source_HyperbolicDividedDifference

-- original header: module
-- original header: public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
-- original header: public import Mathlib.Analysis.SpecialFunctions.Sqrt
-- original header: public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
-- original header: public import Mathlib.Tactic.FieldSimp
-- original header: public import Mathlib.Tactic.Linarith
-- original header: public import Mathlib.Tactic.Positivity
-- original header: public import Mathlib.Tactic.Ring
-- original header: @[expose] public section
/-! # The positive divided-difference moment

This is the real one-dimensional version of the Hermite--Genocchi step in
Section 4.2.  The triangular density is integrated separately on its two
linear pieces, so no unproved simplex integration formula is required.
-/

noncomputable section

namespace PaperVerification.Hyperbolic

open Real Set MeasureTheory intervalIntegral

def dividedIntegral (v u : ℝ) (f : ℝ → ℝ) : ℝ :=
  (∫ s in v..u, (s - v) * f s) / ((u - v) * (1 - v)) +
    (∫ s in u..1, (1 - s) * f s) / ((1 - u) * (1 - v))

def powerDividedDifference (v u z : ℝ) : ℝ :=
  ((1 - u ^ z) / (1 - u) - (u ^ z - v ^ z) / (u - v)) / (1 - v)

def powerSecant (v u z : ℝ) : ℝ :=
  ((1 - v) * u ^ z - (1 - u) * v ^ z) / (u - v)

theorem dividedIntegral_congr {v u : ℝ} (hvu : v ≤ u) (hu : u ≤ 1)
    {f g : ℝ → ℝ} (h : ∀ s ∈ Icc v 1, f s = g s) :
    dividedIntegral v u f = dividedIntegral v u g := by
  unfold dividedIntegral
  congr 1
  · congr 1
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hvu]
    exact fun s hs => congrArg ((s - v) * ·) (h s ⟨hs.1, hs.2.trans hu⟩)
  · congr 1
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hu]
    exact fun s hs => congrArg ((1 - s) * ·) (h s ⟨hvu.trans hs.1, hs.2⟩)

theorem dividedIntegral_const_mul (v u c : ℝ) (f : ℝ → ℝ) :
    dividedIntegral v u (fun s => c * f s) = c * dividedIntegral v u f := by
  unfold dividedIntegral
  simp_rw [show ∀ s, (s - v) * (c * f s) = c * ((s - v) * f s) from fun s => by ring,
    show ∀ s, (1 - s) * (c * f s) = c * ((1 - s) * f s) from fun s => by ring]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  ring

theorem dividedIntegral_sub {v u : ℝ} (hv : 0 < v) (hvu : v < u) (hu : u < 1)
    {f g : ℝ → ℝ} (hf : ContinuousOn f (Icc v 1)) (hg : ContinuousOn g (Icc v 1)) :
    dividedIntegral v u (fun s => f s - g s) =
      dividedIntegral v u f - dividedIntegral v u g := by
  have hsub₁ : Icc v u ⊆ Icc v 1 := fun s hs => ⟨hs.1, hs.2.trans hu.le⟩
  have hsub₂ : Icc u 1 ⊆ Icc v 1 := fun s hs => ⟨hvu.le.trans hs.1, hs.2⟩
  have hfl : IntervalIntegrable (fun s => (s - v) * f s) volume v u :=
    ((continuousOn_id.sub continuousOn_const).mul (hf.mono hsub₁)).intervalIntegrable_of_Icc hvu.le
  have hgl : IntervalIntegrable (fun s => (s - v) * g s) volume v u :=
    ((continuousOn_id.sub continuousOn_const).mul (hg.mono hsub₁)).intervalIntegrable_of_Icc hvu.le
  have hfu : IntervalIntegrable (fun s => (1 - s) * f s) volume u 1 :=
    ((continuousOn_const.sub continuousOn_id).mul (hf.mono hsub₂)).intervalIntegrable_of_Icc hu.le
  have hgu : IntervalIntegrable (fun s => (1 - s) * g s) volume u 1 :=
    ((continuousOn_const.sub continuousOn_id).mul (hg.mono hsub₂)).intervalIntegrable_of_Icc hu.le
  unfold dividedIntegral
  simp_rw [mul_sub]
  rw [intervalIntegral.integral_sub hfl hgl, intervalIntegral.integral_sub hfu hgu]
  ring

theorem dividedIntegral_nonneg {v u : ℝ} (hv : 0 < v) (hvu : v < u) (hu : u < 1)
    {f : ℝ → ℝ} (hf : ∀ s ∈ Icc v 1, 0 ≤ f s) : 0 ≤ dividedIntegral v u f := by
  have hv1 := hvu.trans hu
  apply add_nonneg
  · apply div_nonneg _ (mul_pos (sub_pos.mpr hvu) (sub_pos.mpr hv1)).le
    apply intervalIntegral.integral_nonneg hvu.le
    intro s hs
    exact mul_nonneg (sub_nonneg.mpr hs.1) (hf s ⟨hs.1, hs.2.trans hu.le⟩)
  · apply div_nonneg _ (mul_pos (sub_pos.mpr hu) (sub_pos.mpr hv1)).le
    apply intervalIntegral.integral_nonneg hu.le
    intro s hs
    exact mul_nonneg (sub_nonneg.mpr hs.2) (hf s ⟨hvu.le.trans hs.1, hs.2⟩)

theorem continuousOn_rpow_positive_interval {a b z : ℝ} (ha : 0 < a) :
    ContinuousOn (fun s : ℝ => s ^ z) (Icc a b) :=
  continuousOn_id.rpow_const (fun s hs => Or.inl (ha.trans_le hs.1).ne')

theorem integral_linear_rpow_lower {v u z : ℝ} (hv : 0 < v) (hvu : v ≤ u) :
    (∫ s in v..u, (s - v) * (z * (z - 1) * s ^ (z - 2))) =
      (u - v) * z * u ^ (z - 1) - u ^ z + v ^ z := by
  let F : ℝ → ℝ := fun s => (s - v) * z * s ^ (z - 1) - s ^ z
  have hd : ∀ s ∈ uIcc v u,
      HasDerivAt F ((s - v) * (z * (z - 1) * s ^ (z - 2))) s := by
    rw [uIcc_of_le hvu]
    intro s hs
    have hs0 := hv.trans_le hs.1
    convert ((((hasDerivAt_id s).sub_const v).mul_const z).mul
      (Real.hasDerivAt_rpow_const (Or.inl hs0.ne') :
        HasDerivAt (fun s : ℝ => s ^ (z - 1)) ((z - 1) * s ^ ((z - 1) - 1)) s)).sub
      (Real.hasDerivAt_rpow_const (Or.inl hs0.ne') :
        HasDerivAt (fun s : ℝ => s ^ z) (z * s ^ (z - 1)) s) using 1
    · rfl
    · rw [show z - 1 - 1 = z - 2 by ring]
      simp only [Pi.sub_apply, Pi.mul_apply, id_eq]
      ring
  have hc : ContinuousOn (fun s : ℝ => (s - v) * (z * (z - 1) * s ^ (z - 2))) (Icc v u) :=
    (continuousOn_id.sub continuousOn_const).mul
      (continuousOn_const.mul (continuousOn_rpow_positive_interval hv))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable_of_Icc hvu)
  simpa only [F, sub_self, zero_mul, zero_sub, sub_neg_eq_add] using h

theorem integral_linear_rpow_upper {u z : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) :
    (∫ s in u..1, (1 - s) * (z * (z - 1) * s ^ (z - 2))) =
      -(1 - u) * z * u ^ (z - 1) + 1 - u ^ z := by
  let F : ℝ → ℝ := fun s => (1 - s) * z * s ^ (z - 1) + s ^ z
  have hd : ∀ s ∈ uIcc u 1,
      HasDerivAt F ((1 - s) * (z * (z - 1) * s ^ (z - 2))) s := by
    rw [uIcc_of_le hu1]
    intro s hs
    have hs0 := hu0.trans_le hs.1
    convert ((((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s)).mul_const z).mul
      (Real.hasDerivAt_rpow_const (Or.inl hs0.ne') :
        HasDerivAt (fun s : ℝ => s ^ (z - 1)) ((z - 1) * s ^ ((z - 1) - 1)) s)).add
      (Real.hasDerivAt_rpow_const (Or.inl hs0.ne') :
        HasDerivAt (fun s : ℝ => s ^ z) (z * s ^ (z - 1)) s) using 1
    · rfl
    · rw [show z - 1 - 1 = z - 2 by ring]
      simp only [Pi.sub_apply, Pi.mul_apply, id_eq]
      ring
  have hc : ContinuousOn (fun s : ℝ => (1 - s) * (z * (z - 1) * s ^ (z - 2))) (Icc u 1) :=
    (continuousOn_const.sub continuousOn_id).mul
      (continuousOn_const.mul (continuousOn_rpow_positive_interval hu0))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable_of_Icc hu1)
  simp only [F, sub_self, zero_mul, zero_add, Real.one_rpow] at h
  linarith

/-- The precise power instance of the Hermite--Genocchi formula. -/
theorem powerDividedDifference_eq_integral {v u z : ℝ}
    (hv : 0 < v) (hvu : v < u) (hu : u < 1) :
    powerDividedDifference v u z =
      z * (z - 1) * dividedIntegral v u (fun s => s ^ (z - 2)) := by
  rw [← dividedIntegral_const_mul]
  unfold dividedIntegral
  rw [integral_linear_rpow_lower hv hvu.le,
    integral_linear_rpow_upper (hv.trans hvu) hu.le]
  unfold powerDividedDifference
  field_simp [(sub_pos.mpr hvu).ne', (sub_pos.mpr hu).ne', (sub_pos.mpr (hvu.trans hu)).ne'] <;> ring

/-- Reciprocal substitution about the geometric mean of two positive endpoints. -/
theorem integral_reciprocal_geometric {v u g : ℝ}
    (hv : 0 < v) (hvu : v < u) (hg : 0 < g) (hg2 : g ^ 2 = v * u)
    (hvg : v ≤ g) (hgu : g ≤ u) (f : ℝ → ℝ) :
    (∫ s in g..u, f (g ^ 2 / s) * (g ^ 2 / s ^ 2)) = ∫ s in v..g, f s := by
  have hnz : ∀ s ∈ uIcc g u, s ≠ 0 := by
    rw [uIcc_of_le hgu]
    exact fun s hs => (hg.trans_le hs.1).ne'
  have hc : ContinuousOn (fun s : ℝ => g ^ 2 / s) (uIcc g u) :=
    continuousOn_const.div continuousOn_id hnz
  have hd : ∀ s ∈ Ioo (min g u) (max g u),
      HasDerivAt (fun s : ℝ => g ^ 2 / s) (-(g ^ 2 / s ^ 2)) s := by
    intro s hs
    have hs0 : s ≠ 0 := by
      rw [min_eq_left hgu, max_eq_right hgu] at hs
      exact (hg.trans hs.1).ne'
    convert (hasDerivAt_inv hs0).const_mul (g ^ 2) using 1 <;>
      (try funext s) <;> (try simp only [one_div, div_eq_mul_inv]) <;> ring
  have hm : ∀ s ∈ Ioo (min g u) (max g u), -(g ^ 2 / s ^ 2) ≤ 0 :=
    fun s _ => neg_nonpos.mpr (div_nonneg (sq_nonneg g) (sq_nonneg s))
  have h := integral_comp_mul_deriv_of_deriv_nonpos (g := f) hc hd hm
  have hleft : g ^ 2 / g = g := by field_simp [hg.ne']
  have hright : g ^ 2 / u = v := by rw [hg2]; field_simp [(hv.trans hvu).ne']
  have hfun : (fun s : ℝ => (f ∘ fun s => g ^ 2 / s) s * -(g ^ 2 / s ^ 2)) =
      fun s => -(f (g ^ 2 / s) * (g ^ 2 / s ^ 2)) := by
    funext s
    simp only [Function.comp_apply]
    ring
  rw [hfun, intervalIntegral.integral_neg, hleft, hright, intervalIntegral.integral_symm v g] at h
  exact neg_injective h

theorem dividedIntegral_geometric_base_pos {v u g : ℝ}
    (hv : 0 < v) (hvu : v < u) (hu : u < 1)
    (hg : 0 < g) (hg2 : g ^ 2 = v * u) (hvg : v < g) (hgu : g < u) :
    0 < dividedIntegral v u (fun s => (s - g) / s ^ 2) := by
  let f : ℝ → ℝ := fun s => (s - v) * ((s - g) / s ^ 2)
  have hf : ContinuousOn f (Icc v u) := by
    exact (continuousOn_id.sub continuousOn_const).mul
      ((continuousOn_id.sub continuousOn_const).div (continuousOn_id.pow 2)
        (fun s hs => pow_ne_zero 2 (hv.trans_le hs.1).ne'))
  have hfg : IntervalIntegrable f volume v g :=
    (hf.mono (fun s hs => ⟨hs.1, hs.2.trans hgu.le⟩)).intervalIntegrable_of_Icc hvg.le
  have hfu : IntervalIntegrable f volume g u :=
    (hf.mono (fun s hs => ⟨hvg.le.trans hs.1, hs.2⟩)).intervalIntegrable_of_Icc hgu.le
  have hrec : ContinuousOn (fun s => f (g ^ 2 / s) * (g ^ 2 / s ^ 2)) (Icc g u) := by
    have hq : ContinuousOn (fun s : ℝ => g ^ 2 / s) (Icc g u) :=
      continuousOn_const.div continuousOn_id (fun s hs => (hg.trans_le hs.1).ne')
    exact ((hq.sub continuousOn_const).mul
      ((hq.sub continuousOn_const).div (hq.pow 2)
        (fun s hs => pow_ne_zero 2 (div_ne_zero (pow_ne_zero 2 hg.ne') (hg.trans_le hs.1).ne')))).mul
      (continuousOn_const.div (continuousOn_id.pow 2)
        (fun s hs => pow_ne_zero 2 (hg.trans_le hs.1).ne'))
  have hpair : ∀ s ∈ Icc g u,
      f s + f (g ^ 2 / s) * (g ^ 2 / s ^ 2) =
        (1 + v / g) * (s - g) ^ 2 / s ^ 2 := by
    intro s hs
    dsimp [f]
    field_simp [hg.ne', (hg.trans_le hs.1).ne'] <;> ring
  have hlow : 0 ≤ ∫ s in v..u, f s := by
    rw [← integral_add_adjacent_intervals hfg hfu,
      ← integral_reciprocal_geometric hv hvu hg hg2 hvg.le hgu.le f, add_comm,
      ← intervalIntegral.integral_add hfu (hrec.intervalIntegrable_of_Icc hgu.le)]
    apply intervalIntegral.integral_nonneg hgu.le
    intro s hs
    rw [hpair s hs]
    exact div_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) (sq_nonneg s)
  have hu0 := hv.trans hvu
  have hupp : 0 < ∫ s in u..1, (1 - s) * ((s - g) / s ^ 2) := by
    apply intervalIntegral.integral_pos hu
    · exact (continuousOn_const.sub continuousOn_id).mul
        ((continuousOn_id.sub continuousOn_const).div (continuousOn_id.pow 2)
          (fun s hs => pow_ne_zero 2 (hu0.trans_le hs.1).ne'))
    · intro s hs
      exact mul_nonneg (sub_nonneg.mpr hs.2)
        (div_nonneg (sub_nonneg.mpr (hgu.le.trans hs.1.le)) (sq_nonneg s))
    · let m := (u + 1) / 2
      have hm : m ∈ Ioo u 1 := by dsimp [m]; constructor <;> linarith
      exact ⟨m, ⟨hm.1.le, hm.2.le⟩, mul_pos (sub_pos.mpr hm.2)
        (div_pos (sub_pos.mpr (hgu.trans hm.1)) (sq_pos_of_ne_zero (hu0.trans hm.1).ne'))⟩
  exact add_pos_of_nonneg_of_pos
    (div_nonneg hlow (mul_pos (sub_pos.mpr hvu) (sub_pos.mpr (hvu.trans hu))).le)
    (div_pos hupp (mul_pos (sub_pos.mpr hu) (sub_pos.mpr (hvu.trans hu))))

/-- Strict positivity of equation (17), throughout its full exponent range. -/
theorem dividedIntegral_geometric_rpow_pos {v u r : ℝ}
    (hv : 0 < v) (hvu : v < u) (hu : u < 1) (hr : 0 ≤ r) :
    0 < dividedIntegral v u (fun s => (s - Real.sqrt (v * u)) * s ^ (r - 2)) := by
  let g := Real.sqrt (v * u)
  have hu0 := hv.trans hvu
  have hg : 0 < g := Real.sqrt_pos.mpr (mul_pos hv hu0)
  have hg2 : g ^ 2 = v * u := Real.sq_sqrt (mul_nonneg hv.le hu0.le)
  have hvg : v < g := by nlinarith only [hg2, hv, hg, mul_lt_mul_of_pos_left hvu hv]
  have hgu : g < u := by nlinarith only [hg2, hu0, hg, mul_lt_mul_of_pos_right hvu hu0]
  have hbase := dividedIntegral_geometric_base_pos hv hvu hu hg hg2 hvg hgu
  let f : ℝ → ℝ := fun s => (s - g) * s ^ (r - 2)
  let f₀ : ℝ → ℝ := fun s => (s - g) / s ^ 2
  have hf : ContinuousOn f (Icc v 1) :=
    (continuousOn_id.sub continuousOn_const).mul (continuousOn_rpow_positive_interval hv)
  have hf₀ : ContinuousOn f₀ (Icc v 1) :=
    (continuousOn_id.sub continuousOn_const).div (continuousOn_id.pow 2)
      (fun s hs => pow_ne_zero _ (hv.trans_le hs.1).ne')
  have hgf₀ : ContinuousOn (fun s => g ^ r * f₀ s) (Icc v 1) := continuousOn_const.mul hf₀
  have hdiff : 0 ≤ dividedIntegral v u (fun s => f s - g ^ r * f₀ s) := by
    apply dividedIntegral_nonneg hv hvu hu
    intro s hs
    have hs0 := hv.trans_le hs.1
    have hp : 0 ≤ (s - g) * (s ^ r - g ^ r) := by
      rcases le_total g s with h | h
      · exact mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr (Real.rpow_le_rpow hg.le h hr))
      · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h)
          (sub_nonpos.mpr (Real.rpow_le_rpow hs0.le h hr))
    dsimp [f, f₀]
    rw [Real.rpow_sub hs0 r 2, Real.rpow_ofNat]
    have he : (s - g) * (s ^ r / s ^ 2) - g ^ r * ((s - g) / s ^ 2) =
        ((s - g) * (s ^ r - g ^ r)) / s ^ 2 := by ring
    rw [he]
    exact div_nonneg hp (sq_nonneg s)
  rw [dividedIntegral_sub hv hvu hu hf hgf₀,
    dividedIntegral_const_mul] at hdiff
  have hmul : 0 < g ^ r * dividedIntegral v u f₀ :=
    mul_pos (Real.rpow_pos_of_pos hg _) hbase
  change 0 < dividedIntegral v u f
  linarith

theorem powerSecant_sub_one {v u z : ℝ} (hvu : v < u) (hu : u < 1) :
    powerSecant v u z - 1 = -(1 - u) * (1 - v) * powerDividedDifference v u z := by
  unfold powerSecant powerDividedDifference
  field_simp [(sub_pos.mpr hvu).ne', (sub_pos.mpr hu).ne', (sub_pos.mpr (hvu.trans hu)).ne'] <;> ring

/-- The strict algebraic form of equation (16). -/
theorem powerSecant_geometric_inequality {v u r : ℝ}
    (hv : 0 < v) (hvu : v < u) (hu : u < 1) (hr : r ∈ Ioo 0 1) :
    (1 + r) * Real.sqrt (v * u) * (powerSecant v u r - 1) +
      (1 - r) * (powerSecant v u (1 + r) - 1) < 0 := by
  let g := Real.sqrt (v * u)
  let J := dividedIntegral v u (fun s => (s - g) * s ^ (r - 2))
  have hJ : 0 < J := dividedIntegral_geometric_rpow_pos hv hvu hu hr.1.le
  have hmoment : J = dividedIntegral v u (fun s => s ^ (r - 1)) -
      g * dividedIntegral v u (fun s => s ^ (r - 2)) := by
    have hf : ContinuousOn (fun s : ℝ => s ^ (r - 1)) (Icc v 1) := continuousOn_rpow_positive_interval hv
    have hg : ContinuousOn (fun s : ℝ => g * s ^ (r - 2)) (Icc v 1) :=
      continuousOn_const.mul (continuousOn_rpow_positive_interval hv)
    rw [← dividedIntegral_const_mul, ← dividedIntegral_sub hv hvu hu hf hg]
    apply dividedIntegral_congr hvu.le hu.le
    intro s hs
    have hs0 := hv.trans_le hs.1
    have hpow : s ^ (r - 1) = s ^ (r - 2) * s := by
      convert Real.rpow_add_one hs0.ne' (r - 2) using 1 <;> congr 1 <;> ring
    rw [hpow]
    ring
  rw [powerSecant_sub_one hvu hu, powerSecant_sub_one hvu hu,
    powerDividedDifference_eq_integral hv hvu hu,
    powerDividedDifference_eq_integral hv hvu hu]
  rw [show 1 + r - 2 = r - 1 by ring]
  have he : (1 + r) * Real.sqrt (v * u) *
      (-(1 - u) * (1 - v) * (r * (r - 1) * dividedIntegral v u (fun s => s ^ (r - 2)))) +
      (1 - r) * (-(1 - u) * (1 - v) *
        ((1 + r) * (1 + r - 1) * dividedIntegral v u (fun s => s ^ (r - 1)))) =
      -((1 - u) * (1 - v) * r * (1 - r) * (1 + r)) * J := by
    rw [hmoment]
    dsimp [g]
    ring
  rw [he]
  apply mul_neg_of_neg_of_pos _ hJ
  apply neg_neg_of_pos
  exact mul_pos (mul_pos (mul_pos (mul_pos (sub_pos.mpr hu)
    (sub_pos.mpr (hvu.trans hu))) hr.1) (sub_pos.mpr hr.2)) (by linarith [hr.1])

end PaperVerification.Hyperbolic

#print axioms PaperVerification.Hyperbolic.powerDividedDifference_eq_integral
#print axioms PaperVerification.Hyperbolic.dividedIntegral_geometric_rpow_pos
end
end Source_HyperbolicDividedDifference
-- END ORIGINAL PaperVerification.HyperbolicDividedDifference


-- BEGIN ORIGINAL PaperVerification.HyperbolicLocalization
section Source_HyperbolicLocalization

-- original header: module
-- original header: public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
-- original header: public import Mathlib.Analysis.Convex.Deriv
-- original header: public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
-- original header: public import Mathlib.Tactic.FieldSimp
-- original header: public import Mathlib.Tactic.Ring
-- original header: public import Mathlib.Tactic.Linarith
-- original header: @[expose] public section
/-! # Calculus underlying the two-support localization

This file develops the exact second-derivative and strict-convexity calculations
in equation (13) of the cold-spots paper. These facts do not assume the
hyperbolic inequality, a finite-support reduction, or a Gaussian minimum.
-/

noncomputable section

namespace PaperVerification.Hyperbolic

open Real Set

/-- The hyperbolic cotangent, used only away from zero. -/
def coth (p : ℝ) : ℝ := Real.cosh p / Real.sinh p

/-- The derivative of tanh in a form convenient for exact polynomial certificates. -/
theorem hasDerivAt_tanh (p : ℝ) :
    HasDerivAt Real.tanh (1 - (Real.tanh p) ^ 2) p := by
  have hc : Real.cosh p ≠ 0 := (Real.cosh_pos p).ne'
  convert (Real.hasDerivAt_sinh p).div (Real.hasDerivAt_cosh p) hc using 1 <;>
    (try funext t) <;> (try simp only [Real.tanh_eq_sinh_div_cosh, Pi.div_apply]) <;> field_simp [hc] <;>
    nlinarith only [Real.cosh_sq_sub_sinh_sq p]

theorem hasDerivAt_coth (p : ℝ) (hp : p ≠ 0) :
    HasDerivAt coth (1 - coth p ^ 2) p := by
  have hs : Real.sinh p ≠ 0 := Real.sinh_ne_zero.mpr hp
  unfold coth
  convert (Real.hasDerivAt_cosh p).div (Real.hasDerivAt_sinh p) hs using 1 <;>
    field_simp [hs] <;> nlinarith only [Real.cosh_sq_sub_sinh_sq p]

/-- First quotient in equation (13). -/
def coshQuotient (R p : ℝ) : ℝ := (Real.cosh (2 * p - R)) ^ 2 / (Real.cosh p) ^ 2

/-- Third quotient in equation (13); its domain is p>0. -/
def sinhQuotient (R p : ℝ) : ℝ := (Real.cosh (2 * p - R)) ^ 2 / (Real.sinh p) ^ 2

private theorem hasDerivAt_centered (R p : ℝ) : HasDerivAt (fun t : ℝ => 2 * t - R) 2 p := by
  simpa using ((hasDerivAt_id p).const_mul 2).sub_const R

theorem hasDerivAt_coshQuotient (R p : ℝ) :
    HasDerivAt (coshQuotient R)
      (coshQuotient R p * (4 * Real.tanh (2 * p - R) - 2 * Real.tanh p)) p := by
  have hc : Real.cosh p ≠ 0 := (Real.cosh_pos p).ne'
  have hC : Real.cosh (2 * p - R) ≠ 0 := (Real.cosh_pos _).ne'
  convert (((hasDerivAt_centered R p).cosh).pow 2).div
    ((Real.hasDerivAt_cosh p).pow 2) (pow_ne_zero 2 hc) using 1 <;>
    (try funext t) <;>
    (try simp only [coshQuotient, Real.tanh_eq_sinh_div_cosh, Pi.pow_apply,
      Pi.mul_apply, Pi.sub_apply, Pi.div_apply, Function.comp_apply, Nat.reduceSub, Nat.cast_ofNat, pow_one]) <;>
    field_simp [hc, hC] <;> ring

theorem hasDerivAt_coshQuotient_derivative (R p : ℝ) :
    HasDerivAt
      (fun t => coshQuotient R t * (4 * Real.tanh (2 * t - R) - 2 * Real.tanh t))
      (coshQuotient R p * (6 + 8 * Real.tanh (2 * p - R) ^ 2 +
        6 * Real.tanh p ^ 2 - 16 * Real.tanh (2 * p - R) * Real.tanh p)) p := by
  have hT := (hasDerivAt_tanh (2 * p - R)).comp p (hasDerivAt_centered R p)
  have ht := hasDerivAt_tanh p
  convert (hasDerivAt_coshQuotient R p).mul
    ((hT.const_mul 4).sub (ht.const_mul 2)) using 1 <;>
    (try funext t) <;>
    (try simp only [Function.comp_apply, Pi.mul_apply, Pi.sub_apply]) <;> ring

theorem deriv2_coshQuotient (R p : ℝ) :
    deriv (deriv (coshQuotient R)) p =
      coshQuotient R p * (6 + 8 * Real.tanh (2 * p - R) ^ 2 +
        6 * Real.tanh p ^ 2 - 16 * Real.tanh (2 * p - R) * Real.tanh p) := by
  have hd : deriv (coshQuotient R) =
      fun t => coshQuotient R t * (4 * Real.tanh (2 * t - R) - 2 * Real.tanh t) :=
    funext fun t => (hasDerivAt_coshQuotient R t).deriv
  rw [hd]
  exact (hasDerivAt_coshQuotient_derivative R p).deriv

theorem coshQuotient_secondFactor_pos (R p : ℝ) :
    0 < 6 + 8 * Real.tanh (2 * p - R) ^ 2 + 6 * Real.tanh p ^ 2 -
      16 * Real.tanh (2 * p - R) * Real.tanh p := by
  nlinarith only [sq_nonneg (Real.tanh (2 * p - R) - Real.tanh p), Real.tanh_sq_lt_one p]

theorem continuous_coshQuotient (R : ℝ) : Continuous (coshQuotient R) := by
  unfold coshQuotient
  exact ((Real.continuous_cosh.comp ((continuous_const.mul continuous_id).sub continuous_const)).pow 2).div
    (Real.continuous_cosh.pow 2) (fun p => pow_ne_zero 2 (Real.cosh_pos p).ne')

/-- Strict convexity is global; no sign restriction on R is needed for this quotient. -/
theorem strictConvexOn_coshQuotient (R : ℝ) : StrictConvexOn ℝ Set.univ (coshQuotient R) := by
  apply strictConvexOn_of_deriv2_pos' convex_univ (continuous_coshQuotient R).continuousOn
  intro p hp
  change 0 < deriv (deriv (coshQuotient R)) p
  rw [deriv2_coshQuotient]
  apply mul_pos
  · exact div_pos (pow_pos (Real.cosh_pos _) 2) (pow_pos (Real.cosh_pos _) 2)
  · exact coshQuotient_secondFactor_pos R p

theorem hasDerivAt_sinhQuotient (R p : ℝ) (hp : p ≠ 0) :
    HasDerivAt (sinhQuotient R)
      (sinhQuotient R p * (4 * Real.tanh (2 * p - R) - 2 * coth p)) p := by
  have hs : Real.sinh p ≠ 0 := Real.sinh_ne_zero.mpr hp
  have hC : Real.cosh (2 * p - R) ≠ 0 := (Real.cosh_pos _).ne'
  convert (((hasDerivAt_centered R p).cosh).pow 2).div
    ((Real.hasDerivAt_sinh p).pow 2) (pow_ne_zero 2 hs) using 1 <;>
    (try funext t) <;>
    (try simp only [sinhQuotient, coth, Real.tanh_eq_sinh_div_cosh, Pi.pow_apply,
      Pi.mul_apply, Pi.sub_apply, Pi.div_apply, Function.comp_apply, Nat.reduceSub, Nat.cast_ofNat, pow_one]) <;>
    field_simp [hs, hC] <;> ring

theorem hasDerivAt_sinhQuotient_derivative (R p : ℝ) (hp : p ≠ 0) :
    HasDerivAt
      (fun t => sinhQuotient R t * (4 * Real.tanh (2 * t - R) - 2 * coth t))
      (sinhQuotient R p * (6 + 8 * Real.tanh (2 * p - R) ^ 2 +
        6 * coth p ^ 2 - 16 * Real.tanh (2 * p - R) * coth p)) p := by
  have hT := (hasDerivAt_tanh (2 * p - R)).comp p (hasDerivAt_centered R p)
  have ht := hasDerivAt_coth p hp
  convert (hasDerivAt_sinhQuotient R p hp).mul
    ((hT.const_mul 4).sub (ht.const_mul 2)) using 1 <;>
    (try funext t) <;>
    (try simp only [Function.comp_apply, Pi.mul_apply, Pi.sub_apply]) <;> ring

theorem deriv2_sinhQuotient (R p : ℝ) (hp : 0 < p) :
    deriv (deriv (sinhQuotient R)) p =
      sinhQuotient R p * (6 + 8 * Real.tanh (2 * p - R) ^ 2 +
        6 * coth p ^ 2 - 16 * Real.tanh (2 * p - R) * coth p) := by
  have hd : (Set.Ioi 0).EqOn (deriv (sinhQuotient R))
      (fun t => sinhQuotient R t * (4 * Real.tanh (2 * t - R) - 2 * coth t)) :=
    fun t ht => (hasDerivAt_sinhQuotient R t (ne_of_gt ht)).deriv
  exact (hd.deriv isOpen_Ioi hp).trans (hasDerivAt_sinhQuotient_derivative R p hp.ne').deriv

theorem one_le_coth {p : ℝ} (hp : 0 < p) : 1 ≤ coth p := by
  unfold coth
  apply (le_div_iff₀ (Real.sinh_pos_iff.mpr hp)).mpr
  simpa only [one_mul] using (Real.sinh_lt_cosh (x := p)).le

theorem sinhQuotient_secondFactor_pos (R p : ℝ) (hp : 0 < p) :
    0 < 6 + 8 * Real.tanh (2 * p - R) ^ 2 + 6 * coth p ^ 2 -
      16 * Real.tanh (2 * p - R) * coth p := by
  have hu := one_le_coth hp
  have hT := (Real.tanh_lt_one (2 * p - R)).le
  have hprod : 0 ≤ (1 - Real.tanh (2 * p - R)) *
      (2 * coth p - Real.tanh (2 * p - R) - 1) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith only [hprod, sq_nonneg (coth p - 4 / 3)]

theorem continuousOn_sinhQuotient (R : ℝ) : ContinuousOn (sinhQuotient R) (Set.Ioi 0) := by
  unfold sinhQuotient
  apply (((Real.continuous_cosh.comp ((continuous_const.mul continuous_id).sub continuous_const)).pow 2).continuousOn).div
    (Real.continuous_sinh.pow 2).continuousOn
  intro p hp
  exact pow_ne_zero 2 (Real.sinh_ne_zero.mpr (ne_of_gt hp))

/-- The second type of quotient is strictly convex on the entire positive half-line. -/
theorem strictConvexOn_sinhQuotient (R : ℝ) :
    StrictConvexOn ℝ (Set.Ioi 0) (sinhQuotient R) := by
  apply strictConvexOn_of_deriv2_pos' (convex_Ioi 0) (continuousOn_sinhQuotient R)
  intro p hp
  change 0 < deriv (deriv (sinhQuotient R)) p
  rw [deriv2_sinhQuotient R p hp]
  apply mul_pos
  · exact div_pos (pow_pos (Real.cosh_pos _) 2) (pow_pos (Real.sinh_pos_iff.mpr hp) 2)
  · exact sinhQuotient_secondFactor_pos R p hp

/-- Positive scalar multiplication preserves strict convexity. -/
theorem strictConvexOn_mul_pos {s : Set ℝ} {f : ℝ → ℝ}
    (hf : StrictConvexOn ℝ s f) {c : ℝ} (hc : 0 < c) :
    StrictConvexOn ℝ s (fun x => c * f x) := by
  refine ⟨hf.1, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  simp only [smul_eq_mul]
  calc
    c * f (a * x + b * y) < c * (a * f x + b * f y) := by
      exact mul_lt_mul_of_pos_left (by simpa only [smul_eq_mul] using hf.2 hx hy hxy ha hb hab) hc
    _ = a * (c * f x) + b * (c * f y) := by ring

/-- Nonnegative scalar multiplication preserves convexity, including a vanishing term. -/
theorem convexOn_mul_nonneg {s : Set ℝ} {f : ℝ → ℝ}
    (hf : ConvexOn ℝ s f) {c : ℝ} (hc : 0 ≤ c) :
    ConvexOn ℝ s (fun x => c * f x) := by
  refine ⟨hf.1, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  calc
    c * f (a * x + b * y) ≤ c * (a * f x + b * f y) := by
      exact mul_le_mul_of_nonneg_left (by simpa only [smul_eq_mul] using hf.2 hx hy ha hb hab) hc
    _ = a * (c * f x) + b * (c * f y) := by ring

/-- Reflection preserves strict convexity on an interval symmetric about R/2. -/
theorem strictConvexOn_reflection {R : ℝ} {f : ℝ → ℝ}
    (hf : StrictConvexOn ℝ (Ioo 0 R) f) :
    StrictConvexOn ℝ (Ioo 0 R) (fun p => f (R - p)) := by
  refine ⟨convex_Ioo 0 R, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hRx : R - x ∈ Ioo 0 R := by constructor <;> linarith [hx.1, hx.2]
  have hRy : R - y ∈ Ioo 0 R := by constructor <;> linarith [hy.1, hy.2]
  have hRxy : R - x ≠ R - y := by intro h; apply hxy; linarith
  have hs := hf.2 hRx hRy hRxy ha hb hab
  simp only [smul_eq_mul] at hs ⊢
  have harg : a * (R - x) + b * (R - y) = R - (a * x + b * y) := by
    calc
      _ = (a + b) * R - (a * x + b * y) := by ring
      _ = R - (a * x + b * y) := by rw [hab, one_mul]
  rwa [harg] at hs

/-- Right-hand side of equation (13), using reflection to keep all four quotient
functions in their already established strictly convex form. -/
def curvatureModel (R A C B D F p : ℝ) : ℝ :=
  (A * coshQuotient R p + C * coshQuotient R (R - p) +
    B * sinhQuotient R p + D * sinhQuotient R (R - p)) / F - 1

theorem strictConvexOn_curvatureModel
    (R A C B D F : ℝ) (hA : 0 < A) (hC : 0 < C)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hF : 0 < F) :
    StrictConvexOn ℝ (Ioo 0 R) (curvatureModel R A C B D F) := by
  have hc : StrictConvexOn ℝ (Ioo 0 R) (coshQuotient R) :=
    (strictConvexOn_coshQuotient R).subset (subset_univ _) (convex_Ioo 0 R)
  have hs : StrictConvexOn ℝ (Ioo 0 R) (sinhQuotient R) :=
    (strictConvexOn_sinhQuotient R).subset (fun _ hp => hp.1) (convex_Ioo 0 R)
  have hsum := ((strictConvexOn_mul_pos hc hA).add
    (strictConvexOn_mul_pos (strictConvexOn_reflection hc) hC)).add_convexOn
    ((convexOn_mul_nonneg hs.convexOn hB).add
      (convexOn_mul_nonneg (strictConvexOn_reflection hs).convexOn hD))
  have hscaled := (strictConvexOn_mul_pos hsum (one_div_pos.mpr hF)).add_const (-1)
  apply hscaled.congr
  intro p hp
  simp only [Pi.add_apply, curvatureModel]
  ring

theorem coshQuotient_reflected (R p : ℝ) :
    coshQuotient R (R - p) = Real.cosh (2 * p - R) ^ 2 / Real.cosh (R - p) ^ 2 := by
  unfold coshQuotient
  have he : 2 * (R - p) - R = -(2 * p - R) := by ring
  rw [he, Real.cosh_neg]

theorem sinhQuotient_reflected (R p : ℝ) :
    sinhQuotient R (R - p) = Real.cosh (2 * p - R) ^ 2 / Real.sinh (R - p) ^ 2 := by
  unfold sinhQuotient
  have he : 2 * (R - p) - R = -(2 * p - R) := by ring
  rw [he, Real.cosh_neg]

/-- The real first-variation potential on the open interval. At an endpoint,
a positive coefficient of minus log sinh is interpreted through its positive
infinite limit; no endpoint value is silently assigned by this definition. -/
def variationPotential (R A C B D F p : ℝ) : ℝ :=
  4 / F * (A * Real.log (Real.cosh p) + C * Real.log (Real.cosh (R - p)) -
    B * Real.log (Real.sinh p) - D * Real.log (Real.sinh (R - p))) -
    Real.log (Real.cosh (2 * p - R))

def variationDerivative (R A C B D F p : ℝ) : ℝ :=
  4 / F * (A * Real.tanh p - C * Real.tanh (R - p) -
    B * coth p + D * coth (R - p)) - 2 * Real.tanh (2 * p - R)

def variationSecondDerivative (R A C B D F p : ℝ) : ℝ :=
  4 / F * (A / Real.cosh p ^ 2 + C / Real.cosh (R - p) ^ 2 +
    B / Real.sinh p ^ 2 + D / Real.sinh (R - p) ^ 2) -
    4 / Real.cosh (2 * p - R) ^ 2

theorem hasDerivAt_log_cosh (p : ℝ) :
    HasDerivAt (fun t => Real.log (Real.cosh t)) (Real.tanh p) p := by
  simpa only [Real.tanh_eq_sinh_div_cosh] using
    (Real.hasDerivAt_cosh p).log (Real.cosh_pos p).ne'

theorem hasDerivAt_log_sinh (p : ℝ) (hp : p ≠ 0) :
    HasDerivAt (fun t => Real.log (Real.sinh t)) (coth p) p := by
  simpa only [coth] using (Real.hasDerivAt_sinh p).log (Real.sinh_ne_zero.mpr hp)

private theorem hasDerivAt_reflection (R p : ℝ) :
    HasDerivAt (fun t : ℝ => R - t) (-1) p := by
  simpa using (hasDerivAt_id p).const_sub R

theorem hasDerivAt_variationPotential (R A C B D F p : ℝ) (hp : p ∈ Ioo 0 R) :
    HasDerivAt (variationPotential R A C B D F)
      (variationDerivative R A C B D F p) p := by
  have ha := (hasDerivAt_log_cosh p).const_mul A
  have hc := ((hasDerivAt_log_cosh (R - p)).comp p (hasDerivAt_reflection R p)).const_mul C
  have hb := (hasDerivAt_log_sinh p hp.1.ne').const_mul B
  have hd := ((hasDerivAt_log_sinh (R - p) (sub_pos.mpr hp.2).ne').comp p
    (hasDerivAt_reflection R p)).const_mul D
  have hv := (hasDerivAt_log_cosh (2 * p - R)).comp p (hasDerivAt_centered R p)
  convert ((((ha.add hc).sub hb).sub hd).const_mul (4 / F)).sub hv using 1 <;>
    (try funext t) <;>
    (try simp only [variationPotential, variationDerivative, Function.comp_apply,
      Pi.add_apply, Pi.sub_apply, Pi.mul_apply]) <;> ring

theorem one_sub_tanh_sq (p : ℝ) : 1 - Real.tanh p ^ 2 = 1 / Real.cosh p ^ 2 := by
  rw [Real.tanh_eq_sinh_div_cosh]
  have hc := (Real.cosh_pos p).ne'
  field_simp [hc]
  nlinarith only [Real.cosh_sq_sub_sinh_sq p]

theorem one_sub_coth_sq (p : ℝ) (hp : p ≠ 0) :
    1 - coth p ^ 2 = -(1 / Real.sinh p ^ 2) := by
  unfold coth
  have hs := Real.sinh_ne_zero.mpr hp
  field_simp [hs]
  nlinarith only [Real.cosh_sq_sub_sinh_sq p]

theorem hasDerivAt_variationDerivative (R A C B D F p : ℝ) (hp : p ∈ Ioo 0 R) :
    HasDerivAt (variationDerivative R A C B D F)
      (variationSecondDerivative R A C B D F p) p := by
  have ha := (hasDerivAt_tanh p).const_mul A
  have hc := ((hasDerivAt_tanh (R - p)).comp p (hasDerivAt_reflection R p)).const_mul C
  have hb := (hasDerivAt_coth p hp.1.ne').const_mul B
  have hd := ((hasDerivAt_coth (R - p) (sub_pos.mpr hp.2).ne').comp p
    (hasDerivAt_reflection R p)).const_mul D
  have hv := ((hasDerivAt_tanh (2 * p - R)).comp p (hasDerivAt_centered R p)).const_mul 2
  convert ((((ha.sub hc).sub hb).add hd).const_mul (4 / F)).sub hv using 1 <;>
    (try funext t) <;>
    (try simp only [variationDerivative, variationSecondDerivative, Function.comp_apply,
      Pi.add_apply, Pi.sub_apply, Pi.mul_apply, one_sub_tanh_sq,
      one_sub_coth_sq p hp.1.ne', one_sub_coth_sq (R - p) (sub_pos.mpr hp.2).ne']) <;> ring

theorem deriv2_variationPotential (R A C B D F p : ℝ) (hp : p ∈ Ioo 0 R) :
    deriv (deriv (variationPotential R A C B D F)) p =
      variationSecondDerivative R A C B D F p := by
  have hd : (Ioo 0 R).EqOn (deriv (variationPotential R A C B D F))
      (variationDerivative R A C B D F) :=
    fun t ht => (hasDerivAt_variationPotential R A C B D F t ht).deriv
  exact (hd.deriv isOpen_Ioo hp).trans
    (hasDerivAt_variationDerivative R A C B D F p hp).deriv

/-- Equation (13), with the positive normalization made explicit. -/
theorem variationSecondDerivative_eq_curvatureModel
    (R A C B D F p : ℝ) (hF : F ≠ 0) (hp : p ∈ Ioo 0 R) :
    variationSecondDerivative R A C B D F p =
      (4 / Real.cosh (2 * p - R) ^ 2) * curvatureModel R A C B D F p := by
  have hcp := (Real.cosh_pos p).ne'
  have hcr := (Real.cosh_pos (R - p)).ne'
  have hcv := (Real.cosh_pos (2 * p - R)).ne'
  have hsp := Real.sinh_ne_zero.mpr hp.1.ne'
  have hsr := Real.sinh_ne_zero.mpr (sub_pos.mpr hp.2).ne'
  unfold curvatureModel variationSecondDerivative
  rw [coshQuotient_reflected R p, sinhQuotient_reflected R p]
  unfold coshQuotient sinhQuotient
  field_simp [hF, hcp, hcr, hcv, hsp, hsr] <;> ring

end PaperVerification.Hyperbolic

#print axioms PaperVerification.Hyperbolic.strictConvexOn_coshQuotient
#print axioms PaperVerification.Hyperbolic.strictConvexOn_sinhQuotient

#print axioms PaperVerification.Hyperbolic.strictConvexOn_curvatureModel
#print axioms PaperVerification.Hyperbolic.variationSecondDerivative_eq_curvatureModel
end
end Source_HyperbolicLocalization
-- END ORIGINAL PaperVerification.HyperbolicLocalization


-- BEGIN ORIGINAL PaperVerification.HyperbolicJensen
section Source_HyperbolicJensen

-- original header: module
-- original header: public import PaperVerification.HyperbolicLocalization
-- original header: public import Mathlib.Analysis.SpecialFunctions.Sqrt
-- original header: public import Mathlib.Analysis.Convex.Deriv
-- original header: public import Mathlib.Tactic.LinearCombination
-- original header: @[expose] public section
/-! # The large-scale Jensen bound

The two curvature facts used in Section 5.3 are proved on the full closed
half-line, including zero.  The final strict inequality covers all distinct
unaligned two-point supports and every nontrivial probability weight.
-/

noncomputable section

namespace PaperVerification.Hyperbolic

open Real Set

theorem sinh_cosh_sub_self_pos {v : ℝ} (hv : 0 < v) :
    0 < Real.sinh v * Real.cosh v - v := by
  let f : ℝ → ℝ := fun t => Real.sinh t * Real.cosh t - t
  have hd (t : ℝ) : HasDerivAt f (2 * Real.sinh t ^ 2) t := by
    convert ((Real.hasDerivAt_sinh t).mul (Real.hasDerivAt_cosh t)).sub (hasDerivAt_id t) using 1
    · rfl
    · nlinarith only [Real.cosh_sq_sub_sinh_sq t]
  have hm : StrictMonoOn f (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
      (((Real.continuous_sinh.mul Real.continuous_cosh).sub continuous_id).continuousOn)
    intro t ht
    have ht0 : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
    change 0 < deriv f t
    rw [(hd t).deriv]
    exact mul_pos (by norm_num) (sq_pos_of_ne_zero (Real.sinh_pos_iff.mpr ht0).ne')
  have h := hm (show (0 : ℝ) ∈ Ici 0 from le_rfl) hv.le hv
  simpa only [f, Real.sinh_zero, Real.cosh_zero, zero_mul, sub_zero] using h

theorem self_cosh_sub_sinh_pos {v : ℝ} (hv : 0 < v) :
    0 < v * Real.cosh v - Real.sinh v := by
  let f : ℝ → ℝ := fun t => t * Real.cosh t - Real.sinh t
  have hd (t : ℝ) : HasDerivAt f (t * Real.sinh t) t := by
    convert ((hasDerivAt_id t).mul (Real.hasDerivAt_cosh t)).sub (Real.hasDerivAt_sinh t) using 1
    · rfl
    · simp only [id_eq]
      ring
  have hm : StrictMonoOn f (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
      (((continuous_id.mul Real.continuous_cosh).sub Real.continuous_sinh).continuousOn)
    intro t ht
    have ht0 : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
    change 0 < deriv f t
    rw [(hd t).deriv]
    exact mul_pos ht0 (Real.sinh_pos_iff.mpr ht0)
  have h := hm (show (0 : ℝ) ∈ Ici 0 from le_rfl) hv.le hv
  simpa only [f, Real.sinh_zero, Real.cosh_zero, zero_mul, sub_zero] using h

theorem strictMonoOn_self_coth : StrictMonoOn (fun t : ℝ => t * coth t) (Ioi 0) := by
  have hd (t : ℝ) (ht : 0 < t) : HasDerivAt (fun t : ℝ => t * coth t)
      ((Real.sinh t * Real.cosh t - t) / Real.sinh t ^ 2) t := by
    have hs := (Real.sinh_pos_iff.mpr ht).ne'
    convert (hasDerivAt_id t).mul (hasDerivAt_coth t ht.ne') using 1 <;>
      (try funext s) <;> (try simp only [coth, id_eq, Pi.mul_apply]) <;>
      field_simp [hs] <;> linear_combination t * Real.cosh_sq_sub_sinh_sq t
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
  intro t ht
  have ht0 : 0 < t := interior_subset ht
  rw [(hd t ht0).deriv]
  exact div_pos (sinh_cosh_sub_self_pos ht0)
    (sq_pos_of_ne_zero (Real.sinh_pos_iff.mpr ht0).ne')

theorem strictAntiOn_sinh_scale_ratio {r : ℝ} (hr : r ∈ Ioo 0 1) :
    StrictAntiOn (fun t : ℝ => Real.sinh (r * t) / Real.sinh t) (Ioi 0) := by
  have hd (t : ℝ) (ht : 0 < t) :
      HasDerivAt (fun t : ℝ => Real.sinh (r * t) / Real.sinh t)
        (Real.sinh (r * t) / Real.sinh t * (r * coth (r * t) - coth t)) t := by
    have hs := (Real.sinh_pos_iff.mpr ht).ne'
    have hrs := (Real.sinh_pos_iff.mpr (mul_pos hr.1 ht)).ne'
    convert (((hasDerivAt_id t).const_mul r).sinh).div (Real.hasDerivAt_sinh t) hs using 1 <;>
      (try funext s) <;> (try simp only [coth, id_eq, Pi.div_apply, Function.comp_apply]) <;>
      field_simp [hs, hrs] <;> ring
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
  intro t ht
  have ht0 : 0 < t := interior_subset ht
  have hrt0 := mul_pos hr.1 ht0
  have hrt : r * t < t := by simpa only [one_mul] using mul_lt_mul_of_pos_right hr.2 ht0
  have hc := strictMonoOn_self_coth hrt0 ht0 hrt
  have hcot : r * coth (r * t) - coth t < 0 := by
    have hmul : t * (r * coth (r * t) - coth t) < 0 := by
      nlinarith only [hc]
    nlinarith only [hmul, ht0]
  rw [(hd t ht0).deriv]
  exact mul_neg_of_pos_of_neg
    (div_pos (Real.sinh_pos_iff.mpr hrt0) (Real.sinh_pos_iff.mpr ht0)) hcot

def coshSqrt (x : ℝ) : ℝ := Real.cosh (Real.sqrt x)

def logCoshSqrt (x : ℝ) : ℝ := Real.log (Real.cosh (Real.sqrt x))

theorem hasDerivAt_coshSqrt {x : ℝ} (hx : 0 < x) :
    HasDerivAt coshSqrt (Real.sinh (Real.sqrt x) / (2 * Real.sqrt x)) x := by
  convert (Real.hasDerivAt_sqrt hx.ne').cosh using 1 <;>
    (try funext t) <;> (try simp only [coshSqrt, Function.comp_apply]) <;> ring

theorem hasDerivAt_coshSqrt_derivative {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t => Real.sinh (Real.sqrt t) / (2 * Real.sqrt t))
      ((Real.sqrt x * Real.cosh (Real.sqrt x) - Real.sinh (Real.sqrt x)) /
        (4 * Real.sqrt x ^ 3)) x := by
  have hs := (Real.sqrt_pos.mpr hx).ne'
  convert ((Real.hasDerivAt_sqrt hx.ne').sinh).div
    ((Real.hasDerivAt_sqrt hx.ne').const_mul 2) (mul_ne_zero (by norm_num) hs) using 1 <;>
    (try funext t) <;> (try simp only [Pi.div_apply, Pi.mul_apply, Function.comp_apply]) <;>
    field_simp [hs] <;> ring

theorem deriv2_coshSqrt {x : ℝ} (hx : 0 < x) :
    deriv (deriv coshSqrt) x =
      (Real.sqrt x * Real.cosh (Real.sqrt x) - Real.sinh (Real.sqrt x)) /
        (4 * Real.sqrt x ^ 3) := by
  have hd : (Ioi 0).EqOn (deriv coshSqrt)
      (fun t => Real.sinh (Real.sqrt t) / (2 * Real.sqrt t)) :=
    fun t ht => (hasDerivAt_coshSqrt ht).deriv
  exact (hd.deriv isOpen_Ioi hx).trans (hasDerivAt_coshSqrt_derivative hx).deriv

theorem strictConvexOn_coshSqrt : StrictConvexOn ℝ (Ici 0) coshSqrt := by
  apply strictConvexOn_of_deriv2_pos (convex_Ici 0)
    (Real.continuous_cosh.comp Real.continuous_sqrt).continuousOn
  intro x hx
  have hx0 : 0 < x := by simpa only [interior_Ici, mem_Ioi] using hx
  change 0 < deriv (deriv coshSqrt) x
  rw [deriv2_coshSqrt hx0]
  exact div_pos (self_cosh_sub_sinh_pos (Real.sqrt_pos.mpr hx0))
    (mul_pos (by norm_num) (pow_pos (Real.sqrt_pos.mpr hx0) 3))

theorem hasDerivAt_logCoshSqrt {x : ℝ} (hx : 0 < x) :
    HasDerivAt logCoshSqrt (Real.tanh (Real.sqrt x) / (2 * Real.sqrt x)) x := by
  have hs := (Real.sqrt_pos.mpr hx).ne'
  have hc := (Real.cosh_pos (Real.sqrt x)).ne'
  convert (hasDerivAt_coshSqrt hx).log hc using 1 <;>
    (try funext t) <;>
    (try simp only [logCoshSqrt, coshSqrt, Real.tanh_eq_sinh_div_cosh, Function.comp_apply]) <;>
    field_simp [hs, hc] <;> ring

theorem hasDerivAt_logCoshSqrt_derivative {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t => Real.tanh (Real.sqrt t) / (2 * Real.sqrt t))
      ((Real.sqrt x - Real.sinh (Real.sqrt x) * Real.cosh (Real.sqrt x)) /
        (4 * Real.sqrt x ^ 3 * Real.cosh (Real.sqrt x) ^ 2)) x := by
  have hs := (Real.sqrt_pos.mpr hx).ne'
  have hc := (Real.cosh_pos (Real.sqrt x)).ne'
  have ht := (hasDerivAt_tanh (Real.sqrt x)).comp x (Real.hasDerivAt_sqrt hx.ne')
  simp only [one_sub_tanh_sq] at ht
  convert ht.div ((Real.hasDerivAt_sqrt hx.ne').const_mul 2)
    (mul_ne_zero (by norm_num) hs) using 1 <;>
    (try funext t) <;>
    (try simp only [Pi.div_apply, Pi.mul_apply, Function.comp_apply, Real.tanh_eq_sinh_div_cosh]) <;>
    field_simp [hs, hc] <;> ring

theorem deriv2_logCoshSqrt {x : ℝ} (hx : 0 < x) :
    deriv (deriv logCoshSqrt) x =
      (Real.sqrt x - Real.sinh (Real.sqrt x) * Real.cosh (Real.sqrt x)) /
        (4 * Real.sqrt x ^ 3 * Real.cosh (Real.sqrt x) ^ 2) := by
  have hd : (Ioi 0).EqOn (deriv logCoshSqrt)
      (fun t => Real.tanh (Real.sqrt t) / (2 * Real.sqrt t)) :=
    fun t ht => (hasDerivAt_logCoshSqrt ht).deriv
  exact (hd.deriv isOpen_Ioi hx).trans (hasDerivAt_logCoshSqrt_derivative hx).deriv

theorem strictConcaveOn_logCoshSqrt : StrictConcaveOn ℝ (Ici 0) logCoshSqrt := by
  apply strictConcaveOn_of_deriv2_neg (convex_Ici 0)
    (((Real.continuous_cosh.comp Real.continuous_sqrt).log
      (fun x => (Real.cosh_pos (Real.sqrt x)).ne')).continuousOn)
  intro x hx
  have hx0 : 0 < x := by simpa only [interior_Ici, mem_Ioi] using hx
  change deriv (deriv logCoshSqrt) x < 0
  rw [deriv2_logCoshSqrt hx0]
  exact div_neg_of_neg_of_pos (by linarith only [sinh_cosh_sub_self_pos (Real.sqrt_pos.mpr hx0)])
    (mul_pos (mul_pos (by norm_num) (pow_pos (Real.sqrt_pos.mpr hx0) 3))
      (sq_pos_of_ne_zero (Real.cosh_pos _).ne'))

theorem coshSqrt_square (v : ℝ) : coshSqrt (v ^ 2) = Real.cosh v := by
  rw [coshSqrt, Real.sqrt_sq_eq_abs, Real.cosh_abs]

theorem logCoshSqrt_square (v : ℝ) : logCoshSqrt (v ^ 2) = Real.log (Real.cosh v) := by
  rw [logCoshSqrt, Real.sqrt_sq_eq_abs, Real.cosh_abs]

/-- The strict bound in equation (23) throughout the unaligned range.
No assumption on the size of the support values is used. -/
theorem two_point_centered_cosh_gt_geometric
    {w v₁ v₂ : ℝ} (hw : w ∈ Ioo 0 1) (hv : v₁ < v₂) (hs : v₁ + v₂ < 0) :
    Real.exp (w * Real.log (Real.cosh v₁) + (1 - w) * Real.log (Real.cosh v₂)) <
      w * Real.cosh (v₁ - 2 * (w * v₁ + (1 - w) * v₂)) +
        (1 - w) * Real.cosh (v₂ - 2 * (w * v₁ + (1 - w) * v₂)) := by
  let m := w * v₁ + (1 - w) * v₂
  let Q := w * v₁ ^ 2 + (1 - w) * v₂ ^ 2
  have hm2 : w * (v₁ - 2 * m) ^ 2 + (1 - w) * (v₂ - 2 * m) ^ 2 = Q := by
    dsimp [m, Q]
    ring
  have hne : v₁ ^ 2 ≠ v₂ ^ 2 := by
    intro he
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp he with h | h
    · exact hv.ne h
    · linarith
  have hlog := strictConcaveOn_logCoshSqrt.2 (sq_nonneg v₁) (sq_nonneg v₂) hne
    hw.1 (sub_pos.mpr hw.2) (by ring : w + (1 - w) = 1)
  simp only [smul_eq_mul, logCoshSqrt_square] at hlog
  have hconv := strictConvexOn_coshSqrt.convexOn.2
    (sq_nonneg (v₁ - 2 * m)) (sq_nonneg (v₂ - 2 * m)) hw.1.le
    (sub_nonneg.mpr hw.2.le) (by ring : w + (1 - w) = 1)
  simp only [smul_eq_mul, hm2, coshSqrt_square] at hconv
  have hexp := Real.exp_lt_exp.mpr hlog
  change _ < Real.exp (Real.log (Real.cosh (Real.sqrt Q))) at hexp
  rw [Real.exp_log (Real.cosh_pos _)] at hexp
  exact hexp.trans_le hconv

end PaperVerification.Hyperbolic

#print axioms PaperVerification.Hyperbolic.strictConvexOn_coshSqrt
#print axioms PaperVerification.Hyperbolic.strictConcaveOn_logCoshSqrt
#print axioms PaperVerification.Hyperbolic.two_point_centered_cosh_gt_geometric
end
end Source_HyperbolicJensen
-- END ORIGINAL PaperVerification.HyperbolicJensen


-- BEGIN ORIGINAL PaperVerification.HyperbolicTwoPoint
section Source_HyperbolicTwoPoint

-- original header: module
-- original header: public import PaperVerification.HyperbolicLocalization
-- original header: public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
-- original header: public import Mathlib.Analysis.MeanInequalities
-- original header: public import Mathlib.Tactic.LinearCombination
-- original header: @[expose] public section
/-! # The literal two-point functional

The definitions below are equation (14), including endpoint atoms and the
degenerate weights.  Subsequent scale and boundary arguments use this same
functional throughout.
-/

noncomputable section

namespace PaperVerification.Hyperbolic

open Real Set

def twoPointNumerator (R p q w : ℝ) : ℝ :=
  Real.cosh p ^ (4 * w) * Real.cosh q ^ (4 * (1 - w)) +
    Real.cosh (R - p) ^ (4 * w) * Real.cosh (R - q) ^ (4 * (1 - w)) -
    Real.sinh p ^ (4 * w) * Real.sinh q ^ (4 * (1 - w)) -
    Real.sinh (R - p) ^ (4 * w) * Real.sinh (R - q) ^ (4 * (1 - w))

def twoPointDenominator (R p q w : ℝ) : ℝ :=
  2 * Real.cosh R * Real.cosh (2 * p - R) ^ w * Real.cosh (2 * q - R) ^ (1 - w)

def twoPointRatio (R p q w : ℝ) : ℝ :=
  twoPointNumerator R p q w / twoPointDenominator R p q w

theorem twoPointDenominator_pos (R p q w : ℝ) : 0 < twoPointDenominator R p q w :=
  mul_pos (mul_pos (mul_pos (by norm_num) (Real.cosh_pos _))
    (Real.rpow_pos_of_pos (Real.cosh_pos _) _))
    (Real.rpow_pos_of_pos (Real.cosh_pos _) _)

theorem cosh_fourth_sub_sinh_fourth (p : ℝ) :
    Real.cosh p ^ 4 - Real.sinh p ^ 4 = Real.cosh (2 * p) := by
  rw [Real.cosh_two_mul]
  linear_combination (Real.cosh p ^ 2 + Real.sinh p ^ 2) * Real.cosh_sq_sub_sinh_sq p

theorem cosh_two_reflected_sum (R p : ℝ) :
    Real.cosh (2 * p) + Real.cosh (2 * (R - p)) =
      2 * Real.cosh R * Real.cosh (2 * p - R) := by
  have h₁ : 2 * p = R + (2 * p - R) := by ring
  have h₂ : 2 * (R - p) = R - (2 * p - R) := by ring
  calc
    Real.cosh (2*p)+Real.cosh (2*(R-p)) =
        Real.cosh (R+(2*p-R))+Real.cosh (R-(2*p-R)) :=
      congrArg₂ (· + ·) (congrArg Real.cosh h₁) (congrArg Real.cosh h₂)
    _ = 2*Real.cosh R*Real.cosh (2*p-R) := by
      rw [Real.cosh_add R (2*p-R),Real.cosh_sub R (2*p-R)]
      ring

theorem twoPointNumerator_weight_zero (R p q : ℝ) :
    twoPointNumerator R p q 0 = 2 * Real.cosh R * Real.cosh (2 * q - R) := by
  unfold twoPointNumerator
  norm_num only [mul_zero, sub_zero, mul_one, Real.rpow_zero, one_mul, Real.rpow_ofNat]
  calc
    _ = (Real.cosh q ^ 4 - Real.sinh q ^ 4) +
        (Real.cosh (R - q) ^ 4 - Real.sinh (R - q) ^ 4) := by ring
    _ = _ := by rw [cosh_fourth_sub_sinh_fourth, cosh_fourth_sub_sinh_fourth,
      cosh_two_reflected_sum]

theorem twoPointNumerator_weight_one (R p q : ℝ) :
    twoPointNumerator R p q 1 = 2 * Real.cosh R * Real.cosh (2 * p - R) := by
  unfold twoPointNumerator
  norm_num only [mul_one, sub_self, mul_zero, Real.rpow_zero, mul_one, Real.rpow_ofNat]
  calc
    _ = (Real.cosh p ^ 4 - Real.sinh p ^ 4) +
        (Real.cosh (R - p) ^ 4 - Real.sinh (R - p) ^ 4) := by ring
    _ = _ := by rw [cosh_fourth_sub_sinh_fourth, cosh_fourth_sub_sinh_fourth,
      cosh_two_reflected_sum]

@[simp] theorem twoPointRatio_weight_zero (R p q : ℝ) : twoPointRatio R p q 0 = 1 := by
  unfold twoPointRatio
  rw [twoPointNumerator_weight_zero]
  simp only [twoPointDenominator, sub_zero, Real.rpow_zero, Real.rpow_one, mul_one]
  exact div_self (mul_ne_zero (mul_ne_zero (by norm_num) (Real.cosh_pos _).ne') (Real.cosh_pos _).ne')

@[simp] theorem twoPointRatio_weight_one (R p q : ℝ) : twoPointRatio R p q 1 = 1 := by
  unfold twoPointRatio
  rw [twoPointNumerator_weight_one]
  simp only [twoPointDenominator, sub_self, Real.rpow_zero, Real.rpow_one, mul_one]
  exact div_self (mul_ne_zero (mul_ne_zero (by norm_num) (Real.cosh_pos _).ne') (Real.cosh_pos _).ne')

theorem twoPointNumerator_same {R p : ℝ} (hp : p ∈ Icc 0 R) (w : ℝ) :
    twoPointNumerator R p p w = 2 * Real.cosh R * Real.cosh (2 * p - R) := by
  have hfour (x : ℝ) (hx : 0 ≤ x) : x ^ (4 * w) * x ^ (4 * (1 - w)) = x ^ 4 := by
    rw [← Real.rpow_add' hx (by ring_nf; norm_num : 4 * w + 4 * (1 - w) ≠ 0),
      show 4 * w + 4 * (1 - w) = (4 : ℝ) by ring, Real.rpow_ofNat]
  unfold twoPointNumerator
  rw [hfour _ (Real.cosh_pos _).le, hfour _ (Real.cosh_pos _).le,
    hfour _ (Real.sinh_nonneg_iff.mpr hp.1),
    hfour _ (Real.sinh_nonneg_iff.mpr (sub_nonneg.mpr hp.2))]
  calc
    _ = (Real.cosh p ^ 4 - Real.sinh p ^ 4) +
        (Real.cosh (R - p) ^ 4 - Real.sinh (R - p) ^ 4) := by ring
    _ = _ := by rw [cosh_fourth_sub_sinh_fourth, cosh_fourth_sub_sinh_fourth,
      cosh_two_reflected_sum]

theorem twoPointRatio_same {R p : ℝ} (hp : p ∈ Icc 0 R) (w : ℝ) :
    twoPointRatio R p p w = 1 := by
  have hden : twoPointDenominator R p p w = 2 * Real.cosh R * Real.cosh (2 * p - R) := by
    unfold twoPointDenominator
    rw [mul_assoc, ← Real.rpow_add (Real.cosh_pos _) w (1 - w),
      show w + (1 - w) = (1 : ℝ) by ring, Real.rpow_one]
  unfold twoPointRatio
  rw [twoPointNumerator_same hp, hden]
  exact div_self (mul_ne_zero (mul_ne_zero (by norm_num) (Real.cosh_pos _).ne') (Real.cosh_pos _).ne')

theorem twoPointRatio_reflect (R p q w : ℝ) :
    twoPointRatio R (R - q) (R - p) (1 - w) = twoPointRatio R p q w := by
  have hsub : 1 - (1 - w) = w := by ring
  have hp : R - (R - p) = p := by ring
  have hq : R - (R - q) = q := by ring
  have hp' : 2 * (R - p) - R = -(2 * p - R) := by ring
  have hq' : 2 * (R - q) - R = -(2 * q - R) := by ring
  unfold twoPointRatio twoPointNumerator twoPointDenominator
  rw [hsub, hp, hq, hp', hq', Real.cosh_neg, Real.cosh_neg]
  congr 1 <;> ring

theorem weighted_cosh_product_gt_sinh_product {p q r s : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 < r) (hs : 0 < s) :
    Real.sinh p ^ r * Real.sinh q ^ s < Real.cosh p ^ r * Real.cosh q ^ s := by
  have hp' := Real.rpow_lt_rpow (Real.sinh_nonneg_iff.mpr hp) (Real.sinh_lt_cosh p) hr
  have hq' := Real.rpow_lt_rpow (Real.sinh_nonneg_iff.mpr hq) (Real.sinh_lt_cosh q) hs
  exact (mul_le_mul_of_nonneg_left hq'.le
    (Real.rpow_nonneg (Real.sinh_nonneg_iff.mpr hp) r)).trans_lt
      (mul_lt_mul_of_pos_right hp' (Real.rpow_pos_of_pos (Real.cosh_pos q) s))

theorem twoPointNumerator_pos {R p q w : ℝ}
    (hp : p ∈ Icc 0 R) (hq : q ∈ Icc 0 R) (hw : w ∈ Icc 0 1) :
    0 < twoPointNumerator R p q w := by
  rcases hw.1.eq_or_lt with hw0 | hw0
  · rw [← hw0, twoPointNumerator_weight_zero]
    positivity
  rcases hw.2.eq_or_lt with hw1 | hw1
  · rw [hw1, twoPointNumerator_weight_one]
    positivity
  have h4w : 0 < 4*w := mul_pos (by norm_num : (0:ℝ)<4) hw0
  have h4c : 0 < 4*(1-w) := mul_pos (by norm_num : (0:ℝ)<4) (sub_pos.mpr hw1)
  have h₁ := weighted_cosh_product_gt_sinh_product hp.1 hq.1 h4w h4c
  have h₂ := weighted_cosh_product_gt_sinh_product (sub_nonneg.mpr hp.2) (sub_nonneg.mpr hq.2)
    h4w h4c
  unfold twoPointNumerator
  linarith

theorem twoPointRatio_pos {R p q w : ℝ}
    (hp : p ∈ Icc 0 R) (hq : q ∈ Icc 0 R) (hw : w ∈ Icc 0 1) :
    0 < twoPointRatio R p q w :=
  div_pos (twoPointNumerator_pos hp hq hw) (twoPointDenominator_pos _ _ _ _)

theorem twoPointNumerator_half (R p q : ℝ) :
    twoPointNumerator R p q (1 / 2) =
      Real.cosh R * (Real.cosh (2 * p - R) + Real.cosh (2 * q - R)) := by
  have hprod (a b : ℝ) : Real.cosh a ^ 2 * Real.cosh b ^ 2 -
      Real.sinh a ^ 2 * Real.sinh b ^ 2 = (Real.cosh (2 * a) + Real.cosh (2 * b)) / 2 := by
    rw [Real.cosh_two_mul, Real.cosh_two_mul]
    linear_combination (Real.cosh b ^ 2 + Real.sinh b ^ 2) / 2 * Real.cosh_sq_sub_sinh_sq a +
      (Real.cosh a ^ 2 + Real.sinh a ^ 2) / 2 * Real.cosh_sq_sub_sinh_sq b
  unfold twoPointNumerator
  norm_num only [show (4 : ℝ) * (1 / 2) = 2 by norm_num,
    show (4 : ℝ) * (1 - 1 / 2) = 2 by norm_num, Real.rpow_ofNat]
  calc
    _ = (Real.cosh p ^ 2 * Real.cosh q ^ 2 - Real.sinh p ^ 2 * Real.sinh q ^ 2) +
        (Real.cosh (R - p) ^ 2 * Real.cosh (R - q) ^ 2 -
          Real.sinh (R - p) ^ 2 * Real.sinh (R - q) ^ 2) := by ring
    _ = _ := by
      rw [hprod, hprod]
      linear_combination (cosh_two_reflected_sum R p) / 2 + (cosh_two_reflected_sum R q) / 2

theorem twoPointRatio_half_ge_one (R p q : ℝ) : 1 ≤ twoPointRatio R p q (1 / 2) := by
  have ham := Real.geom_mean_le_arith_mean2_weighted
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (Real.cosh_pos (2 * p - R)).le (Real.cosh_pos (2 * q - R)).le (by norm_num : (1 : ℝ) / 2 + 1 / 2 = 1)
  apply (le_div_iff₀ (twoPointDenominator_pos _ _ _ _)).mpr
  rw [one_mul, twoPointNumerator_half]
  unfold twoPointDenominator
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
  have h := mul_le_mul_of_nonneg_left ham
    (mul_pos (by norm_num : (0:ℝ)<2) (Real.cosh_pos R)).le
  nlinarith only [h]

theorem twoPointRatio_half_eq_one_iff (R p q : ℝ) :
    twoPointRatio R p q (1 / 2) = 1 ↔ p = q ∨ p + q = R := by
  let A := Real.cosh (2 * p - R)
  let B := Real.cosh (2 * q - R)
  have hmean : A ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ) = A / 2 + B / 2 ↔ A = B := by
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using
      (Real.geom_mean_eq_arith_mean2_weighted_iff_of_pos (p₁:=A) (p₂:=B)
        (show (0 : ℝ) < 1 / 2 by norm_num) (show (0 : ℝ) < 1 / 2 by norm_num)
        (Real.cosh_pos (2 * p - R)).le (Real.cosh_pos (2 * q - R)).le
        (by norm_num : (1 : ℝ) / 2 + 1 / 2 = 1))
  have hratio : twoPointRatio R p q (1 / 2) = 1 ↔ A = B := by
    rw [twoPointRatio, div_eq_one_iff_eq (twoPointDenominator_pos _ _ _ _).ne',
      twoPointNumerator_half]
    unfold twoPointDenominator
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
    change Real.cosh R * (A + B) = 2 * Real.cosh R * A ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ) ↔ A = B
    rw [← hmean]
    constructor <;> intro h
    · apply (mul_left_cancel₀ (Real.cosh_pos R).ne')
      nlinarith only [h]
    · rw [show 2 * Real.cosh R * A ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ) =
        2 * Real.cosh R * (A ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ)) by ring, h]
      ring
  rw [hratio]
  constructor
  · intro h
    have he : |2 * p - R| = |2 * q - R| := le_antisymm
      (Real.cosh_le_cosh.mp h.le) (Real.cosh_le_cosh.mp h.ge)
    rcases abs_eq_abs.mp he with h | h
    · left; linarith
    · right; linarith
  · rintro (rfl | h)
    · rfl
    · change Real.cosh (2 * p - R) = Real.cosh (2 * q - R)
      have he : 2 * p - R = -(2 * q - R) := by linarith
      rw [he, Real.cosh_neg]

theorem continuous_twoPointRatio {w : ℝ} (hw : w ∈ Ioo 0 1) :
    Continuous (fun x : ℝ × ℝ × ℝ => twoPointRatio x.1 x.2.1 x.2.2 w) := by
  have he₁ : 0 ≤ 4 * w := (mul_pos (by norm_num) hw.1).le
  have he₂ : 0 ≤ 4 * (1 - w) := (mul_pos (by norm_num) (sub_pos.mpr hw.2)).le
  have hc (f : (ℝ × ℝ × ℝ) → ℝ) (hf : Continuous f) (s : ℝ) :
      Continuous (fun x => Real.cosh (f x) ^ s) :=
    (Real.continuous_cosh.comp hf).rpow_const (fun x => Or.inl (Real.cosh_pos _).ne')
  have hs (f : (ℝ × ℝ × ℝ) → ℝ) (hf : Continuous f) (s : ℝ) (h : 0 ≤ s) :
      Continuous (fun x => Real.sinh (f x) ^ s) :=
    (Real.continuous_sinh.comp hf).rpow_const (fun x => Or.inr h)
  unfold twoPointRatio
  apply Continuous.div
  · unfold twoPointNumerator
    exact (((hc _ continuous_snd.fst _).mul (hc _ continuous_snd.snd _)).add
      ((hc _ (continuous_fst.sub continuous_snd.fst) _).mul
        (hc _ (continuous_fst.sub continuous_snd.snd) _))).sub
      ((hs _ continuous_snd.fst _ he₁).mul (hs _ continuous_snd.snd _ he₂)) |>.sub
      ((hs _ (continuous_fst.sub continuous_snd.fst) _ he₁).mul
        (hs _ (continuous_fst.sub continuous_snd.snd) _ he₂))
  · unfold twoPointDenominator
    exact ((continuous_const.mul (Real.continuous_cosh.comp continuous_fst)).mul
      (hc _ ((continuous_const.mul continuous_snd.fst).sub continuous_fst) _)).mul
      (hc _ ((continuous_const.mul continuous_snd.snd).sub continuous_fst) _)
  · exact fun x => (twoPointDenominator_pos _ _ _ _).ne'

end PaperVerification.Hyperbolic

#print axioms PaperVerification.Hyperbolic.twoPointRatio_half_ge_one
#print axioms PaperVerification.Hyperbolic.continuous_twoPointRatio
end
end Source_HyperbolicTwoPoint
-- END ORIGINAL PaperVerification.HyperbolicTwoPoint


-- BEGIN ORIGINAL PaperVerification.HyperbolicDeficits
section Source_HyperbolicDeficits

-- original header: module
-- original header: public import PaperVerification.HyperbolicDividedDifference
-- original header: public import PaperVerification.HyperbolicJensen
-- original header: public import PaperVerification.HyperbolicTwoPoint
-- original header: @[expose] public section
/-! # The translated arithmetic deficits

Both functions are the literal real-power expressions in Section 4.2.
The derivative calculation is reduced to the already proved positive
divided-difference moment.
-/

noncomputable section

namespace PaperVerification.Hyperbolic

open Real Set

def arithmeticDeficit (δ r a : ℝ) : ℝ :=
  Real.cosh a ^ (2 + 2 * r) * Real.cosh (a + δ) ^ (2 - 2 * r) -
    Real.sinh a ^ (2 + 2 * r) * Real.sinh (a + δ) ^ (2 - 2 * r) -
    (1 + r) / 2 * Real.cosh (2 * a) - (1 - r) / 2 * Real.cosh (2 * (a + δ))

theorem rpow_weighted_square_ratio {x y r : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x ^ (2 + 2 * r) * y ^ (2 - 2 * r) =
      x ^ 2 * y ^ 2 * (x ^ 2 / y ^ 2) ^ r := by
  have hx' : (x ^ 2) ^ r = x ^ (2 * r) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hx.le]
  have hy' : (y ^ 2) ^ r = y ^ (2 * r) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hy.le]
  rw [Real.rpow_add hx 2 (2 * r), Real.rpow_sub hy 2 (2 * r),
    Real.rpow_two, Real.rpow_two, Real.div_rpow (sq_nonneg x) (sq_nonneg y), hx', hy']
  ring

theorem hasDerivAt_rpow_product_logarithmic {f g : ℝ → ℝ} {x f' g' r s : ℝ}
    (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x)
    (hfx : 0 < f x) (hgx : 0 < g x) :
    HasDerivAt (fun y => f y ^ r * g y ^ s)
      (f x ^ r * g x ^ s * (r * f' / f x + s * g' / g x)) x := by
  convert (hf.rpow_const (Or.inl hfx.ne')).mul (hg.rpow_const (Or.inl hgx.ne')) using 1
  rw [Real.rpow_sub_one hfx.ne' r, Real.rpow_sub_one hgx.ne' s]
  field_simp [hfx.ne', hgx.ne'] <;> ring

theorem powerSecant_eq_linear {v u D T z : ℝ} (hvu : v ≠ u)
    (h₁ : D ^ 2 - T ^ 2 = 1) (h₂ : D ^ 2 * u - T ^ 2 * v = 1) :
    powerSecant v u z = D ^ 2 * u ^ z - T ^ 2 * v ^ z := by
  have hD : (u - v) * D ^ 2 = 1 - v := by linear_combination h₂ - v * h₁
  have hT : (u - v) * T ^ 2 = 1 - u := by linear_combination h₂ - u * h₁
  unfold powerSecant
  rw [← hD, ← hT]
  field_simp [sub_ne_zero.mpr hvu.symm] <;> ring

theorem hyperbolic_square_ratio_bounds {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) :
    0 < Real.sinh a ^ 2 / Real.sinh (a + δ) ^ 2 ∧
      Real.sinh a ^ 2 / Real.sinh (a + δ) ^ 2 <
        Real.cosh a ^ 2 / Real.cosh (a + δ) ^ 2 ∧
      Real.cosh a ^ 2 / Real.cosh (a + δ) ^ 2 < 1 := by
  have hb : 0 < a + δ := add_pos ha hδ
  have hab : a < a + δ := lt_add_of_pos_right _ hδ
  have hC := Real.cosh_pos a
  have hD := Real.cosh_pos (a + δ)
  have hS := Real.sinh_pos_iff.mpr ha
  have hT := Real.sinh_pos_iff.mpr hb
  have hCD : Real.cosh a < Real.cosh (a + δ) := Real.cosh_strictMonoOn ha.le hb.le hab
  have hST : Real.sinh a < Real.sinh (a + δ) := Real.sinh_strictMono hab
  have hCs : Real.cosh a ^ 2 = 1 + Real.sinh a ^ 2 := by linarith [Real.cosh_sq_sub_sinh_sq a]
  have hDs : Real.cosh (a + δ) ^ 2 = 1 + Real.sinh (a + δ) ^ 2 := by
    linarith [Real.cosh_sq_sub_sinh_sq (a + δ)]
  refine ⟨div_pos (sq_pos_of_ne_zero hS.ne') (sq_pos_of_ne_zero hT.ne'), ?_, ?_⟩
  · apply (div_lt_div_iff₀ (sq_pos_of_ne_zero hT.ne') (sq_pos_of_ne_zero hD.ne')).mpr
    rw [hCs, hDs]
    nlinarith only [(sq_lt_sq₀ hS.le hT.le).mpr hST]
  · apply (div_lt_one (sq_pos_of_ne_zero hD.ne')).mpr
    exact (sq_lt_sq₀ hC.le hD.le).mpr hCD

theorem hasDerivAt_arithmeticDeficit {a δ r : ℝ} (ha : 0 < a) (hδ : 0 < δ) :
    HasDerivAt (arithmeticDeficit δ r)
      (2 * ((1 + r) * Real.cosh a * Real.sinh a *
          (powerSecant (Real.sinh a ^ 2 / Real.sinh (a + δ) ^ 2)
            (Real.cosh a ^ 2 / Real.cosh (a + δ) ^ 2) r - 1) +
        (1 - r) * Real.cosh (a + δ) * Real.sinh (a + δ) *
          (powerSecant (Real.sinh a ^ 2 / Real.sinh (a + δ) ^ 2)
            (Real.cosh a ^ 2 / Real.cosh (a + δ) ^ 2) (1 + r) - 1))) a := by
  let C := Real.cosh a
  let S := Real.sinh a
  let D := Real.cosh (a + δ)
  let T := Real.sinh (a + δ)
  let u := C ^ 2 / D ^ 2
  let v := S ^ 2 / T ^ 2
  have hC : 0 < C := Real.cosh_pos _
  have hD : 0 < D := Real.cosh_pos _
  have hS : 0 < S := Real.sinh_pos_iff.mpr ha
  have hT : 0 < T := Real.sinh_pos_iff.mpr (add_pos ha hδ)
  obtain ⟨hv, hvu, hu⟩ := hyperbolic_square_ratio_bounds ha hδ
  change 0 < v at hv
  change v < u at hvu
  change u < 1 at hu
  have hu0 := hv.trans hvu
  have hu' : D ^ 2 * u = C ^ 2 := by dsimp [u]; field_simp [hD.ne']
  have hv' : T ^ 2 * v = S ^ 2 := by dsimp [v]; field_simp [hT.ne']
  have h₁ : D ^ 2 - T ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq _
  have h₂ : D ^ 2 * u - T ^ 2 * v = 1 := by rw [hu', hv']; exact Real.cosh_sq_sub_sinh_sq _
  have hφ (z : ℝ) : powerSecant v u z = D ^ 2 * u ^ z - T ^ 2 * v ^ z :=
    powerSecant_eq_linear hvu.ne h₁ h₂
  have hφ' : powerSecant v u (1 + r) = C ^ 2 * u ^ r - S ^ 2 * v ^ r := by
    rw [hφ, Real.rpow_add hu0 1 r, Real.rpow_add hv 1 r, Real.rpow_one, Real.rpow_one]
    rw [← mul_assoc, hu', ← mul_assoc, hv']
  have hDb : HasDerivAt (fun a => Real.cosh (a + δ)) T a := by
    simpa only [mul_one, id_eq, T] using ((hasDerivAt_id a).add_const δ).cosh
  have hTb : HasDerivAt (fun a => Real.sinh (a + δ)) D a := by
    simpa only [mul_one, id_eq, D] using ((hasDerivAt_id a).add_const δ).sinh
  have hprodC := hasDerivAt_rpow_product_logarithmic (r := 2 + 2 * r) (s := 2 - 2 * r)
    (Real.hasDerivAt_cosh a) hDb hC hD
  have hprodS := hasDerivAt_rpow_product_logarithmic (r := 2 + 2 * r) (s := 2 - 2 * r)
    (Real.hasDerivAt_sinh a) hTb hS hT
  have hd := ((hprodC.sub hprodS).sub
    ((((hasDerivAt_id a).const_mul 2).cosh).const_mul ((1 + r) / 2))).sub
    (((((hasDerivAt_id a).add_const δ).const_mul 2).cosh).const_mul ((1 - r) / 2))
  convert hd using 1
  · rfl
  · change 2 * ((1 + r) * C * S * (powerSecant v u r - 1) +
        (1 - r) * D * T * (powerSecant v u (1 + r) - 1)) = _
    rw [hφ', hφ, rpow_weighted_square_ratio hC hD, rpow_weighted_square_ratio hS hT]
    simp only [Real.sinh_two_mul, mul_one]
    change 2 * ((1 + r) * C * S * (D ^ 2 * u ^ r - T ^ 2 * v ^ r - 1) +
      (1 - r) * D * T * (C ^ 2 * u ^ r - S ^ 2 * v ^ r - 1)) =
      C ^ 2 * D ^ 2 * u ^ r * ((2 + 2 * r) * S / C + (2 - 2 * r) * T / D) -
        S ^ 2 * T ^ 2 * v ^ r * ((2 + 2 * r) * C / S + (2 - 2 * r) * D / T) -
        (1 + r) / 2 * (2 * S * C * 2) -
        (1 - r) / 2 * (2 * T * D * 2)
    field_simp [hC.ne', hD.ne', hS.ne', hT.ne'] <;> ring

theorem deriv_arithmeticDeficit_neg {a δ r : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (hr : r ∈ Ioo 0 1) :
    deriv (arithmeticDeficit δ r) a < 0 := by
  let C := Real.cosh a
  let S := Real.sinh a
  let D := Real.cosh (a + δ)
  let T := Real.sinh (a + δ)
  let u := C ^ 2 / D ^ 2
  let v := S ^ 2 / T ^ 2
  have hC : 0 < C := Real.cosh_pos _
  have hD : 0 < D := Real.cosh_pos _
  have hS : 0 < S := Real.sinh_pos_iff.mpr ha
  have hT : 0 < T := Real.sinh_pos_iff.mpr (add_pos ha hδ)
  obtain ⟨hv, hvu, hu⟩ := hyperbolic_square_ratio_bounds ha hδ
  change 0 < v at hv
  change v < u at hvu
  change u < 1 at hu
  have harg : v * u = (C * S / (D * T)) ^ 2 := by
    dsimp [v, u]
    field_simp [hD.ne', hT.ne'] <;> ring
  have hg : Real.sqrt (v * u) = C * S / (D * T) := by
    rw [harg, Real.sqrt_sq_eq_abs, abs_of_pos (div_pos (mul_pos hC hS) (mul_pos hD hT))]
  have hineg := powerSecant_geometric_inequality hv hvu hu hr
  have hneg := mul_neg_of_pos_of_neg (mul_pos (by norm_num : (0 : ℝ) < 2) (mul_pos hD hT)) hineg
  rw [(hasDerivAt_arithmeticDeficit ha hδ).deriv]
  change 2 * ((1 + r) * C * S * (powerSecant v u r - 1) +
    (1 - r) * D * T * (powerSecant v u (1 + r) - 1)) < 0
  rw [hg] at hneg
  convert hneg using 1 <;> field_simp [hD.ne', hT.ne'] <;> ring

theorem continuous_arithmeticDeficit {δ r : ℝ} (hr : r ∈ Ioo (-1) 1) :
    Continuous (arithmeticDeficit δ r) := by
  have hplus : 0 ≤ 2 + 2 * r := by linarith [hr.1]
  have hminus : 0 ≤ 2 - 2 * r := by linarith [hr.2]
  unfold arithmeticDeficit
  exact (((Real.continuous_cosh.rpow_const (fun _ => Or.inr hplus)).mul
    ((Real.continuous_cosh.comp (continuous_id.add continuous_const)).rpow_const
      (fun _ => Or.inr hminus))).sub
    ((Real.continuous_sinh.rpow_const (fun _ => Or.inr hplus)).mul
      ((Real.continuous_sinh.comp (continuous_id.add continuous_const)).rpow_const
        (fun _ => Or.inr hminus)))).sub
    (continuous_const.mul (Real.continuous_cosh.comp (continuous_const.mul continuous_id))) |>.sub
    (continuous_const.mul (Real.continuous_cosh.comp
      (continuous_const.mul (continuous_id.add continuous_const))))

/-- The strict decrease asserted in equation (15), including the endpoint. -/
theorem strictAntiOn_arithmeticDeficit {δ r : ℝ} (hδ : 0 < δ) (hr : r ∈ Ioo 0 1) :
    StrictAntiOn (arithmeticDeficit δ r) (Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici 0)
    (continuous_arithmeticDeficit ⟨by linarith [hr.1], hr.2⟩).continuousOn
  intro a ha
  have ha0 : 0 < a := by simpa only [interior_Ici, mem_Ioi] using ha
  exact deriv_arithmeticDeficit_neg ha0 hδ hr

theorem rpow_symmetric_eq_sinh {x : ℝ} (hx : 0 < x) (r : ℝ) :
    x ^ r + x ^ (-r) = 4 * Real.sinh (r * Real.log x / 2) ^ 2 + 2 := by
  let t := r * Real.log x / 2
  have he : x ^ r + x ^ (-r) = 2 * Real.cosh (2 * t) := by
    rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hx, Real.cosh_eq]
    have h₁ : Real.log x * r = 2 * t := by dsimp [t]; ring
    have h₂ : Real.log x * (-r) = -(2 * t) := by dsimp [t]; ring
    rw [h₁, h₂]
    ring
  rw [he, Real.cosh_two_mul]
  nlinarith only [Real.cosh_sq_sub_sinh_sq t]

theorem rpow_square_ratio_symmetric {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (r : ℝ) :
    (x ^ 2 / y ^ 2) ^ r + (x ^ 2 / y ^ 2) ^ (-r) =
      4 * Real.sinh (r * Real.log (y / x)) ^ 2 + 2 := by
  rw [rpow_symmetric_eq_sinh (div_pos (sq_pos_of_ne_zero hx.ne') (sq_pos_of_ne_zero hy.ne'))]
  have ha : r * Real.log (x ^ 2 / y ^ 2) / 2 = -(r * Real.log (y / x)) := by
    rw [Real.log_div (pow_ne_zero _ hx.ne') (pow_ne_zero _ hy.ne'),
      Real.log_pow, Real.log_pow, Real.log_div hy.ne' hx.ne']
    norm_num
    ring
  rw [ha, Real.sinh_neg, neg_sq]

theorem sinh_log_ratio_balance {C S D T : ℝ}
    (hC : 0 < C) (hS : 0 < S) (hD : 0 < D) (hT : 0 < T)
    (h₁ : C ^ 2 - S ^ 2 = 1) (h₂ : D ^ 2 - T ^ 2 = 1) :
    C * D * Real.sinh (Real.log (D / C)) =
      S * T * Real.sinh (Real.log (T / S)) := by
  have hleft : C * D * Real.sinh (Real.log (D / C)) = (D ^ 2 - C ^ 2) / 2 := by
    rw [Real.sinh_eq, Real.exp_log (div_pos hD hC), Real.exp_neg,
      Real.exp_log (div_pos hD hC)]
    field_simp [hC.ne', hD.ne'] <;> ring
  have hright : S * T * Real.sinh (Real.log (T / S)) = (T ^ 2 - S ^ 2) / 2 := by
    rw [Real.sinh_eq, Real.exp_log (div_pos hT hS), Real.exp_neg,
      Real.exp_log (div_pos hT hS)]
    field_simp [hS.ne', hT.ne'] <;> ring
  rw [hleft, hright]
  linarith

theorem arithmeticDeficit_sum_identity {a δ r : ℝ} (ha : 0 < a) (hδ : 0 < δ) :
    arithmeticDeficit δ r a + arithmeticDeficit δ (-r) a =
      4 * ((Real.cosh a * Real.cosh (a + δ) *
          Real.sinh (r * Real.log (Real.cosh (a + δ) / Real.cosh a))) ^ 2 -
        (Real.sinh a * Real.sinh (a + δ) *
          Real.sinh (r * Real.log (Real.sinh (a + δ) / Real.sinh a))) ^ 2) := by
  have hC := Real.cosh_pos a
  have hD := Real.cosh_pos (a + δ)
  have hS := Real.sinh_pos_iff.mpr ha
  have hT := Real.sinh_pos_iff.mpr (add_pos ha hδ)
  have hbase : 2 * (Real.cosh a ^ 2 * Real.cosh (a + δ) ^ 2 -
      Real.sinh a ^ 2 * Real.sinh (a + δ) ^ 2) =
        Real.cosh (2 * a) + Real.cosh (2 * (a + δ)) := by
    rw [Real.cosh_two_mul, Real.cosh_two_mul]
    linear_combination
      (Real.cosh (a + δ) ^ 2 + Real.sinh (a + δ) ^ 2) * Real.cosh_sq_sub_sinh_sq a +
      (Real.cosh a ^ 2 + Real.sinh a ^ 2) * Real.cosh_sq_sub_sinh_sq (a + δ)
  unfold arithmeticDeficit
  rw [rpow_weighted_square_ratio hC hD, rpow_weighted_square_ratio hS hT,
    rpow_weighted_square_ratio hC hD, rpow_weighted_square_ratio hS hT]
  calc
    _ = Real.cosh a ^ 2 * Real.cosh (a + δ) ^ 2 *
        ((Real.cosh a ^ 2 / Real.cosh (a + δ) ^ 2) ^ r +
          (Real.cosh a ^ 2 / Real.cosh (a + δ) ^ 2) ^ (-r)) -
      Real.sinh a ^ 2 * Real.sinh (a + δ) ^ 2 *
        ((Real.sinh a ^ 2 / Real.sinh (a + δ) ^ 2) ^ r +
          (Real.sinh a ^ 2 / Real.sinh (a + δ) ^ 2) ^ (-r)) -
      Real.cosh (2 * a) - Real.cosh (2 * (a + δ)) := by ring
    _ = _ := by
      rw [rpow_square_ratio_symmetric hC hD, rpow_square_ratio_symmetric hS hT]
      linear_combination hbase

theorem arithmeticDeficit_sum_pos_of_pos {a δ r : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (hr : r ∈ Ioo 0 1) :
    0 < arithmeticDeficit δ r a + arithmeticDeficit δ (-r) a := by
  let C := Real.cosh a
  let S := Real.sinh a
  let D := Real.cosh (a + δ)
  let T := Real.sinh (a + δ)
  let A := Real.log (D / C)
  let B := Real.log (T / S)
  have hC : 0 < C := Real.cosh_pos _
  have hD : 0 < D := Real.cosh_pos _
  have hS : 0 < S := Real.sinh_pos_iff.mpr ha
  have hT : 0 < T := Real.sinh_pos_iff.mpr (add_pos ha hδ)
  have hab : a < a + δ := lt_add_of_pos_right _ hδ
  have hCD : C < D := Real.cosh_strictMonoOn ha.le (add_pos ha hδ).le hab
  have hA : 0 < A := Real.log_pos ((one_lt_div hC).mpr hCD)
  have hTC : 0 < T * C - D * S := by
    have hs := Real.sinh_sub (a + δ) a
    rw [add_sub_cancel_left] at hs
    rw [← hs]
    exact Real.sinh_pos_iff.mpr hδ
  have hAB : A < B := Real.log_lt_log (div_pos hD hC)
    ((div_lt_div_iff₀ hC hS).mpr (by linarith only [hTC]))
  have hB := hA.trans hAB
  have hbalance : C * D * Real.sinh A = S * T * Real.sinh B :=
    sinh_log_ratio_balance hC hS hD hT (Real.cosh_sq_sub_sinh_sq _) (Real.cosh_sq_sub_sinh_sq _)
  have hratio := strictAntiOn_sinh_scale_ratio hr hA hB hAB
  have hprod : S * T * Real.sinh (r * B) < C * D * Real.sinh (r * A) := by
    calc
      _ = (C * D * Real.sinh A) * (Real.sinh (r * B) / Real.sinh B) := by
        rw [hbalance]
        field_simp [(Real.sinh_pos_iff.mpr hB).ne'] <;> ring
      _ < (C * D * Real.sinh A) * (Real.sinh (r * A) / Real.sinh A) :=
        mul_lt_mul_of_pos_left hratio (mul_pos (mul_pos hC hD) (Real.sinh_pos_iff.mpr hA))
      _ = _ := by field_simp [(Real.sinh_pos_iff.mpr hA).ne'] <;> ring
  have hsquare : (S * T * Real.sinh (r * B)) ^ 2 < (C * D * Real.sinh (r * A)) ^ 2 :=
    (sq_lt_sq₀ (mul_pos (mul_pos hS hT) (Real.sinh_pos_iff.mpr (mul_pos hr.1 hB))).le
      (mul_pos (mul_pos hC hD) (Real.sinh_pos_iff.mpr (mul_pos hr.1 hA))).le).mpr hprod
  rw [arithmeticDeficit_sum_identity ha hδ]
  change 0 < 4 * ((C * D * Real.sinh (r * A)) ^ 2 - (S * T * Real.sinh (r * B)) ^ 2)
  exact mul_pos (by norm_num) (sub_pos.mpr hsquare)

theorem arithmeticDeficit_sum_zero_identity {δ r : ℝ} (hr : r ∈ Ioo 0 1) :
    arithmeticDeficit δ r 0 + arithmeticDeficit δ (-r) 0 =
      4 * Real.cosh δ ^ 2 * Real.sinh (r * Real.log (Real.cosh δ)) ^ 2 := by
  have hC := Real.cosh_pos δ
  have he₁ : 2 + 2 * r ≠ 0 := by linarith [hr.1]
  have he₂ : 2 + 2 * (-r) ≠ 0 := by linarith [hr.2]
  unfold arithmeticDeficit
  simp only [Real.cosh_zero, Real.sinh_zero, Real.one_rpow, Real.zero_rpow he₁,
    Real.zero_rpow he₂, one_mul, zero_mul, sub_zero, add_zero, zero_add, mul_zero]
  have hp : 2 - 2 * r = 2 + (-2 * r) := by ring
  have hm : 2 - 2 * (-r) = 2 + 2 * r := by ring
  rw [hp, hm, Real.rpow_add hC 2 (-2 * r), Real.rpow_add hC 2 (2 * r), Real.rpow_two]
  have hsym := rpow_symmetric_eq_sinh hC (2 * r)
  rw [show -(2 * r) = -2 * r by ring, show 2 * r * Real.log (Real.cosh δ) / 2 =
    r * Real.log (Real.cosh δ) by ring] at hsym
  rw [Real.cosh_two_mul]
  nlinarith only [hsym, Real.cosh_sq_sub_sinh_sq δ,
    congrArg (fun x : ℝ => Real.cosh δ ^ 2 * x) hsym]

/-- The other strict assertion of equation (15), also at the endpoint. -/
theorem arithmeticDeficit_sum_pos {a δ r : ℝ}
    (ha : 0 ≤ a) (hδ : 0 < δ) (hr : r ∈ Ioo 0 1) :
    0 < arithmeticDeficit δ r a + arithmeticDeficit δ (-r) a := by
  rcases ha.eq_or_lt with ha | ha
  · rw [← ha, arithmeticDeficit_sum_zero_identity hr]
    have hc : 1 < Real.cosh δ := Real.one_lt_cosh.mpr hδ.ne'
    exact mul_pos (mul_pos (by norm_num) (sq_pos_of_ne_zero (Real.cosh_pos _).ne'))
      (sq_pos_of_ne_zero (Real.sinh_pos_iff.mpr (mul_pos hr.1 (Real.log_pos hc))).ne')
  · exact arithmeticDeficit_sum_pos_of_pos ha hδ hr

theorem twoPointNumerator_sub_arithmetic (R p q w : ℝ) :
    twoPointNumerator R p q w -
      2 * Real.cosh R * (w * Real.cosh (2 * p - R) + (1 - w) * Real.cosh (2 * q - R)) =
      arithmeticDeficit (q - p) (-(1 - 2 * w)) p +
        arithmeticDeficit (q - p) (1 - 2 * w) (R - q) := by
  have hpq : p + (q - p) = q := by ring
  have hR : R - q + (q - p) = R - p := by ring
  have he₁ : 2 + 2 * (-(1 - 2 * w)) = 4 * w := by ring
  have he₂ : 2 - 2 * (-(1 - 2 * w)) = 4 * (1 - w) := by ring
  have he₃ : 2 + 2 * (1 - 2 * w) = 4 * (1 - w) := by ring
  have he₄ : 2 - 2 * (1 - 2 * w) = 4 * w := by ring
  unfold arithmeticDeficit twoPointNumerator
  rw [hpq, hR, he₁, he₂, he₃, he₄]
  linear_combination w * (cosh_two_reflected_sum R p) + (1 - w) * (cosh_two_reflected_sum R q)

/-- The complete strict aligned-range inequality of Section 4.3. -/
theorem twoPointRatio_gt_one_aligned {R p q w : ℝ}
    (hp : p ∈ Icc 0 R) (hq : q ∈ Icc 0 R)
    (hpq : p < q) (hw : w ∈ Ioo 0 (1 / 2)) (halign : R ≤ p + q) :
    1 < twoPointRatio R p q w := by
  let δ := q - p
  let r := 1 - 2 * w
  have hδ : 0 < δ := sub_pos.mpr hpq
  have hr : r ∈ Ioo 0 1 := by dsimp [r]; constructor <;> linarith [hw.1, hw.2]
  have ha' : 0 ≤ R - q := sub_nonneg.mpr hq.2
  have hle : R - q ≤ p := by linarith
  have hmono := (strictAntiOn_arithmeticDeficit hδ hr).antitoneOn ha' hp.1 hle
  have hsum := arithmeticDeficit_sum_pos hp.1 hδ hr
  have hstrict : 0 < arithmeticDeficit δ (-r) p + arithmeticDeficit δ r (R - q) := by
    linarith
  have hF : 2 * Real.cosh R *
      (w * Real.cosh (2 * p - R) + (1 - w) * Real.cosh (2 * q - R)) <
        twoPointNumerator R p q w := by
    apply sub_pos.mp
    rw [twoPointNumerator_sub_arithmetic]
    exact hstrict
  have ham := Real.geom_mean_le_arith_mean2_weighted hw.1.le
    (show 0 ≤ 1 - w by linarith [hw.2]) (Real.cosh_pos (2 * p - R)).le
    (Real.cosh_pos (2 * q - R)).le (by ring : w + (1 - w) = 1)
  have hden : twoPointDenominator R p q w ≤ 2 * Real.cosh R *
      (w * Real.cosh (2 * p - R) + (1 - w) * Real.cosh (2 * q - R)) := by
    unfold twoPointDenominator
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left ham
      (mul_pos (by norm_num) (Real.cosh_pos R)).le
  exact (lt_div_iff₀ (twoPointDenominator_pos _ _ _ _)).mpr
    (by simpa only [one_mul] using hden.trans_lt hF)

end PaperVerification.Hyperbolic

#print axioms PaperVerification.Hyperbolic.deriv_arithmeticDeficit_neg
#print axioms PaperVerification.Hyperbolic.strictAntiOn_arithmeticDeficit
#print axioms PaperVerification.Hyperbolic.twoPointRatio_gt_one_aligned
end
end Source_HyperbolicDeficits
-- END ORIGINAL PaperVerification.HyperbolicDeficits


-- BEGIN ORIGINAL PaperVerification.HyperbolicBoundaryActual
section Source_HyperbolicBoundaryActual

-- original header: module
-- original header: public import PaperVerification.HyperbolicBoundary
-- original header: public import PaperVerification.HyperbolicTwoPoint
-- original header: public import PaperVerification.HyperbolicDeficits
-- original header: @[expose] public section
/-! # Boundary derivatives of the literal two-point functional

The derivative identities in this file are obtained directly from equation
(14).  No transformed boundary formula is assumed.
-/

noncomputable section

namespace PaperVerification.Hyperbolic

open Real Set

def twoPointObjective (R p q w : ℝ) : ℝ :=
  Real.log (twoPointNumerator R p q w) - Real.log 2 - Real.log (Real.cosh R) -
    w * Real.log (Real.cosh (2 * p - R)) - (1 - w) * Real.log (Real.cosh (2 * q - R))

def boundaryTermU (q w : ℝ) : ℝ := Real.cosh q ^ (4 * (1 - w))

def boundaryTermV (R q w : ℝ) : ℝ :=
  Real.cosh R ^ (4 * w) * Real.cosh (R - q) ^ (4 * (1 - w))

def boundaryTermW (R q w : ℝ) : ℝ :=
  Real.sinh R ^ (4 * w) * Real.sinh (R - q) ^ (4 * (1 - w))

def boundaryActualX (R q w : ℝ) : ℝ :=
  2 * boundaryTermU q w / twoPointNumerator R 0 q w - 1

def boundaryActualY (R q w : ℝ) : ℝ :=
  2 * boundaryTermW R q w / twoPointNumerator R 0 q w

theorem twoPointDenominator_log (R p q w : ℝ) :
    Real.log (twoPointDenominator R p q w) = Real.log 2 + Real.log (Real.cosh R) +
      w * Real.log (Real.cosh (2 * p - R)) + (1 - w) * Real.log (Real.cosh (2 * q - R)) := by
  unfold twoPointDenominator
  rw [Real.log_mul (mul_ne_zero (mul_ne_zero (by norm_num) (Real.cosh_pos R).ne')
      (Real.rpow_pos_of_pos (Real.cosh_pos _) _).ne')
      (Real.rpow_pos_of_pos (Real.cosh_pos _) _).ne',
    Real.log_mul (mul_ne_zero (by norm_num) (Real.cosh_pos R).ne')
      (Real.rpow_pos_of_pos (Real.cosh_pos _) _).ne',
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.cosh_pos R).ne',
    Real.log_rpow (Real.cosh_pos _), Real.log_rpow (Real.cosh_pos _)]

theorem twoPointObjective_eq_log_ratio {R p q w : ℝ}
    (hp : p ∈ Icc 0 R) (hq : q ∈ Icc 0 R) (hw : w ∈ Icc 0 1) :
    twoPointObjective R p q w = Real.log (twoPointRatio R p q w) := by
  rw [twoPointRatio, Real.log_div (twoPointNumerator_pos hp hq hw).ne'
    (twoPointDenominator_pos _ _ _ _).ne', twoPointDenominator_log]
  unfold twoPointObjective
  ring

theorem boundary_numerator (R q w : ℝ) (hw : 0 < w) :
    twoPointNumerator R 0 q w = boundaryTermU q w + boundaryTermV R q w - boundaryTermW R q w := by
  simp only [twoPointNumerator, boundaryTermU, boundaryTermV, boundaryTermW,
    Real.cosh_zero, Real.sinh_zero, Real.one_rpow,
    Real.zero_rpow (mul_pos (by norm_num : (0 : ℝ) < 4) hw).ne',
    one_mul, zero_mul, sub_zero]

theorem hasDerivAt_cosh_rpow (x r : ℝ) :
    HasDerivAt (fun x => Real.cosh x ^ r) (r * Real.tanh x * Real.cosh x ^ r) x := by
  have hc := (Real.cosh_pos x).ne'
  convert (Real.hasDerivAt_cosh x).rpow_const (Or.inl hc) using 1
  · rw [Real.rpow_sub_one hc, Real.tanh_eq_sinh_div_cosh]
    ring

theorem hasDerivAt_sinh_rpow {x : ℝ} (hx : 0 < x) (r : ℝ) :
    HasDerivAt (fun x => Real.sinh x ^ r) (r * coth x * Real.sinh x ^ r) x := by
  have hs := (Real.sinh_pos_iff.mpr hx).ne'
  convert (Real.hasDerivAt_sinh x).rpow_const (Or.inl hs) using 1
  · rw [Real.rpow_sub_one hs]
    unfold coth
    ring

theorem hasDerivAt_sinh_rpow_zero {r : ℝ} (hr : 1 < r) :
    HasDerivAt (fun x => Real.sinh x ^ r) 0 0 := by
  have hd := (Real.hasDerivAt_sinh 0).rpow_const (p := r) (Or.inr hr.le)
  simpa only [Real.sinh_zero, Real.cosh_zero, one_mul,
    Real.zero_rpow (sub_pos.mpr hr).ne', mul_zero] using hd

theorem hasDerivAt_boundaryNumerator_q {R q w : ℝ}
    (hq : q < R) (hw : 0 < w) :
    HasDerivAt (fun q => twoPointNumerator R 0 q w)
      (4 * (1 - w) * (boundaryTermU q w * Real.tanh q -
        boundaryTermV R q w * Real.tanh (R - q) + boundaryTermW R q w * coth (R - q))) q := by
  have hU := hasDerivAt_cosh_rpow q (4 * (1 - w))
  have hV := ((hasDerivAt_cosh_rpow (R - q) (4 * (1 - w))).comp q
    ((hasDerivAt_id q).const_sub R)).const_mul (Real.cosh R ^ (4 * w))
  have hW := ((hasDerivAt_sinh_rpow (sub_pos.mpr hq) (4 * (1 - w))).comp q
    ((hasDerivAt_id q).const_sub R)).const_mul (Real.sinh R ^ (4 * w))
  convert (hU.add hV).sub hW using 1
  · funext q
    exact boundary_numerator R q w hw
  · simp only [boundaryTermU, boundaryTermV, boundaryTermW, Function.comp_apply]
    ring

theorem hasDerivAt_boundaryNumerator_R {R q w : ℝ}
    (hR : 0 < R) (hq : q < R) (hw : 0 < w) :
    HasDerivAt (fun R => twoPointNumerator R 0 q w)
      (boundaryTermV R q w * (4 * w * Real.tanh R + 4 * (1 - w) * Real.tanh (R - q)) -
        boundaryTermW R q w * (4 * w * coth R + 4 * (1 - w) * coth (R - q))) R := by
  have hC := hasDerivAt_cosh_rpow R (4 * w)
  have hD := (hasDerivAt_cosh_rpow (R - q) (4 * (1 - w))).comp R ((hasDerivAt_id R).sub_const q)
  have hS := hasDerivAt_sinh_rpow hR (4 * w)
  have hT := (hasDerivAt_sinh_rpow (sub_pos.mpr hq) (4 * (1 - w))).comp R
    ((hasDerivAt_id R).sub_const q)
  have hd := ((hC.mul hD).const_add (boundaryTermU q w)).sub (hS.mul hT)
  convert hd using 1
  · funext R
    exact boundary_numerator R q w hw
  · simp only [boundaryTermV, boundaryTermW, Function.comp_apply, id_eq]
    ring

theorem hasDerivAt_boundaryNumerator_p {R q w : ℝ}
    (hR : 0 < R) (hw : 1 < 4 * w) :
    HasDerivAt (fun p => twoPointNumerator R p q w)
      (4 * w * (-Real.tanh R * boundaryTermV R q w + coth R * boundaryTermW R q w)) 0 := by
  have hA := (hasDerivAt_cosh_rpow 0 (4 * w)).mul_const (Real.cosh q ^ (4 * (1 - w)))
  have hC := ((hasDerivAt_cosh_rpow (R - 0) (4 * w)).comp 0
    ((hasDerivAt_id 0).const_sub R)).mul_const (Real.cosh (R - q) ^ (4 * (1 - w)))
  have hB := (hasDerivAt_sinh_rpow_zero hw).mul_const (Real.sinh q ^ (4 * (1 - w)))
  have hD := ((hasDerivAt_sinh_rpow (show 0 < R - 0 by simpa only [sub_zero] using hR) (4 * w)).comp 0
    ((hasDerivAt_id 0).const_sub R)).mul_const (Real.sinh (R - q) ^ (4 * (1 - w)))
  simp only [sub_zero] at hC hD
  convert ((hA.add hC).sub hB).sub hD using 1
  · rfl
  · simp only [boundaryTermV, boundaryTermW, Real.tanh_zero, Real.cosh_zero,
      Real.one_rpow, mul_zero, zero_mul, zero_add, add_zero, sub_zero, Function.comp_apply]
    ring

theorem hasDerivAt_boundaryObjective_q {R q w : ℝ}
    (hq : q < R) (hw : 0 < w) (hF : twoPointNumerator R 0 q w ≠ 0) :
    HasDerivAt (fun q => twoPointObjective R 0 q w)
      (4 * (1 - w) * (boundaryTermU q w * Real.tanh q -
        boundaryTermV R q w * Real.tanh (R - q) + boundaryTermW R q w * coth (R - q)) /
          twoPointNumerator R 0 q w - 2 * (1 - w) * Real.tanh (2 * q - R)) q := by
  have hnum := (hasDerivAt_boundaryNumerator_q hq hw).log hF
  have hlast := ((hasDerivAt_log_cosh (2 * q - R)).comp q
    (((hasDerivAt_id q).const_mul 2).sub_const R)).const_mul (1 - w)
  convert (((hnum.sub_const (Real.log 2)).sub_const (Real.log (Real.cosh R))).sub_const
    (w * Real.log (Real.cosh (2 * 0 - R)))).sub hlast using 1
  · rfl
  · ring

theorem hasDerivAt_boundaryObjective_R {R q w : ℝ}
    (hR : 0 < R) (hq : q < R) (hw : 0 < w) (hF : twoPointNumerator R 0 q w ≠ 0) :
    HasDerivAt (fun R => twoPointObjective R 0 q w)
      ((boundaryTermV R q w * (4 * w * Real.tanh R + 4 * (1 - w) * Real.tanh (R - q)) -
        boundaryTermW R q w * (4 * w * coth R + 4 * (1 - w) * coth (R - q))) /
          twoPointNumerator R 0 q w - (1 + w) * Real.tanh R +
            (1 - w) * Real.tanh (2 * q - R)) R := by
  have hnum := (hasDerivAt_boundaryNumerator_R hR hq hw).log hF
  have hmid := ((hasDerivAt_log_cosh (2 * 0 - R)).comp R
    ((hasDerivAt_id R).const_sub (2 * 0))).const_mul w
  have hlast := ((hasDerivAt_log_cosh (2 * q - R)).comp R
    ((hasDerivAt_id R).const_sub (2 * q))).const_mul (1 - w)
  convert (((hnum.sub_const (Real.log 2)).sub (hasDerivAt_log_cosh R)).sub hmid).sub hlast using 1
  · rfl
  · simp only [mul_zero, zero_sub, Real.tanh_neg]
    ring

theorem hasDerivAt_boundaryObjective_p {R q w : ℝ}
    (hR : 0 < R) (hw : 1 < 4 * w) (hF : twoPointNumerator R 0 q w ≠ 0) :
    HasDerivAt (fun p => twoPointObjective R p q w)
      (4 * w * (-Real.tanh R * boundaryTermV R q w + coth R * boundaryTermW R q w) /
        twoPointNumerator R 0 q w + 2 * w * Real.tanh R) 0 := by
  have hnum := (hasDerivAt_boundaryNumerator_p hR hw).log hF
  have hmid := ((hasDerivAt_log_cosh (2 * 0 - R)).comp 0
    (((hasDerivAt_id 0).const_mul 2).sub_const R)).const_mul w
  have hd := (((hnum.sub_const (Real.log 2)).sub_const (Real.log (Real.cosh R))).sub hmid).sub_const
    ((1 - w) * Real.log (Real.cosh (2 * q - R)))
  convert hd using 1
  · rfl
  · simp only [mul_zero, zero_sub, Real.tanh_neg]
    ring

theorem strictMono_tanh : StrictMono Real.tanh := by
  apply strictMono_of_deriv_pos
  intro x
  rw [(hasDerivAt_tanh x).deriv]
  exact sub_pos.mpr (Real.tanh_sq_lt_one x)

theorem tanh_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.mpr hx) (Real.cosh_pos x)

theorem coth_eq_inv_tanh (x : ℝ) : coth x = 1 / Real.tanh x := by
  simp only [coth, Real.tanh_eq_sinh_div_cosh, one_div_div, one_mul]

theorem one_sub_tanh_product_pos (x y : ℝ) : 0 < 1 - Real.tanh x * Real.tanh y := by
  have he : Real.cosh (x - y) = Real.cosh x * Real.cosh y * (1 - Real.tanh x * Real.tanh y) := by
    rw [Real.cosh_sub, Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh]
    field_simp [(Real.cosh_pos x).ne', (Real.cosh_pos y).ne'] <;> ring
  have h := Real.cosh_pos (x - y)
  rw [he] at h
  exact (mul_pos_iff_of_pos_left (mul_pos (Real.cosh_pos x) (Real.cosh_pos y))).mp h

theorem tanh_sub_formula (x y : ℝ) :
    Real.tanh (x - y) = (Real.tanh x - Real.tanh y) / (1 - Real.tanh x * Real.tanh y) := by
  have hn := (one_sub_tanh_product_pos x y).ne'
  apply (eq_div_iff hn).mpr
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_sub, Real.cosh_sub,
    Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh]
  have hc : Real.cosh x * Real.cosh y - Real.sinh x * Real.sinh y ≠ 0 := by
    rw [← Real.cosh_sub]
    exact (Real.cosh_pos _).ne'
  have hc' : -(Real.sinh x * Real.sinh y) + Real.cosh y * Real.cosh x ≠ 0 := by
    convert hc using 1 <;> ring
  field_simp [(Real.cosh_pos x).ne', (Real.cosh_pos y).ne', hc, hc'] <;>
    ring_nf <;> field_simp [hc'] <;> ring

theorem tanh_sub_two_den_pos (x y : ℝ) :
    0 < 1 - 2 * Real.tanh x * Real.tanh y + Real.tanh y ^ 2 := by
  have he : Real.cosh (x - 2 * y) = Real.cosh x * Real.cosh y ^ 2 *
      (1 - 2 * Real.tanh x * Real.tanh y + Real.tanh y ^ 2) := by
    rw [Real.cosh_sub, Real.cosh_two_mul, Real.sinh_two_mul,
      Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh]
    field_simp [(Real.cosh_pos x).ne', (Real.cosh_pos y).ne'] <;> ring
  have h := Real.cosh_pos (x - 2 * y)
  rw [he] at h
  exact (mul_pos_iff_of_pos_left
    (mul_pos (Real.cosh_pos x) (sq_pos_of_ne_zero (Real.cosh_pos y).ne'))).mp h

theorem tanh_sub_two_formula (x y : ℝ) :
    Real.tanh (x - 2 * y) =
      (Real.tanh x - 2 * Real.tanh y + Real.tanh x * Real.tanh y ^ 2) /
        (1 - 2 * Real.tanh x * Real.tanh y + Real.tanh y ^ 2) := by
  apply (eq_div_iff (tanh_sub_two_den_pos x y).ne').mpr
  -- Clear the original cosh denominator before expanding it. Otherwise a
  -- ring normal form can reorder the expanded denominator after field_simp.
  rw [Real.tanh_eq_sinh_div_cosh (x - 2*y), div_mul_eq_mul_div]
  apply (div_eq_iff (Real.cosh_pos (x - 2*y)).ne').mpr
  rw [Real.sinh_sub, Real.cosh_sub, Real.cosh_two_mul, Real.sinh_two_mul]
  simp only [Real.tanh_eq_sinh_div_cosh]
  field_simp [(Real.cosh_pos x).ne', (Real.cosh_pos y).ne'] <;> ring

theorem boundary_tanh_parameters {R q : ℝ} (hq : q ∈ Ioo 0 R) :
    Real.tanh R ^ 2 ∈ Ioo 0 1 ∧ Real.tanh (R - q) / Real.tanh R ∈ Ioo 0 1 := by
  have hR := hq.1.trans hq.2
  have hT := tanh_pos_of_pos hR
  have hV := tanh_pos_of_pos (sub_pos.mpr hq.2)
  have hVT : Real.tanh (R - q) < Real.tanh R := strictMono_tanh (by linarith [hq.1])
  exact ⟨⟨sq_pos_of_ne_zero hT.ne', Real.tanh_sq_lt_one R⟩,
    ⟨div_pos hV hT, (div_lt_one hT).mpr hVT⟩⟩

theorem boundary_tanh_formulas {R q : ℝ} (hq : q ∈ Ioo 0 R) :
    let T := Real.tanh R
    let u := T ^ 2
    let z := Real.tanh (R - q) / T
    Real.tanh q = T * (1 - z) / (1 - u * z) ∧
      Real.tanh (2 * q - R) = T * (1 - 2 * z + u * z ^ 2) / (1 - 2 * u * z + u * z ^ 2) ∧
      Real.tanh (R - q) = T * z := by
  dsimp only
  let T := Real.tanh R
  let u := T ^ 2
  let z := Real.tanh (R - q) / T
  have hT : 0 < T := tanh_pos_of_pos (hq.1.trans hq.2)
  have hV : Real.tanh (R - q) = T * z := by dsimp [z]; field_simp [hT.ne']
  obtain ⟨hu, hz⟩ := boundary_tanh_parameters hq
  change u ∈ Ioo 0 1 at hu
  change z ∈ Ioo 0 1 at hz
  have hb : 0 < 1 - u * z := (boundary_parameters_pos hu hz).2.1
  have hc := (boundary_cd_pos hu hz).1
  refine ⟨?_, ?_, hV⟩
  · change Real.tanh q = T * (1 - z) / (1 - u * z)
    conv_lhs => rw [show q = R - (R - q) by ring]
    rw [tanh_sub_formula, hV]
    change (T - T * z) / (1 - T * (T * z)) = T * (1 - z) / (1 - u * z)
    dsimp [u]
    congr 1 <;> ring
  · change Real.tanh (2 * q - R) =
      T * (1 - 2 * z + u * z ^ 2) / (1 - 2 * u * z + u * z ^ 2)
    rw [show 2 * q - R = R - 2 * (R - q) by ring, tanh_sub_two_formula, hV]
    change (T - 2 * (T * z) + T * (T * z) ^ 2) /
      (1 - 2 * T * (T * z) + (T * z) ^ 2) =
        T * (1 - 2 * z + u * z ^ 2) / (1 - 2 * u * z + u * z ^ 2)
    dsimp [u]
    congr 1 <;> ring

/-- All three actual first derivatives in the variables used by the compact
minimum argument. -/
theorem boundary_actual_derivatives {R q w : ℝ}
    (hq : q ∈ Ioo 0 R) (hw : w ∈ Ioo (1 / 4) (1 / 2)) :
    let T := Real.tanh R
    let u := T ^ 2
    let z := Real.tanh (R - q) / T
    let t := 2 * (1 - w)
    let X := boundaryActualX R q w
    let Y := boundaryActualY R q w
    HasDerivAt (fun q => twoPointObjective R 0 q w)
      (T * boundaryQNormalized u z t X Y) q ∧
    HasDerivAt (fun R => twoPointObjective R 0 q w)
      (T * boundaryRNormalized u z t X Y) R ∧
    HasDerivAt (fun p => twoPointObjective R p q w)
      (2 * w * T * (X + (1 - u) / u * Y)) 0 := by
  dsimp only
  let T := Real.tanh R
  let u := T ^ 2
  let z := Real.tanh (R - q) / T
  let t := 2 * (1 - w)
  let F := twoPointNumerator R 0 q w
  let U := boundaryTermU q w
  let V := boundaryTermV R q w
  let W := boundaryTermW R q w
  have hR := hq.1.trans hq.2
  have hw0 : 0 < w := (by norm_num : (0 : ℝ) < 1 / 4).trans hw.1
  have hw1 : w < 1 := hw.2.trans (by norm_num)
  have hr : 1 < 4 * w := by linarith [hw.1]
  have hF : 0 < F := twoPointNumerator_pos ⟨le_rfl, hR.le⟩ ⟨hq.1.le, hq.2.le⟩ ⟨hw0.le, hw1.le⟩
  have hT : 0 < T := tanh_pos_of_pos hR
  have hFe : F = U + V - W := boundary_numerator R q w hw0
  have hVe : V = F - U + W := by linarith only [hFe]
  obtain ⟨hu, hz⟩ := boundary_tanh_parameters hq
  change u ∈ Ioo 0 1 at hu
  change z ∈ Ioo 0 1 at hz
  have hb := (boundary_parameters_pos hu hz).2.1
  have hc := (boundary_cd_pos hu hz).1
  obtain ⟨hQ, hE, hV⟩ := boundary_tanh_formulas hq
  change Real.tanh q = T * (1 - z) / (1 - u * z) at hQ
  change Real.tanh (2 * q - R) = T * (1 - 2 * z + u * z ^ 2) / (1 - 2 * u * z + u * z ^ 2) at hE
  change Real.tanh (R - q) = T * z at hV
  have hCQ : coth (R - q) = 1 / (T * z) := by rw [coth_eq_inv_tanh, hV]
  have hCR : coth R = 1 / T := coth_eq_inv_tanh R
  have hqb := hasDerivAt_boundaryObjective_q hq.2 hw0 hF.ne'
  have hRb := hasDerivAt_boundaryObjective_R hR hq.2 hw0 hF.ne'
  have hpb := hasDerivAt_boundaryObjective_p hR hr hF.ne'
  refine ⟨?_, ?_, ?_⟩
  · convert hqb using 1
    conv_rhs => rw [hQ, hE, hV, hCQ]
    change T * boundaryQNormalized u z t (2 * U / F - 1) (2 * W / F) =
      4 * (1 - w) * (U * (T * (1 - z) / (1 - u * z)) - V * (T * z) + W * (1 / (T * z))) / F -
        2 * (1 - w) * (T * (1 - 2 * z + u * z ^ 2) / (1 - 2 * u * z + u * z ^ 2))
    rw [hVe]
    unfold boundaryQNormalized
    dsimp [u, t] at *
    field_simp [hF.ne', hT.ne', hz.1.ne', hb.ne', hc.ne'] <;> ring
  · convert hRb using 1
    conv_rhs => rw [hV, hCQ, hCR, hE]
    change T * boundaryRNormalized u z t (2 * U / F - 1) (2 * W / F) =
      (V * (4 * w * T + 4 * (1 - w) * (T * z)) -
        W * (4 * w * (1 / T) + 4 * (1 - w) * (1 / (T * z)))) / F -
          (1 + w) * T + (1 - w) * (T * (1 - 2 * z + u * z ^ 2) / (1 - 2 * u * z + u * z ^ 2))
    rw [hVe]
    unfold boundaryRNormalized
    dsimp [u, t] at *
    field_simp [hF.ne', hT.ne', hz.1.ne', hb.ne', hc.ne'] <;> ring
  · convert hpb using 1
    rw [hCR]
    change 2 * w * T * (2 * U / F - 1 + (1 - u) / u * (2 * W / F)) =
      4 * w * (-T * V + (1 / T) * W) / F + 2 * w * T
    rw [hVe]
    dsimp [u]
    field_simp [hF.ne', hT.ne'] <;> ring

/-- The complete boundary exclusion, retaining the permitted one-sided scale
condition instead of imposing a stationary scale. -/
theorem boundary_inward_deriv_negative {R q w : ℝ}
    (hq : q ∈ Ioo 0 R) (hw : w ∈ Ioo (1 / 4) (1 / 2))
    (hQ : deriv (fun q => twoPointObjective R 0 q w) q = 0)
    (hR : deriv (fun R => twoPointObjective R 0 q w) R ≤ 0) :
    deriv (fun p => twoPointObjective R p q w) 0 < 0 := by
  obtain ⟨hq', hR', hp'⟩ := boundary_actual_derivatives hq hw
  rw [hq'.deriv] at hQ
  rw [hR'.deriv] at hR
  rw [hp'.deriv]
  have hT := tanh_pos_of_pos (hq.1.trans hq.2)
  obtain ⟨hu, hz⟩ := boundary_tanh_parameters hq
  have ht : 1 < 2 * (1 - w) := by linarith [hw.2]
  have hQ' := (mul_eq_zero.mp hQ).resolve_left hT.ne'
  have hR' := nonpos_of_mul_nonpos_right hR hT
  exact mul_neg_of_pos_of_neg
    (mul_pos (mul_pos (by norm_num) ((by norm_num : (0 : ℝ) < 1 / 4).trans hw.1)) hT)
    (boundary_direct_inward_negative hu hz ht hR' hQ')

end PaperVerification.Hyperbolic

#print axioms PaperVerification.Hyperbolic.boundary_actual_derivatives
#print axioms PaperVerification.Hyperbolic.boundary_inward_deriv_negative
end
end Source_HyperbolicBoundaryActual
-- END ORIGINAL PaperVerification.HyperbolicBoundaryActual


-- BEGIN ORIGINAL PaperVerification.HyperbolicKernel
section Source_HyperbolicKernel

-- original header: module
-- original header: public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
-- original header: public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
-- original header: public import Mathlib.Tactic.FieldSimp
-- original header: public import Mathlib.Tactic.Ring
-- original header: public import Mathlib.Tactic.Linarith
-- original header: @[expose] public section
/-! # Exact resolvent algebra and reciprocal comparison

These are equations (20)--(22) and the pointwise sign comparison in Section 5.2.
The formulas are proved for arbitrary real parameters in their stated domains.
-/

noncomputable section

namespace PaperVerification.Hyperbolic

open Real Set MeasureTheory intervalIntegral

/-- The quartic transform appearing after the exponential coordinate change. -/
def quarticTransform (z : ℝ) (f : ℝ → ℝ) : ℝ :=
  (f z - f (-z) + z ^ 4 * (f (1 / z) - f (-1 / z))) / (z + z ^ 3)

/-- All quartic polynomials have transform independent of z. -/
theorem quarticTransform_polynomial (z p₀ p₁ p₂ p₃ p₄ : ℝ) (hz : z ≠ 0) :
    quarticTransform z (fun t => p₀ + p₁ * t + p₂ * t ^ 2 + p₃ * t ^ 3 + p₄ * t ^ 4) =
      2 * (p₁ + p₃) := by
  have hd : z + z ^ 3 ≠ 0 := by
    have hf : z + z ^ 3 = z * (1 + z ^ 2) := by ring
    rw [hf]
    exact mul_ne_zero hz (ne_of_gt (by nlinarith only [sq_nonneg z]))
  unfold quarticTransform
  field_simp [hz, hd]
  ring

/-- Resolvent transform as a rational function of x=z². -/
def resolventKernel (s x : ℝ) : ℝ :=
  -2 / s ^ 2 + (2 * (s ^ 2 - 1) / s ^ 2) * (x / ((s ^ 2 - x) * (1 - s ^ 2 * x)))

def resolventSlope (s x : ℝ) : ℝ :=
  2 * (s ^ 2 - 1) * (1 - x ^ 2) / ((s ^ 2 - x) ^ 2 * (1 - s ^ 2 * x) ^ 2)

theorem quarticTransform_resolvent (s z : ℝ) (hs : s ≠ 0) (hz : z ≠ 0)
    (h₁ : s ^ 2 - z ^ 2 ≠ 0) (h₂ : 1 - s ^ 2 * z ^ 2 ≠ 0) :
    quarticTransform z (fun t => 1 / (t + s)) = resolventKernel s (z ^ 2) := by
  have hsp : z + s ≠ 0 := by
    intro h
    apply h₁
    rw [show s = -z by linarith]
    ring
  have hsm : -z + s ≠ 0 := by
    intro h
    apply h₁
    rw [show s = z by linarith]
    ring
  have hsz : 1 / z + s ≠ 0 := by
    intro h
    apply h₂
    have hh := congrArg (fun t : ℝ => t * z) h
    field_simp [hz] at hh
    nlinarith [sq_nonneg (s * z + 1)]
  have hsz' : -1 / z + s ≠ 0 := by
    intro h
    apply h₂
    have hh := congrArg (fun t : ℝ => t * z) h
    field_simp [hz] at hh
    nlinarith [sq_nonneg (s * z - 1)]
  have hd : z + z ^ 3 ≠ 0 := by
    rw [show z + z ^ 3 = z * (1 + z ^ 2) by ring]
    exact mul_ne_zero hz (ne_of_gt (by nlinarith only [sq_nonneg z]))
  have hplus : 1 + s * z ≠ 0 := by
    intro h
    apply h₂
    rw [← mul_pow, show s * z = -1 by linarith]
    norm_num
  have hminus : -1 + s * z ≠ 0 := by
    intro h
    apply h₂
    rw [← mul_pow, show s * z = 1 by linarith]
    norm_num
  unfold quarticTransform resolventKernel
  field_simp [hs, hz, h₁, h₂, hsp, hsm, hsz, hsz', hd, hplus, hminus] <;>
    (try field_simp [hs, hz, h₁, h₂, hsp, hsm, hsz, hsz', hd, hplus, hminus]) <;> ring

theorem hasDerivAt_resolventKernel (s x : ℝ) (hs : s ≠ 0)
    (h₁ : s ^ 2 - x ≠ 0) (h₂ : 1 - s ^ 2 * x ≠ 0) :
    HasDerivAt (resolventKernel s) (resolventSlope s x) x := by
  have hleft := (hasDerivAt_id x).const_sub (s ^ 2)
  have hright := ((hasDerivAt_id x).const_mul (s ^ 2)).const_sub 1
  have hden := hleft.mul hright
  have hquot := (hasDerivAt_id x).div hden (mul_ne_zero h₁ h₂)
  convert (hasDerivAt_const x (-2 / s ^ 2)).add
    (hquot.const_mul (2 * (s ^ 2 - 1) / s ^ 2)) using 1 <;>
    (try funext t) <;>
    (try simp only [resolventKernel, resolventSlope, Pi.mul_apply, Pi.add_apply,
      Pi.div_apply, Pi.sub_apply, id_eq]) <;>
    field_simp [hs, h₁, h₂] <;> ring

/-- The exact reciprocity factor, including its negative sign. -/
theorem resolventSlope_reciprocal (s x : ℝ) (hs : s ≠ 0)
    (h₁ : s ^ 2 - x ≠ 0) (h₂ : 1 - s ^ 2 * x ≠ 0) :
    resolventSlope (1 / s) x = -(s ^ 6) * resolventSlope s x := by
  have hd₁ : (1 / s) ^ 2 - x = (1 - s ^ 2 * x) / s ^ 2 := by field_simp [hs] <;> ring
  have hd₂ : 1 - (1 / s) ^ 2 * x = (s ^ 2 - x) / s ^ 2 := by field_simp [hs] <;> ring
  unfold resolventSlope
  rw [hd₁, hd₂]
  field_simp [hs, h₁, h₂] <;> ring

theorem resolventSlope_pos {s x : ℝ} (hs : 1 < s) (hx : |x| < 1)
    (h₁ : s ^ 2 - x ≠ 0) (h₂ : 1 - s ^ 2 * x ≠ 0) : 0 < resolventSlope s x := by
  apply div_pos
  · have hx2 : x ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one x).mpr hx
    exact mul_pos (mul_pos (by norm_num) (by nlinarith only [hs])) (by linarith)
  · exact mul_pos (sq_pos_of_ne_zero h₁) (sq_pos_of_ne_zero h₂)

theorem resolventSlope_neg {s x : ℝ} (hs₀ : 0 ≤ s) (hs₁ : s < 1) (hx : |x| < 1)
    (h₁ : s ^ 2 - x ≠ 0) (h₂ : 1 - s ^ 2 * x ≠ 0) : resolventSlope s x < 0 := by
  apply div_neg_of_neg_of_pos
  · have hx2 : x ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one x).mpr hx
    have hs2 : s ^ 2 < 1 := by nlinarith only [hs₀, hs₁]
    exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num) (by linarith)) (by linarith)
  · exact mul_pos (sq_pos_of_ne_zero h₁) (sq_pos_of_ne_zero h₂)

/-- Density arising from the compact Stieltjes representation. -/
def branchDensity (a b r s : ℝ) : ℝ := (s - a) ^ r * (b - s) ^ (4 - r)

theorem branchDensity_pos {a b r s : ℝ} (hs : s ∈ Ioo a b) :
    0 < branchDensity a b r s :=
  mul_pos (Real.rpow_pos_of_pos (sub_pos.mpr hs.1) _)
    (Real.rpow_pos_of_pos (sub_pos.mpr hs.2) _)

theorem branchDensity_nonneg {a b r s : ℝ} (hs : s ∈ Icc a b) :
    0 ≤ branchDensity a b r s :=
  mul_nonneg (Real.rpow_nonneg (sub_nonneg.mpr hs.1) _)
    (Real.rpow_nonneg (sub_nonneg.mpr hs.2) _)

theorem continuous_branchDensity (a b r : ℝ) (hr : r ∈ Ioo 0 4) :
    Continuous (branchDensity a b r) :=
  ((continuous_id.sub continuous_const).rpow_const (fun _ => Or.inr hr.1.le)).mul
    ((continuous_const.sub continuous_id).rpow_const (fun _ => Or.inr (sub_pos.mpr hr.2).le))

/-- The strict reciprocal density comparison, for the full parameter range r<2. -/
theorem branchDensity_lt_reciprocal
    {a b r s : ℝ} (ha : 0 < a) (hab : a * b < 1)
    (hr : r ∈ Ioo 0 2) (hs : s ∈ Ioo 1 b) :
    branchDensity a b r s < s ^ 4 * branchDensity a b r (1 / s) := by
  have hs0 : 0 < s := lt_trans zero_lt_one hs.1
  have hb0 : 0 < b := hs0.trans hs.2
  have ha1 : a < 1 := by nlinarith [mul_pos ha (sub_pos.mpr (lt_trans hs.1 hs.2))]
  have has : a * s < 1 := by nlinarith [mul_pos ha (sub_pos.mpr hs.2)]
  have hC : 0 < 1 - a * s := sub_pos.mpr has
  have hB : 0 < b - s := sub_pos.mpr hs.2
  have hA : 0 < s - a := by linarith only [ha1, hs.1]
  have hD : 0 < b * s - 1 := by nlinarith [mul_pos (sub_pos.mpr hs.1) hb0]
  let U : ℝ := (s - a) / (1 - a * s)
  let V : ℝ := (b * s - 1) / (b - s)
  have hU : 1 < U := by
    apply (lt_div_iff₀ hC).mpr
    have hp := mul_pos (sub_pos.mpr hs.1) (by linarith : 0 < 1 + a)
    nlinarith
  have hVU : V - U = (1 - a * b) * (s ^ 2 - 1) / ((b - s) * (1 - a * s)) := by
    dsimp [U, V]
    rw [div_sub_div _ _ hB.ne' hC.ne']
    congr 1 <;> ring
  have hUV : U < V := by
    apply sub_pos.mp
    rw [hVU]
    exact div_pos (mul_pos (sub_pos.mpr hab) (by nlinarith only [hs.1])) (mul_pos hB hC)
  have hV : 1 < V := hU.trans hUV
  have hpowers : U ^ r < V ^ (4 - r) :=
    (Real.rpow_lt_rpow (lt_trans zero_lt_one hU).le hUV hr.1).trans
      (Real.rpow_lt_rpow_of_exponent_lt hV (by linarith [hr.2]))
  have hfactor : 0 < (1 - a * s) ^ r * (b - s) ^ (4 - r) :=
    mul_pos (Real.rpow_pos_of_pos hC _) (Real.rpow_pos_of_pos hB _)
  have hleft : branchDensity a b r s =
      ((1 - a * s) ^ r * (b - s) ^ (4 - r)) * U ^ r := by
    have hprod : (1 - a * s) * U = s - a := by dsimp [U]; field_simp [hC.ne']
    unfold branchDensity
    rw [← hprod, Real.mul_rpow hC.le (lt_trans zero_lt_one hU).le]
    ring
  have hright : s ^ 4 * branchDensity a b r (1 / s) =
      ((1 - a * s) ^ r * (b - s) ^ (4 - r)) * V ^ (4 - r) := by
    have h₁ : 1 / s - a = (1 - a * s) / s := by field_simp [hs0.ne'] <;> ring
    have h₂ : b - 1 / s = (b * s - 1) / s := by field_simp [hs0.ne'] <;> ring
    have hprod : (b - s) * V = b * s - 1 := by dsimp [V]; field_simp [hB.ne']
    have hsPow : s ^ r * s ^ (4 - r) = s ^ (4 : ℕ) := by
      rw [← Real.rpow_add hs0, show r + (4 - r) = (4 : ℝ) by ring]
      exact Real.rpow_natCast s 4
    unfold branchDensity
    rw [h₁, h₂, Real.div_rpow hC.le hs0.le, Real.div_rpow hD.le hs0.le,
      div_mul_div_comm, hsPow, ← hprod, Real.mul_rpow hB.le (lt_trans zero_lt_one hV).le]
    field_simp [hs0.ne'] <;> ring
  rw [hleft, hright]
  exact mul_lt_mul_of_pos_left hpowers hfactor

/-- In reciprocal coordinates the combined kernel contribution is strictly negative. -/
theorem paired_resolventSlope_neg
    {a b r s x : ℝ} (ha : 0 < a) (hab : a * b < 1)
    (hr : r ∈ Ioo 0 2) (hs : s ∈ Ioo 1 b) (hx : |x| < 1)
    (h₁ : s ^ 2 - x ≠ 0) (h₂ : 1 - s ^ 2 * x ≠ 0) :
    resolventSlope s x * (branchDensity a b r s - s ^ 4 * branchDensity a b r (1 / s)) < 0 :=
  mul_neg_of_pos_of_neg (resolventSlope_pos hs.1 hx h₁ h₂)
    (sub_neg.mpr (branchDensity_lt_reciprocal ha hab hr hs))

end PaperVerification.Hyperbolic

#print axioms PaperVerification.Hyperbolic.quarticTransform_polynomial
#print axioms PaperVerification.Hyperbolic.hasDerivAt_resolventKernel
#print axioms PaperVerification.Hyperbolic.branchDensity_lt_reciprocal
end
end Source_HyperbolicKernel
-- END ORIGINAL PaperVerification.HyperbolicKernel


-- BEGIN ORIGINAL PaperVerification.HyperbolicKernelIntegral
section Source_HyperbolicKernelIntegral

-- original header: module
-- original header: public import PaperVerification.HyperbolicKernel
-- original header: public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
-- original header: @[expose] public section
/-! # Sign of the full resolvent integral

The reciprocal pairing is carried out for the actual interval integral, including
the part below `1 / b`.  All statements retain the open parameter ranges from
Section 5.2 of the paper.
-/

noncomputable section

namespace PaperVerification.Hyperbolic

open Real Set MeasureTheory intervalIntegral

theorem resolvent_denominators_pos {a b x s : ℝ}
    (ha : 0 < a) (hx : 0 < x) (hxa : x < a ^ 2) (hxb : b ^ 2 * x < 1)
    (hs : s ∈ Icc a b) : 0 < s ^ 2 - x ∧ 0 < 1 - s ^ 2 * x := by
  have hs0 : 0 < s := ha.trans_le hs.1
  have hb0 : 0 < b := hs0.trans_le hs.2
  have has : a ^ 2 ≤ s ^ 2 := (sq_le_sq₀ ha.le hs0.le).mpr hs.1
  have hsb : s ^ 2 ≤ b ^ 2 := (sq_le_sq₀ hs0.le hb0.le).mpr hs.2
  constructor
  · linarith
  · have := mul_le_mul_of_nonneg_right hsb hx.le
    linarith

theorem continuousOn_resolventSlope {a b x : ℝ}
    (ha : 0 < a) (hx : 0 < x) (hxa : x < a ^ 2) (hxb : b ^ 2 * x < 1) :
    ContinuousOn (fun s => resolventSlope s x) (Icc a b) := by
  unfold resolventSlope
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro s hs
    obtain ⟨h₁, h₂⟩ := resolvent_denominators_pos ha hx hxa hxb hs
    exact mul_ne_zero (pow_ne_zero _ h₁.ne') (pow_ne_zero _ h₂.ne')

theorem continuousOn_density_resolventSlope {a b r x : ℝ}
    (ha : 0 < a) (hr : r ∈ Ioo 0 2) (hx : 0 < x)
    (hxa : x < a ^ 2) (hxb : b ^ 2 * x < 1) :
    ContinuousOn (fun s => branchDensity a b r s * resolventSlope s x) (Icc a b) :=
  (continuous_branchDensity a b r ⟨hr.1, by linarith [hr.2]⟩).continuousOn.mul
    (continuousOn_resolventSlope ha hx hxa hxb)

/-- The reciprocal substitution, with the Jacobian and orientation made explicit. -/
theorem integral_reciprocal_one {b : ℝ} (hb : 1 ≤ b) (f : ℝ → ℝ) :
    (∫ s in 1..b, f (1 / s) / s ^ 2) = ∫ s in (1 / b)..1, f s := by
  have hnz : ∀ s ∈ uIcc (1 : ℝ) b, s ≠ 0 := by
    rw [uIcc_of_le hb]
    intro s hs
    linarith [hs.1]
  have hc : ContinuousOn (fun s : ℝ => 1 / s) (uIcc 1 b) :=
    continuousOn_const.div continuousOn_id (fun s hs => hnz s hs)
  have hd : ∀ s ∈ Ioo (min (1 : ℝ) b) (max 1 b),
      HasDerivAt (fun s : ℝ => 1 / s) (-(1 / s ^ 2)) s := by
    intro s hs
    have hs0 : s ≠ 0 := by
      rw [min_eq_left hb, max_eq_right hb] at hs
      linarith [hs.1]
    simpa only [one_div] using hasDerivAt_inv hs0
  have hm : ∀ s ∈ Ioo (min (1 : ℝ) b) (max 1 b), -(1 / s ^ 2) ≤ 0 := by
    intro s _
    exact neg_nonpos.mpr (div_nonneg zero_le_one (sq_nonneg s))
  have h := integral_comp_mul_deriv_of_deriv_nonpos (g := f) hc hd hm
  have hfun : (fun s : ℝ => (f ∘ fun s => 1 / s) s * -(1 / s ^ 2)) =
      fun s => -(f (1 / s) / s ^ 2) := by
    funext s
    simp only [Function.comp_apply]
    ring
  rw [hfun, intervalIntegral.integral_neg, one_div_one, integral_symm (1 / b) 1] at h
  exact neg_injective h

theorem integral_resolventSlope_negative_below_one
    {a b r x : ℝ} (ha : 0 < a) (hab : a < b) (hb : b ≤ 1)
    (hr : r ∈ Ioo 0 2) (hx : 0 < x) (hxa : x < a ^ 2) (hxb : b ^ 2 * x < 1) :
    (∫ s in a..b, branchDensity a b r s * resolventSlope s x) < 0 := by
  have hax : a < 1 := hab.trans_le hb
  have hx1 : |x| < 1 := by
    rw [abs_of_pos hx]
    nlinarith only [ha, hax, hxa]
  have hcont := continuousOn_density_resolventSlope ha hr hx hxa hxb
  have hnonpos : ∀ s ∈ Icc a b, branchDensity a b r s * resolventSlope s x ≤ 0 := by
    intro s hs
    obtain ⟨h₁, h₂⟩ := resolvent_denominators_pos ha hx hxa hxb hs
    have hs1 : s ≤ 1 := hs.2.trans hb
    rcases hs1.eq_or_lt with hs1 | hs1
    · subst s
      simp [resolventSlope]
    · exact mul_nonpos_of_nonneg_of_nonpos (branchDensity_nonneg hs)
        (resolventSlope_neg (ha.le.trans hs.1) hs1 hx1 h₁.ne' h₂.ne').le
  have hpos : 0 < ∫ s in a..b, -(branchDensity a b r s * resolventSlope s x) := by
    refine integral_pos hab hcont.neg (fun s hs => neg_nonneg.mpr (hnonpos s ⟨hs.1.le, hs.2⟩)) ?_
    let m := (a + b) / 2
    have hm : m ∈ Ioo a b := by dsimp [m]; constructor <;> linarith
    obtain ⟨h₁, h₂⟩ := resolvent_denominators_pos ha hx hxa hxb ⟨hm.1.le, hm.2.le⟩
    exact ⟨m, ⟨hm.1.le, hm.2.le⟩, neg_pos.mpr
      (mul_neg_of_pos_of_neg (branchDensity_pos hm)
        (resolventSlope_neg (ha.le.trans hm.1.le) (hm.2.trans_le hb) hx1 h₁.ne' h₂.ne'))⟩
  rw [intervalIntegral.integral_neg] at hpos
  linarith

/-- Strict negativity of equation (22), for every admissible real parameter. -/
theorem integral_resolventSlope_neg
    {a b r x : ℝ} (ha : 0 < a) (hab : a < b) (hab1 : a * b < 1)
    (hr : r ∈ Ioo 0 2) (hx : 0 < x) (hxa : x < a ^ 2) (hxb : b ^ 2 * x < 1) :
    (∫ s in a..b, branchDensity a b r s * resolventSlope s x) < 0 := by
  by_cases hb : b ≤ 1
  · exact integral_resolventSlope_negative_below_one ha hab hb hr hx hxa hxb
  have hb1 : 1 < b := lt_of_not_ge hb
  have hb0 : 0 < b := zero_lt_one.trans hb1
  have hai : a < 1 / b := (lt_div_iff₀ hb0).mpr (by simpa using hab1)
  have hi0 : 0 < 1 / b := div_pos zero_lt_one hb0
  have hi1 : 1 / b < 1 := (div_lt_iff₀ hb0).mpr (by simpa using hb1)
  have ha1 : a < 1 := hai.trans hi1
  have hx1 : |x| < 1 := by
    rw [abs_of_pos hx]
    nlinarith only [ha, ha1, hxa]
  let f : ℝ → ℝ := fun s => branchDensity a b r s * resolventSlope s x
  let paired : ℝ → ℝ := fun s =>
    resolventSlope s x * (branchDensity a b r s - s ^ 4 * branchDensity a b r (1 / s))
  have hcont : ContinuousOn f (Icc a b) := continuousOn_density_resolventSlope ha hr hx hxa hxb
  have hsub₁ : Icc a (1 / b) ⊆ Icc a b := fun s hs => ⟨hs.1, hs.2.trans (hi1.le.trans hb1.le)⟩
  have hsub₂ : Icc (1 / b) 1 ⊆ Icc a b := fun s hs => ⟨hai.le.trans hs.1, hs.2.trans hb1.le⟩
  have hsub₃ : Icc 1 b ⊆ Icc a b := fun s hs => ⟨ha1.le.trans hs.1, hs.2⟩
  have hi₁ : IntervalIntegrable f volume a (1 / b) := (hcont.mono hsub₁).intervalIntegrable_of_Icc hai.le
  have hi₂ : IntervalIntegrable f volume (1 / b) 1 := (hcont.mono hsub₂).intervalIntegrable_of_Icc hi1.le
  have hi₃ : IntervalIntegrable f volume 1 b := (hcont.mono hsub₃).intervalIntegrable_of_Icc hb1.le
  have hrec : ∀ s ∈ Icc 1 b, 1 / s ∈ Icc a b := by
    intro s hs
    have hs0 : 0 < s := zero_lt_one.trans_le hs.1
    constructor
    · apply (le_div_iff₀ hs0).mpr
      have := mul_le_mul_of_nonneg_left hs.2 ha.le
      linarith
    · apply (div_le_iff₀ hs0).mpr
      have := mul_le_mul_of_nonneg_left hs.1 hb0.le
      linarith
  have hreccont : ContinuousOn (fun s : ℝ => 1 / s) (Icc 1 b) :=
    continuousOn_const.div continuousOn_id (fun s hs => by linarith [hs.1])
  have hrecf : ContinuousOn (fun s => f (1 / s) / s ^ 2) (Icc 1 b) :=
    (hcont.comp hreccont hrec).div (continuousOn_id.pow 2)
      (fun s hs => pow_ne_zero _ (by linarith [hs.1]))
  have hpair : ∀ s ∈ Icc 1 b, f s + f (1 / s) / s ^ 2 = paired s := by
    intro s hs
    obtain ⟨h₁, h₂⟩ := resolvent_denominators_pos ha hx hxa hxb (hsub₃ hs)
    have hs0 : s ≠ 0 := by linarith [hs.1]
    dsimp [f, paired]
    rw [resolventSlope_reciprocal s x hs0 h₁.ne' h₂.ne']
    field_simp [hs0]
    ring
  have hpairint : (∫ s in (1 / b)..1, f s) + (∫ s in 1..b, f s) =
      ∫ s in 1..b, paired s := by
    rw [← integral_reciprocal_one hb1.le f, add_comm,
      ← intervalIntegral.integral_add hi₃ (hrecf.intervalIntegrable_of_Icc hb1.le)]
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hb1.le]
    exact hpair
  have hpairnonpos : (∫ s in 1..b, paired s) ≤ 0 := by
    have hnonneg : 0 ≤ ∫ s in 1..b, -paired s := by
      apply integral_nonneg hb1.le
      intro s hs
      apply neg_nonneg.mpr
      obtain ⟨h₁, h₂⟩ := resolvent_denominators_pos ha hx hxa hxb (hsub₃ hs)
      rcases hs.1.eq_or_lt with hs1 | hs1
      · rw [← hs1]
        simp [paired, resolventSlope]
      · rcases hs.2.eq_or_lt with hsb | hsb
        · subst s
          have hρ : 0 ≤ branchDensity a b r (1 / b) := branchDensity_nonneg (hrec b ⟨hb1.le, le_rfl⟩)
          have hρb : branchDensity a b r b = 0 := by
            simp [branchDensity, Real.zero_rpow (by linarith [hr.2] : 4 - r ≠ 0)]
          dsimp [paired]
          rw [hρb]
          exact mul_nonpos_of_nonneg_of_nonpos
            (resolventSlope_pos hb1 hx1 h₁.ne' h₂.ne').le
            (by simpa only [zero_sub] using
              neg_nonpos.mpr (mul_nonneg (pow_nonneg hb0.le 4) hρ))
        · exact (paired_resolventSlope_neg ha hab1 hr ⟨hs1, hsb⟩ hx1 h₁.ne' h₂.ne').le
    rw [intervalIntegral.integral_neg] at hnonneg
    linarith
  have hleft : (∫ s in a..(1 / b), f s) < 0 := by
    have hnonpos : ∀ s ∈ Icc a (1 / b), f s ≤ 0 := by
      intro s hs
      obtain ⟨h₁, h₂⟩ := resolvent_denominators_pos ha hx hxa hxb (hsub₁ hs)
      exact mul_nonpos_of_nonneg_of_nonpos (branchDensity_nonneg (hsub₁ hs))
        (resolventSlope_neg (ha.le.trans hs.1) (hs.2.trans_lt hi1) hx1 h₁.ne' h₂.ne').le
    have hpos : 0 < ∫ s in a..(1 / b), -f s := by
      refine integral_pos hai (hcont.mono hsub₁).neg
        (fun s hs => neg_nonneg.mpr (hnonpos s ⟨hs.1.le, hs.2⟩)) ?_
      let m := (a + 1 / b) / 2
      have hm : m ∈ Ioo a (1 / b) := by dsimp [m]; constructor <;> linarith
      have hmb : m ∈ Ioo a b := ⟨hm.1, hm.2.trans (hi1.trans hb1)⟩
      obtain ⟨h₁, h₂⟩ := resolvent_denominators_pos ha hx hxa hxb ⟨hmb.1.le, hmb.2.le⟩
      exact ⟨m, ⟨hm.1.le, hm.2.le⟩, neg_pos.mpr
        (mul_neg_of_pos_of_neg (branchDensity_pos hmb)
          (resolventSlope_neg (ha.le.trans hm.1.le) (hm.2.trans hi1) hx1 h₁.ne' h₂.ne'))⟩
    rw [intervalIntegral.integral_neg] at hpos
    linarith
  have hsplit := integral_add_adjacent_intervals (hi₁.trans hi₂) hi₃
  rw [← integral_add_adjacent_intervals hi₁ hi₂, add_assoc, hpairint] at hsplit
  change (∫ s in a..b, f s) < 0
  linarith

end PaperVerification.Hyperbolic

#print axioms PaperVerification.Hyperbolic.integral_resolventSlope_neg
end
end Source_HyperbolicKernelIntegral
-- END ORIGINAL PaperVerification.HyperbolicKernelIntegral


-- Kernel-environment audit: every mathematical source body precedes this command.
set_option maxHeartbeats 0 in
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let kenv := env.checked.get
  let entries := kenv.constants.foldStage2
    (fun rows name ci => rows.push (name, ci)) (#[] : Array (Name × ConstantInfo))
  let kind : ConstantInfo → String := fun ci => match ci with
    | .axiomInfo _ => "axiom"
    | .defnInfo _ => "definition"
    | .thmInfo _ => "theorem"
    | .opaqueInfo _ => "opaque"
    | .quotInfo _ => "quotient"
    | .ctorInfo _ => "constructor"
    | .recInfo _ => "recursor"
    | .inductInfo _ => "inductive"
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut rows : Array Json := #[]
  let mut failures : Array Json := #[]
  for (name, ci) in entries do
    if ci.isUnsafe then
      failures := failures.push (Json.mkObj [
        ("declaration", toJson name.toString),
        ("unsafe_declaration", toJson true)])
    let deps := ci.getUsedConstantsAsSet.toArray.qsort Name.lt
    let mut dependencyRows : Array Json := #[]
    for dep in deps do
      match kenv.find? dep with
      | none =>
        failures := failures.push (Json.mkObj [
          ("declaration", toJson name.toString),
          ("missing_dependency", toJson dep.toString)])
      | some info =>
        let origin := match env.getModuleIdxFor? dep with
          | some idx => env.header.moduleNames[idx]!.toString
          | none => env.mainModule.toString
        dependencyRows := dependencyRows.push (Json.mkObj [
          ("name", toJson dep.toString), ("kind", toJson (kind info)),
          ("module", toJson origin)])
    let axioms ← Lean.collectAxioms name
    let bad := axioms.filter (fun ax => !allowed.contains ax)
    if !bad.isEmpty then
      failures := failures.push (Json.mkObj [
        ("declaration", toJson name.toString),
        ("unapproved_axioms", toJson (bad.map Name.toString))])
    rows := rows.push (Json.mkObj [
      ("name", toJson name.toString), ("kind", toJson (kind ci)),
      ("unsafe", toJson ci.isUnsafe),
      ("type", toJson (toString ci.type)),
      ("level_parameters", toJson (ci.levelParams.map Name.toString)),
      ("has_body", toJson (ci.value? (allowOpaque := true)).isSome),
      ("dependencies", Json.arr dependencyRows),
      ("axioms", toJson (axioms.map Name.toString))])
  let sourceHash ← IO.getEnv "PAPER_VERIFICATION_SOURCE_SHA256"
  let fingerprint ← IO.getEnv "PAPER_VERIFICATION_FINGERPRINT"
  let document := Json.mkObj [
    ("schema", toJson (1 : Nat)),
    ("module", toJson env.mainModule.toString),
    ("source_sha256", toJson sourceHash),
    ("fingerprint", toJson fingerprint),
    ("kernel_environment", toJson true),
    ("declarations", Json.arr rows),
    ("failures", Json.arr failures),
    ("passed", toJson failures.isEmpty)]
  let target := (← IO.getEnv "PAPER_VERIFICATION_AUDIT_PATH").getD ".lake/build/paper-audit/PaperVerification_Lattice001.json"
  let path : System.FilePath := target
  if let some parent := path.parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile path (document.compress ++ "\n")
  if !failures.isEmpty then
    throwError "Kernel declaration audit rejected {failures.size} dependency/axiom findings; see {target}"
  logInfo m!"Kernel declaration audit passed for {rows.size} declarations; see {target}"
