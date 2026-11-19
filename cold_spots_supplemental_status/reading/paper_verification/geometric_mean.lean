module
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
@[expose] public section
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
