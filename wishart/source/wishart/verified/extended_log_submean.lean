module

public import wishart.verified.field_frontier02

@[expose] public section

/-!
# Logarithmic submean inequalities with zero values

For a continuous nonnegative function, the extended logarithm takes the
value −∞ at zero.  On a ball where `log f ≤ M`, its submean inequality is
exactly the inequality saying that the average of `M - log f` is at most its
value at the center.  We express that nonnegative defect in `ℝ≥0∞`, assigning
∞ at a zero of `f`.  This avoids using `Real.log 0`, which is not −∞, and
avoids any undefined difference of infinite integrals.

The literal extended inequality implies a finite logarithmic submean
inequality for `max f ε`.  Positive finite products can then decrease to the
original product, including its zeros.  No monotonicity in a matrix ridge
and no differentiability assumption is used.
-/

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal BigOperators

namespace WishartVerification

/-- The nonnegative defect from an upper bound for the extended logarithm.
On the nonnegative domain, the exceptional value is exactly `M - (-∞)`. -/
def extendedLogDefect (M a : ℝ) : ℝ≥0∞ :=
  if a = 0 then ∞ else ENNReal.ofReal (M - Real.log a)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The extended logarithmic submean inequality, written using its
nonnegative defect from any finite upper bound on the ball.  At a zero
center the right side is ∞, so the inequality has its usual automatic
meaning. Continuity of the nonnegative function supplies the upper
semicontinuity of its extended logarithm. -/
structure ExtendedLogSubmean (f : E → ℝ) : Prop where
  nonnegative : ∀ x, 0 ≤ f x
  continuous : Continuous f
  defect_average : ∀ (x : E) (r : ℝ), 0 < r → ∀ M : ℝ,
    (∀ y ∈ ball x r, f y ≤ Real.exp M) →
      (⨍⁻ y in ball x r, extendedLogDefect M (f y) ∂volume) ≤ extendedLogDefect M (f x)

/-- Finite positive logarithms satisfy the same extended formulation. -/
theorem PositiveLogSubmean.toExtendedLogSubmean {f : E → ℝ}
    (hf : PositiveLogSubmean f) : ExtendedLogSubmean f := by
  refine ⟨fun x => (hf.positive x).le, hf.continuous, ?_⟩
  intro x r hr M hbound
  have hnonneg : 0 ≤ᵐ[volume.restrict (ball x r)] (fun y => M - Real.log (f y)) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    exact sub_nonneg.mpr ((Real.log_le_iff_le_exp (hf.positive y)).mpr (hbound y hy))
  have hint : IntegrableOn (fun y => M - Real.log (f y)) (ball x r) :=
    continuous_integrableOn_ball (continuous_const.sub hf.logarithm.continuous) x r
  have heq : (fun y => extendedLogDefect M (f y)) =
      fun y => ENNReal.ofReal (M - Real.log (f y)) := by
    funext y
    rw [extendedLogDefect, if_neg (hf.positive y).ne']
  rw [heq, setLAverage_eq, ← ofReal_setAverage hint hnonneg,
    setAverage_fun_sub (continuous_integrableOn_ball (f := fun _ : E => M) continuous_const x r)
      (continuous_integrableOn_ball hf.logarithm.continuous x r),
    setAverage_const (measure_ball_pos volume x hr).ne' measure_ball_lt_top.ne,
    extendedLogDefect, if_neg (hf.positive x).ne']
  exact ENNReal.ofReal_le_ofReal (sub_le_sub_left (hf.logarithm.le_average x r hr) M)

/-- The identically zero factor is allowed, with logarithm identically −∞. -/
theorem ExtendedLogSubmean.zero : ExtendedLogSubmean (fun _ : E => (0 : ℝ)) := by
  refine ⟨fun _ => le_rfl, continuous_const, ?_⟩
  intro x r hr M hbound
  simp [extendedLogDefect]

theorem extendedLogDefect_truncation_le {a ε M : ℝ} (ha : 0 ≤ a) (hε : 0 < ε) :
    ENNReal.ofReal (M - Real.log (max a ε)) ≤ extendedLogDefect M a := by
  by_cases ha0 : a = 0
  · simp [extendedLogDefect, ha0]
  · rw [extendedLogDefect, if_neg ha0]
    exact ENNReal.ofReal_le_ofReal (sub_le_sub_left
      (Real.log_le_log (lt_of_le_of_ne ha (Ne.symm ha0)) (le_max_left a ε)) M)

theorem ExtendedLogSubmean.positive_truncation {f : E → ℝ}
    (hf : ExtendedLogSubmean f) {ε : ℝ} (hε : 0 < ε) :
    PositiveLogSubmean (fun x => max (f x) ε) := by
  have hp (x : E) : 0 < max (f x) ε := hε.trans_le (le_max_right _ _)
  have hc : Continuous (fun x => max (f x) ε) := hf.continuous.max continuous_const
  have hlog : Continuous (fun x => Real.log (max (f x) ε)) := hc.log (fun x => (hp x).ne')
  refine ⟨hp, hc, hlog, ?_⟩
  intro x r hr
  by_cases hxε : f x ≤ ε
  · rw [max_eq_right hxε]
    have hcst := (BallSubmean.const (E := E) (Real.log ε)).le_average x r hr
    exact hcst.trans (setAverage_mono_continuous continuous_const hlog
      (fun y => Real.log_le_log hε (le_max_right _ _)) x r)
  · have hεx : ε < f x := lt_of_not_ge hxε
    have hfx : 0 < f x := hε.trans hεx
    obtain ⟨a, ha, hmax⟩ := (isCompact_closedBall x r).exists_isMaxOn
      (show (closedBall x r).Nonempty from ⟨x, mem_closedBall_self hr.le⟩) hlog.continuousOn
    let M : ℝ := Real.log (max (f a) ε)
    have hbound (y : E) (hy : y ∈ ball x r) :
        Real.log (max (f y) ε) ≤ M := hmax (ball_subset_closedBall hy)
    have hupper (y : E) (hy : y ∈ ball x r) : f y ≤ Real.exp M := by
      calc
        f y ≤ max (f y) ε := le_max_left _ _
        _ = Real.exp (Real.log (max (f y) ε)) := (Real.exp_log (hp y)).symm
        _ ≤ Real.exp M := Real.exp_le_exp.mpr (hbound y hy)
    have hcenter : Real.log (f x) ≤ M := by
      simpa only [max_eq_left hεx.le] using hbound x (mem_ball_self hr)
    have hle : (⨍⁻ y in ball x r,
        ENNReal.ofReal (M - Real.log (max (f y) ε)) ∂volume) ≤
        ENNReal.ofReal (M - Real.log (f x)) := by
      calc
        _ ≤ ⨍⁻ y in ball x r, extendedLogDefect M (f y) ∂volume :=
          laverage_mono_ae (Eventually.of_forall fun y =>
            extendedLogDefect_truncation_le (hf.nonnegative y) hε)
        _ ≤ extendedLogDefect M (f x) := hf.defect_average x r hr M hupper
        _ = ENNReal.ofReal (M - Real.log (f x)) := by
          rw [extendedLogDefect, if_neg hfx.ne']
    have hint : IntegrableOn (fun y => M - Real.log (max (f y) ε)) (ball x r) :=
      continuous_integrableOn_ball (continuous_const.sub hlog) x r
    have hn : 0 ≤ᵐ[volume.restrict (ball x r)]
        (fun y => M - Real.log (max (f y) ε)) := by
      filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
      exact sub_nonneg.mpr (hbound y hy)
    rw [setLAverage_eq, ← ofReal_setAverage hint hn,
      setAverage_fun_sub (continuous_integrableOn_ball (f := fun _ : E => M) continuous_const x r)
        (continuous_integrableOn_ball hlog x r),
      setAverage_const (measure_ball_pos volume x hr).ne' measure_ball_lt_top.ne] at hle
    have hreal := (ENNReal.ofReal_le_ofReal_iff (sub_nonneg.mpr hcenter)).mp hle
    rw [max_eq_left hεx.le]
    linarith

/-- Products preserve the ordinary submean inequality even when their
factors vanish; the assumption concerns each factor's extended logarithm. -/
theorem ExtendedLogSubmean.finset_prod_ballSubmean {ι : Type*} (s : Finset ι)
    (f : ι → E → ℝ) (hf : ∀ i ∈ s, ExtendedLogSubmean (f i)) :
    BallSubmean (fun x => ∏ i ∈ s, f i x) := by
  classical
  let F (n : ℕ) (x : E) : ℝ := ∏ i ∈ s, max (f i x) (positiveRidge n)
  have hF (n : ℕ) : PositiveLogSubmean (F n) :=
    PositiveLogSubmean.finset_prod s (fun i x => max (f i x) (positiveRidge n))
      (fun i hi => (hf i hi).positive_truncation (positiveRidge_pos n))
  apply BallSubmean.of_nonnegative_antitone_limit (F := F)
    (fun n => (hF n).toBallSubmean)
  · exact continuous_finsetProd s (fun i hi => (hf i hi).continuous)
  · intro n x
    exact (hF n).positive x |>.le
  · intro x n m hnm
    apply Finset.prod_le_prod₀
    · intro i hi
      exact (positiveRidge_pos m).le.trans (le_max_right _ _)
    · intro i hi
      exact max_le_max le_rfl (positiveRidge_antitone hnm)
  · intro x
    have hlim : Tendsto (fun n => ∏ i ∈ s, max (f i x) (positiveRidge n)) atTop
        (𝓝 (∏ i ∈ s, max (f i x) 0)) := by
      apply tendsto_finsetProd
      intro i hi
      exact tendsto_const_nhds.max positiveRidge_tendsto
    have heq : (∏ i ∈ s, max (f i x) 0) = ∏ i ∈ s, f i x :=
      Finset.prod_congr rfl (fun i hi => max_eq_left ((hf i hi).nonnegative x))
    simpa only [heq] using hlim

end WishartVerification

end
