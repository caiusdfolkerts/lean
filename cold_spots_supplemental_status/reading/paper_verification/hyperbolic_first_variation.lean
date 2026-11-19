module
public import PaperVerification.HyperbolicMeasure
public import PaperVerification.GeometricMeanMix
public import PaperVerification.GeometricMeanLog
public import Mathlib.Analysis.Calculus.Deriv.Slope
@[expose] public section
/-! # First variation for arbitrary probability measures

All four geometric moments are varied exactly. Vanishing moments remain zero;
they are not differentiated through the undefined extended logarithm. The
resulting entropy identity proves that the lower first-variation bound is the
actual probability average of the potential.
-/

noncomputable section

namespace PaperVerification.Hyperbolic

open Real Set MeasureTheory Filter Topology

/-- The potential g associated to an arbitrary probability measure. -/
def measurePotential (R : ℝ) (μ : ProbabilityMeasure (Interval R)) (p : ℝ) : ℝ :=
  variationPotential R (geometricMoment 4 (intervalCosh R) μ)
    (geometricMoment 4 (intervalReflectedCosh R) μ)
    (geometricMoment 4 (intervalSinh R) μ)
    (geometricMoment 4 (intervalReflectedSinh R) μ) (hyperbolicNumerator R μ) p

/-- Its finite logarithmic-entropy average. -/
def potentialEntropy (R : ℝ) (μ : ProbabilityMeasure (Interval R)) : ℝ :=
  (geometricMoment 4 (intervalCosh R) μ * Real.log (geometricMoment 4 (intervalCosh R) μ) +
    geometricMoment 4 (intervalReflectedCosh R) μ * Real.log (geometricMoment 4 (intervalReflectedCosh R) μ) -
    geometricMoment 4 (intervalSinh R) μ * Real.log (geometricMoment 4 (intervalSinh R) μ) -
    geometricMoment 4 (intervalReflectedSinh R) μ * Real.log (geometricMoment 4 (intervalReflectedSinh R) μ)) /
      hyperbolicNumerator R μ - ∫ p, intervalCenteredLogCosh R p ∂μ

/-- Points where the first-variation potential has a finite endpoint limit. -/
def AdmissiblePoint (R : ℝ) (μ : ProbabilityMeasure (Interval R)) (p : Interval R) : Prop :=
  (geometricMoment 4 (intervalSinh R) μ = 0 ∨ 0 < (p : ℝ)) ∧
    (geometricMoment 4 (intervalReflectedSinh R) μ = 0 ∨ (p : ℝ) < R)

theorem intervalSinh_nonneg (R : ℝ) (p : Interval R) : 0 ≤ intervalSinh R p :=
  Real.sinh_nonneg_iff.mpr p.property.1

theorem intervalReflectedSinh_nonneg (R : ℝ) (p : Interval R) :
    0 ≤ intervalReflectedSinh R p :=
  Real.sinh_nonneg_iff.mpr (sub_nonneg.mpr p.property.2)

theorem ae_admissiblePoint (R : ℝ) (μ : ProbabilityMeasure (Interval R)) :
    ∀ᵐ p ∂(μ : Measure (Interval R)), AdmissiblePoint R μ p := by
  have hB : ∀ᵐ (p : Interval R) ∂(μ : Measure (Interval R)),
      geometricMoment 4 (intervalSinh R) μ = 0 ∨ 0 < (p : ℝ) := by
    by_cases hz : geometricMoment 4 (intervalSinh R) μ = 0
    · exact Filter.Eventually.of_forall (fun _ => Or.inl hz)
    · have hp : 0 < geometricMoment 4 (intervalSinh R) μ :=
        lt_of_le_of_ne (geometricMoment_nonneg 4 (intervalSinh R) μ) (Ne.symm hz)
      have hae := (ae_pos_and_integrable_log_of_geometricMoment_pos 4 (by norm_num)
        (intervalSinh R) μ (intervalSinh_nonneg R) hp).1
      filter_upwards [hae] with p hp
      exact Or.inr (Real.sinh_pos_iff.mp hp)
  have hD : ∀ᵐ (p : Interval R) ∂(μ : Measure (Interval R)),
      geometricMoment 4 (intervalReflectedSinh R) μ = 0 ∨ (p : ℝ) < R := by
    by_cases hz : geometricMoment 4 (intervalReflectedSinh R) μ = 0
    · exact Filter.Eventually.of_forall (fun _ => Or.inl hz)
    · have hp : 0 < geometricMoment 4 (intervalReflectedSinh R) μ :=
        lt_of_le_of_ne (geometricMoment_nonneg 4 (intervalReflectedSinh R) μ) (Ne.symm hz)
      have hae := (ae_pos_and_integrable_log_of_geometricMoment_pos 4 (by norm_num)
        (intervalReflectedSinh R) μ (intervalReflectedSinh_nonneg R) hp).1
      filter_upwards [hae] with p hp
      exact Or.inr (sub_pos.mp (Real.sinh_pos_iff.mp hp))
  exact hB.and hD

theorem integrable_measurePotential (R : ℝ) (μ : ProbabilityMeasure (Interval R)) :
    Integrable (fun p : Interval R => measurePotential R μ p) (μ : Measure (Interval R)) := by
  have hA := integrable_geometricMoment_mul_log 4 (by norm_num) (intervalCosh R) μ
    (fun p => (Real.cosh_pos (p : ℝ)).le)
  have hC := integrable_geometricMoment_mul_log 4 (by norm_num) (intervalReflectedCosh R) μ
    (fun p => (Real.cosh_pos (R - (p : ℝ))).le)
  have hB := integrable_geometricMoment_mul_log 4 (by norm_num) (intervalSinh R) μ (intervalSinh_nonneg R)
  have hD := integrable_geometricMoment_mul_log 4 (by norm_num) (intervalReflectedSinh R) μ
    (intervalReflectedSinh_nonneg R)
  exact ((((hA.add hC).sub hB).sub hD).const_mul (4 / hyperbolicNumerator R μ)).sub
    (integrable_continuousMap (intervalCenteredLogCosh R) μ)

theorem integral_measurePotential (R : ℝ) (hR : 0 < R)
    (μ : ProbabilityMeasure (Interval R)) :
    (∫ p : Interval R, measurePotential R μ p ∂μ) = potentialEntropy R μ := by
  have hAint := integrable_geometricMoment_mul_log 4 (by norm_num) (intervalCosh R) μ
    (fun p => (Real.cosh_pos (p : ℝ)).le)
  have hCint := integrable_geometricMoment_mul_log 4 (by norm_num) (intervalReflectedCosh R) μ
    (fun p => (Real.cosh_pos (R - (p : ℝ))).le)
  have hBint := integrable_geometricMoment_mul_log 4 (by norm_num) (intervalSinh R) μ (intervalSinh_nonneg R)
  have hDint := integrable_geometricMoment_mul_log 4 (by norm_num) (intervalReflectedSinh R) μ
    (intervalReflectedSinh_nonneg R)
  have hA := geometricMoment_mul_log_integral 4 (by norm_num) (intervalCosh R) μ
    (fun p => (Real.cosh_pos (p : ℝ)).le)
  have hC := geometricMoment_mul_log_integral 4 (by norm_num) (intervalReflectedCosh R) μ
    (fun p => (Real.cosh_pos (R - (p : ℝ))).le)
  have hB := geometricMoment_mul_log_integral 4 (by norm_num) (intervalSinh R) μ (intervalSinh_nonneg R)
  have hD := geometricMoment_mul_log_integral 4 (by norm_num) (intervalReflectedSinh R) μ
    (intervalReflectedSinh_nonneg R)
  have hACint : Integrable (fun p : Interval R =>
      geometricMoment 4 (intervalCosh R) μ * Real.log (intervalCosh R p) +
        geometricMoment 4 (intervalReflectedCosh R) μ * Real.log (intervalReflectedCosh R p))
      (μ : Measure (Interval R)) := hAint.add hCint
  have hACBint : Integrable (fun p : Interval R =>
      geometricMoment 4 (intervalCosh R) μ * Real.log (intervalCosh R p) +
        geometricMoment 4 (intervalReflectedCosh R) μ * Real.log (intervalReflectedCosh R p) -
        geometricMoment 4 (intervalSinh R) μ * Real.log (intervalSinh R p))
      (μ : Measure (Interval R)) := hACint.sub hBint
  have hACBDint : Integrable (fun p : Interval R =>
      geometricMoment 4 (intervalCosh R) μ * Real.log (intervalCosh R p) +
        geometricMoment 4 (intervalReflectedCosh R) μ * Real.log (intervalReflectedCosh R p) -
        geometricMoment 4 (intervalSinh R) μ * Real.log (intervalSinh R p) -
        geometricMoment 4 (intervalReflectedSinh R) μ * Real.log (intervalReflectedSinh R p))
      (μ : Measure (Interval R)) := hACBint.sub hDint
  change (∫ p, (4 / hyperbolicNumerator R μ) *
    (geometricMoment 4 (intervalCosh R) μ * Real.log (intervalCosh R p) +
    geometricMoment 4 (intervalReflectedCosh R) μ * Real.log (intervalReflectedCosh R p) -
    geometricMoment 4 (intervalSinh R) μ * Real.log (intervalSinh R p) -
    geometricMoment 4 (intervalReflectedSinh R) μ * Real.log (intervalReflectedSinh R p)) -
    intervalCenteredLogCosh R p ∂μ) = _
  rw [integral_sub (hACBDint.const_mul (4 / hyperbolicNumerator R μ))
      (integrable_continuousMap (intervalCenteredLogCosh R) μ), integral_const_mul,
    integral_sub hACBint hDint,
    integral_sub hACint hBint, integral_add hAint hCint]
  unfold potentialEntropy
  field_simp [(hyperbolicNumerator_pos R hR μ).ne']
  linarith only [hA, hC, hB, hD]

/-- A smooth real extension of the objective along variations toward p. -/
def objectiveSegment (R : ℝ) (μ : ProbabilityMeasure (Interval R)) (p : Interval R) (t : ℝ) : ℝ :=
  Real.log
    (momentSegment (geometricMoment 4 (intervalCosh R) μ) (intervalCosh R p ^ 4) t +
      momentSegment (geometricMoment 4 (intervalReflectedCosh R) μ) (intervalReflectedCosh R p ^ 4) t -
      momentSegment (geometricMoment 4 (intervalSinh R) μ) (intervalSinh R p ^ 4) t -
      momentSegment (geometricMoment 4 (intervalReflectedSinh R) μ) (intervalReflectedSinh R p ^ 4) t) -
    Real.log (2 * Real.cosh R) -
      ((1 - t) * (∫ q, intervalCenteredLogCosh R q ∂μ) + t * intervalCenteredLogCosh R p)

@[simp] theorem objectiveSegment_zero (R : ℝ) (μ : ProbabilityMeasure (Interval R)) (p : Interval R) :
    objectiveSegment R μ p 0 = hyperbolicObjective R μ := by
  simp only [objectiveSegment, momentSegment_zero _ _ (geometricMoment_nonneg 4 (intervalCosh R) μ),
    momentSegment_zero _ _ (geometricMoment_nonneg 4 (intervalReflectedCosh R) μ),
    momentSegment_zero _ _ (geometricMoment_nonneg 4 (intervalSinh R) μ),
    momentSegment_zero _ _ (geometricMoment_nonneg 4 (intervalReflectedSinh R) μ),
    sub_zero, one_mul, zero_mul, add_zero, hyperbolicObjective, hyperbolicNumerator]

theorem objectiveSegment_eq_mixture (R : ℝ) (μ : ProbabilityMeasure (Interval R))
    (p : Interval R) (hp : AdmissiblePoint R μ p) (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
    objectiveSegment R μ p t =
      hyperbolicObjective R (mixProbability μ (diracProbability p) t ⟨ht.1, ht.2.le⟩) := by
  have hA : geometricMoment 4 (intervalCosh R) (diracProbability p) = intervalCosh R p ^ 4 := by
    simpa only [Real.rpow_ofNat] using geometricMoment_dirac 4 (by norm_num)
      (intervalCosh R) p (Real.cosh_pos (p : ℝ)).le
  have hC : geometricMoment 4 (intervalReflectedCosh R) (diracProbability p) =
      intervalReflectedCosh R p ^ 4 := by
    simpa only [Real.rpow_ofNat] using geometricMoment_dirac 4 (by norm_num)
      (intervalReflectedCosh R) p (Real.cosh_pos (R - (p : ℝ))).le
  have hB : geometricMoment 4 (intervalSinh R) (diracProbability p) = intervalSinh R p ^ 4 := by
    simpa only [Real.rpow_ofNat] using geometricMoment_dirac 4 (by norm_num)
      (intervalSinh R) p (intervalSinh_nonneg R p)
  have hD : geometricMoment 4 (intervalReflectedSinh R) (diracProbability p) =
      intervalReflectedSinh R p ^ 4 := by
    simpa only [Real.rpow_ofNat] using geometricMoment_dirac 4 (by norm_num)
      (intervalReflectedSinh R) p (intervalReflectedSinh_nonneg R p)
  have hAp : geometricMoment 4 (intervalCosh R) μ = 0 ∨
      0 < geometricMoment 4 (intervalCosh R) (diracProbability p) :=
    Or.inr (by rw [hA]; exact pow_pos (Real.cosh_pos (p : ℝ)) 4)
  have hCp : geometricMoment 4 (intervalReflectedCosh R) μ = 0 ∨
      0 < geometricMoment 4 (intervalReflectedCosh R) (diracProbability p) :=
    Or.inr (by rw [hC]; exact pow_pos (Real.cosh_pos (R - (p : ℝ))) 4)
  have hBp : geometricMoment 4 (intervalSinh R) μ = 0 ∨
      0 < geometricMoment 4 (intervalSinh R) (diracProbability p) := by
    rcases hp.1 with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [hB]; exact pow_pos (Real.sinh_pos_iff.mpr h) 4)
  have hDp : geometricMoment 4 (intervalReflectedSinh R) μ = 0 ∨
      0 < geometricMoment 4 (intervalReflectedSinh R) (diracProbability p) := by
    rcases hp.2 with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [hD]; exact pow_pos (Real.sinh_pos_iff.mpr (sub_pos.mpr h)) 4)
  have hmixIntegral :
      (∫ q, intervalCenteredLogCosh R q ∂(mixProbability μ (diracProbability p) t ⟨ht.1, ht.2.le⟩)) =
        (1 - t) * (∫ q, intervalCenteredLogCosh R q ∂μ) + t * intervalCenteredLogCosh R p := by
    simpa only [coe_diracProbability, integral_dirac] using
      integral_mixProbability (intervalCenteredLogCosh R) μ (diracProbability p) t ⟨ht.1, ht.2.le⟩
  unfold objectiveSegment hyperbolicObjective hyperbolicNumerator
  rw [geometricMoment_mix_eq_momentSegment_of_admissible 4 (by norm_num) (intervalCosh R) μ
      (diracProbability p) t ht hAp,
    geometricMoment_mix_eq_momentSegment_of_admissible 4 (by norm_num) (intervalReflectedCosh R) μ
      (diracProbability p) t ht hCp,
    geometricMoment_mix_eq_momentSegment_of_admissible 4 (by norm_num) (intervalSinh R) μ
      (diracProbability p) t ht hBp,
    geometricMoment_mix_eq_momentSegment_of_admissible 4 (by norm_num) (intervalReflectedSinh R) μ
      (diracProbability p) t ht hDp, hA, hC, hB, hD, hmixIntegral]

/-- Exact first variation, valid at finite endpoints as well as in the interior. -/
theorem hasDerivAt_objectiveSegment_zero (R : ℝ) (hR : 0 < R)
    (μ : ProbabilityMeasure (Interval R)) (p : Interval R) :
    HasDerivAt (objectiveSegment R μ p)
      (measurePotential R μ p - potentialEntropy R μ) 0 := by
  have hA := hasDerivAt_momentSegment_zero
    (geometricMoment 4 (intervalCosh R) μ) (intervalCosh R p ^ 4)
    (geometricMoment_nonneg 4 (intervalCosh R) μ)
  have hC := hasDerivAt_momentSegment_zero
    (geometricMoment 4 (intervalReflectedCosh R) μ) (intervalReflectedCosh R p ^ 4)
    (geometricMoment_nonneg 4 (intervalReflectedCosh R) μ)
  have hB := hasDerivAt_momentSegment_zero
    (geometricMoment 4 (intervalSinh R) μ) (intervalSinh R p ^ 4)
    (geometricMoment_nonneg 4 (intervalSinh R) μ)
  have hD := hasDerivAt_momentSegment_zero
    (geometricMoment 4 (intervalReflectedSinh R) μ) (intervalReflectedSinh R p ^ 4)
    (geometricMoment_nonneg 4 (intervalReflectedSinh R) μ)
  have hnum := ((hA.add hC).sub hB).sub hD
  have hnum0 :
    momentSegment (geometricMoment 4 (intervalCosh R) μ) (intervalCosh R p ^ 4) 0 +
      momentSegment (geometricMoment 4 (intervalReflectedCosh R) μ) (intervalReflectedCosh R p ^ 4) 0 -
      momentSegment (geometricMoment 4 (intervalSinh R) μ) (intervalSinh R p ^ 4) 0 -
      momentSegment (geometricMoment 4 (intervalReflectedSinh R) μ) (intervalReflectedSinh R p ^ 4) 0 =
      hyperbolicNumerator R μ := by
    simp only [momentSegment_zero _ _ (geometricMoment_nonneg 4 (intervalCosh R) μ),
      momentSegment_zero _ _ (geometricMoment_nonneg 4 (intervalReflectedCosh R) μ),
      momentSegment_zero _ _ (geometricMoment_nonneg 4 (intervalSinh R) μ),
      momentSegment_zero _ _ (geometricMoment_nonneg 4 (intervalReflectedSinh R) μ), hyperbolicNumerator]
  have hnum_ne := hnum0.trans_ne (hyperbolicNumerator_pos R hR μ).ne'
  have hlast := (((hasDerivAt_id (0 : ℝ)).const_sub 1).mul_const
    (∫ q, intervalCenteredLogCosh R q ∂μ)).add
    ((hasDerivAt_id (0 : ℝ)).mul_const (intervalCenteredLogCosh R p))
  convert ((hnum.log hnum_ne).sub_const (Real.log (2 * Real.cosh R))).sub hlast using 1
  · rfl
  · simp only [Pi.add_apply, Pi.sub_apply]
    rw [hnum0]
    simp only [measurePotential, variationPotential, potentialEntropy,
      intervalCosh, intervalReflectedCosh, intervalSinh, intervalReflectedSinh,
      intervalCenteredLogCosh, ContinuousMap.coe_mk, Real.log_pow]
    field_simp [(hyperbolicNumerator_pos R hR μ).ne'] <;> ring

/-- The elementary right-derivative condition, stated without a tangent-cone assumption. -/
theorem derivative_nonneg_of_right_minimum {f : ℝ → ℝ} {d : ℝ}
    (hd : HasDerivAt f d 0) (hmin : ∀ t ∈ Ico (0 : ℝ) 1, f 0 ≤ f t) : 0 ≤ d := by
  apply ge_of_tendsto hd.tendsto_slope_zero_right
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with t ht0 ht1
  simp only [zero_add, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr ht0.le) (sub_nonneg.mpr (hmin t ⟨ht0.le, ht1⟩))

/-- The potential at every finite admissible point is at least its true average. -/
theorem potentialEntropy_le_measurePotential_of_minimizer
    (R : ℝ) (hR : 0 < R) (μ : ProbabilityMeasure (Interval R))
    (hmin : ∀ ν : ProbabilityMeasure (Interval R), hyperbolicObjective R μ ≤ hyperbolicObjective R ν)
    (p : Interval R) (hp : AdmissiblePoint R μ p) :
    potentialEntropy R μ ≤ measurePotential R μ p := by
  apply sub_nonneg.mp
  apply derivative_nonneg_of_right_minimum (hasDerivAt_objectiveSegment_zero R hR μ p)
  intro t ht
  rw [objectiveSegment_zero, objectiveSegment_eq_mixture R μ p hp t ht]
  exact hmin _

/-- A minimizing measure concentrates almost everywhere on the minimum-potential level. -/
theorem ae_measurePotential_eq_entropy_of_minimizer
    (R : ℝ) (hR : 0 < R) (μ : ProbabilityMeasure (Interval R))
    (hmin : ∀ ν : ProbabilityMeasure (Interval R), hyperbolicObjective R μ ≤ hyperbolicObjective R ν) :
    ∀ᵐ (p : Interval R) ∂(μ : Measure (Interval R)), measurePotential R μ p = potentialEntropy R μ := by
  have hnonneg : 0 ≤ᵐ[(μ : Measure (Interval R))]
      fun p : Interval R => measurePotential R μ p - potentialEntropy R μ := by
    filter_upwards [ae_admissiblePoint R μ] with p hp
    exact sub_nonneg.mpr (potentialEntropy_le_measurePotential_of_minimizer R hR μ hmin p hp)
  have hint := (integrable_measurePotential R μ).sub (integrable_const (potentialEntropy R μ))
  have hzero : (∫ p : Interval R, measurePotential R μ p - potentialEntropy R μ ∂μ) = 0 := by
    rw [integral_sub (integrable_measurePotential R μ) (integrable_const _),
      integral_measurePotential R hR μ]
    simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
      one_smul, sub_self]
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnonneg hint).mp hzero
  filter_upwards [hae] with p hp
  exact sub_eq_zero.mp hp

end PaperVerification.Hyperbolic

#print axioms PaperVerification.Hyperbolic.integral_measurePotential
#print axioms PaperVerification.Hyperbolic.potentialEntropy_le_measurePotential_of_minimizer
#print axioms PaperVerification.Hyperbolic.ae_measurePotential_eq_entropy_of_minimizer
