module
public import PaperVerification.GeometricMean
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
@[expose] public section
/-! # Geometric means on segments of probability measures

The exact multiplicative segment identity includes zero geometric means, rather
than assuming logarithmic integrability. This is the analytic reason a vanished
sinh term stays zero under every proper variation toward an interior atom.
-/

noncomputable section

namespace PaperVerification.Hyperbolic

open MeasureTheory Set Filter Topology

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [CompactSpace X] [OpensMeasurableSpace X]

/-- Convex combination of two probability measures. -/
def mixProbability (μ ν : ProbabilityMeasure X) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ProbabilityMeasure X :=
  ⟨ENNReal.ofReal (1 - t) • (μ : Measure X) + ENNReal.ofReal t • (ν : Measure X), by
    constructor
    simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add (sub_nonneg.mpr ht.2) ht.1]
    norm_num⟩

@[simp] theorem coe_mixProbability (μ ν : ProbabilityMeasure X) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    ((mixProbability μ ν t ht) : Measure X) =
      ENNReal.ofReal (1 - t) • (μ : Measure X) + ENNReal.ofReal t • (ν : Measure X) := rfl

theorem integral_mixProbability (f : C(X, ℝ)) (μ ν : ProbabilityMeasure X) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ x, f x ∂(mixProbability μ ν t ht)) =
      (1 - t) * (∫ x, f x ∂μ) + t * (∫ x, f x ∂ν) := by
  rw [coe_mixProbability, integral_add_measure
    ((integrable_continuousMap f μ).smul_measure ENNReal.ofReal_ne_top)
    ((integrable_continuousMap f ν).smul_measure ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure, ENNReal.toReal_ofReal (sub_nonneg.mpr ht.2),
    ENNReal.toReal_ofReal ht.1, smul_eq_mul]

theorem truncatedGeometricMoment_mix (k : ℝ) (f : C(X, ℝ))
    (μ ν : ProbabilityMeasure X) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    truncatedGeometricMoment k f (mixProbability μ ν t ht) n =
      truncatedGeometricMoment k f μ n ^ (1 - t) *
        truncatedGeometricMoment k f ν n ^ t := by
  unfold truncatedGeometricMoment
  rw [integral_mixProbability]
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.rpow_def_of_pos (Real.exp_pos _)]
  rw [Real.log_exp, Real.log_exp, ← Real.exp_add]
  congr 1
  ring

/-- Exact segment identity, valid at the endpoints and for zero geometric means. -/
theorem geometricMoment_mix (k : ℝ) (hk : 0 ≤ k) (f : C(X, ℝ))
    (μ ν : ProbabilityMeasure X) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    geometricMoment k f (mixProbability μ ν t ht) =
      geometricMoment k f μ ^ (1 - t) * geometricMoment k f ν ^ t := by
  have h₁ := ((tendsto_truncatedGeometricMoment k hk f μ).rpow_const
    (Or.inr (sub_nonneg.mpr ht.2))).mul
    ((tendsto_truncatedGeometricMoment k hk f ν).rpow_const (Or.inr ht.1))
  have h₂ := tendsto_truncatedGeometricMoment k hk f (mixProbability μ ν t ht)
  have heq : truncatedGeometricMoment k f (mixProbability μ ν t ht) =
      fun n => truncatedGeometricMoment k f μ n ^ (1 - t) *
        truncatedGeometricMoment k f ν n ^ t :=
    funext (truncatedGeometricMoment_mix k f μ ν t ht)
  rw [heq] at h₂
  exact tendsto_nhds_unique h₂ h₁

/-- A zero geometric moment remains zero under every proper convex variation. -/
theorem geometricMoment_mix_eq_zero (k : ℝ) (hk : 0 ≤ k) (f : C(X, ℝ))
    (μ ν : ProbabilityMeasure X) (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1)
    (hzero : geometricMoment k f μ = 0) :
    geometricMoment k f (mixProbability μ ν t ⟨ht.1, ht.2.le⟩) = 0 := by
  rw [geometricMoment_mix k hk f μ ν t ⟨ht.1, ht.2.le⟩, hzero,
    Real.zero_rpow (sub_pos.mpr ht.2).ne', zero_mul]

/-- A Dirac measure as a probability measure. -/
def diracProbability (p : X) : ProbabilityMeasure X := ⟨Measure.dirac p, inferInstance⟩

@[simp] theorem coe_diracProbability (p : X) :
    ((diracProbability p) : Measure X) = Measure.dirac p := rfl

theorem geometricMoment_dirac [MeasurableSingletonClass X]
    (k : ℝ) (hk : 0 ≤ k) (f : C(X, ℝ)) (p : X) (hfp : 0 ≤ f p) :
    geometricMoment k f (diracProbability p) = f p ^ k := by
  have hcut : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hm : Tendsto (fun n : ℕ => max (Real.exp (-(n : ℝ))) (f p)) atTop (𝓝 (f p)) := by
    simpa only [max_eq_right hfp] using hcut.max
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => f p) atTop (𝓝 (f p)))
  have hpow := hm.rpow_const (Or.inr hk)
  have hseq := tendsto_truncatedGeometricMoment k hk f (diracProbability p)
  have heq : truncatedGeometricMoment k f (diracProbability p) =
      fun n : ℕ => max (Real.exp (-(n : ℝ))) (f p) ^ k := by
    funext n
    simp only [truncatedGeometricMoment, coe_diracProbability, integral_dirac, truncatedLog,
      ContinuousMap.coe_mk]
    rw [Real.rpow_def_of_pos ((Real.exp_pos _).trans_le (le_max_left _ _))]
    congr 1
    ring
  rw [heq] at hseq
  exact tendsto_nhds_unique hseq hpow

/-- A smooth extension around t=0 of a proper geometric-mean segment. The zero
case is identically zero; it is not replaced by exp(log 0). -/
def momentSegment (a b t : ℝ) : ℝ :=
  if a = 0 then 0 else Real.exp ((1 - t) * Real.log a + t * Real.log b)

theorem momentSegment_eq_rpow (a b t : ℝ) (ha : 0 ≤ a) (hb : 0 < b) (ht : t < 1) :
    momentSegment a b t = a ^ (1 - t) * b ^ t := by
  by_cases haz : a = 0
  · simp only [momentSegment, haz, ↓reduceIte,
      Real.zero_rpow (sub_pos.mpr ht).ne', zero_mul]
  · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm haz)
    rw [momentSegment, if_neg haz, Real.rpow_def_of_pos hap, Real.rpow_def_of_pos hb,
      ← Real.exp_add]
    congr 1
    ring

@[simp] theorem momentSegment_zero (a b : ℝ) (ha : 0 ≤ a) : momentSegment a b 0 = a := by
  by_cases haz : a = 0
  · simp [momentSegment, haz]
  · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm haz)
    simp [momentSegment, haz, Real.exp_log hap]

theorem hasDerivAt_momentSegment_zero (a b : ℝ) (ha : 0 ≤ a) :
    HasDerivAt (momentSegment a b) (a * (Real.log b - Real.log a)) 0 := by
  by_cases haz : a = 0
  · subst a
    have hfun : momentSegment 0 b = fun _ : ℝ => 0 := by
      funext t
      exact if_pos rfl
    rw [hfun, zero_mul]
    exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm haz)
    have hd := ((((hasDerivAt_id (0 : ℝ)).const_sub 1).mul_const (Real.log a)).add
      ((hasDerivAt_id (0 : ℝ)).mul_const (Real.log b))).exp
    convert hd using 1 <;> (try funext t) <;>
      (try simp only [momentSegment, if_neg haz, sub_zero, one_mul, zero_mul,
        add_zero, Real.exp_log hap, Pi.add_apply, Pi.sub_apply, Pi.mul_apply,
        Function.comp_apply, id_eq]) <;> ring

theorem geometricMoment_mix_eq_momentSegment (k : ℝ) (hk : 0 ≤ k) (f : C(X, ℝ))
    (μ ν : ProbabilityMeasure X) (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1)
    (hν : 0 < geometricMoment k f ν) :
    geometricMoment k f (mixProbability μ ν t ⟨ht.1, ht.2.le⟩) =
      momentSegment (geometricMoment k f μ) (geometricMoment k f ν) t := by
  rw [momentSegment_eq_rpow _ _ _ (geometricMoment_nonneg k f μ) hν ht.2]
  exact geometricMoment_mix k hk f μ ν t ⟨ht.1, ht.2.le⟩

/-- The segment formula also includes a vanishing atom when the original
geometric moment is already zero. -/
theorem momentSegment_eq_rpow_of_admissible (a b t : ℝ) (ha : 0 ≤ a)
    (hb : a = 0 ∨ 0 < b) (ht : t < 1) :
    momentSegment a b t = a ^ (1 - t) * b ^ t := by
  rcases hb with haz | hb
  · simp only [momentSegment, haz, ↓reduceIte,
      Real.zero_rpow (sub_pos.mpr ht).ne', zero_mul]
  · exact momentSegment_eq_rpow a b t ha hb ht

theorem geometricMoment_mix_eq_momentSegment_of_admissible
    (k : ℝ) (hk : 0 ≤ k) (f : C(X, ℝ))
    (μ ν : ProbabilityMeasure X) (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1)
    (hν : geometricMoment k f μ = 0 ∨ 0 < geometricMoment k f ν) :
    geometricMoment k f (mixProbability μ ν t ⟨ht.1, ht.2.le⟩) =
      momentSegment (geometricMoment k f μ) (geometricMoment k f ν) t := by
  rw [momentSegment_eq_rpow_of_admissible _ _ _ (geometricMoment_nonneg k f μ) hν ht.2]
  exact geometricMoment_mix k hk f μ ν t ⟨ht.1, ht.2.le⟩

end PaperVerification.Hyperbolic

#print axioms PaperVerification.Hyperbolic.geometricMoment_mix
#print axioms PaperVerification.Hyperbolic.geometricMoment_mix_eq_zero
#print axioms PaperVerification.Hyperbolic.geometricMoment_dirac
#print axioms PaperVerification.Hyperbolic.hasDerivAt_momentSegment_zero
