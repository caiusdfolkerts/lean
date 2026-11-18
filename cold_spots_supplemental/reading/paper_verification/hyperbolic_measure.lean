module
public import PaperVerification.GeometricMean
public import PaperVerification.HyperbolicLocalization
public import Mathlib.MeasureTheory.Measure.Prokhorov
@[expose] public section
/-! # Weak compactness and existence for the hyperbolic variational problem

The probability measures are unrestricted Borel probability measures on the full
closed interval. The sinh terms use the truncation-defined geometric moment, so
endpoint atoms and divergent negative logarithmic integrals remain included.
-/

noncomputable section

namespace PaperVerification.Hyperbolic

open Real Set MeasureTheory Filter Topology

abbrev Interval (R : ℝ) := Set.Icc (0 : ℝ) R

def intervalCosh (R : ℝ) : C(Interval R, ℝ) :=
  ⟨fun p => Real.cosh (p : ℝ), Real.continuous_cosh.comp continuous_subtype_val⟩

def intervalReflectedCosh (R : ℝ) : C(Interval R, ℝ) :=
  ⟨fun p => Real.cosh (R - (p : ℝ)),
    Real.continuous_cosh.comp (continuous_const.sub continuous_subtype_val)⟩

def intervalSinh (R : ℝ) : C(Interval R, ℝ) :=
  ⟨fun p => Real.sinh (p : ℝ), Real.continuous_sinh.comp continuous_subtype_val⟩

def intervalReflectedSinh (R : ℝ) : C(Interval R, ℝ) :=
  ⟨fun p => Real.sinh (R - (p : ℝ)),
    Real.continuous_sinh.comp (continuous_const.sub continuous_subtype_val)⟩

def intervalCenteredLogCosh (R : ℝ) : C(Interval R, ℝ) :=
  ⟨fun p => Real.log (Real.cosh (2 * (p : ℝ) - R)),
    (Real.continuous_cosh.comp
      ((continuous_const.mul continuous_subtype_val).sub continuous_const)).log
        (fun p => (Real.cosh_pos _).ne')⟩

def hyperbolicNumerator (R : ℝ) (μ : ProbabilityMeasure (Interval R)) : ℝ :=
  geometricMoment 4 (intervalCosh R) μ + geometricMoment 4 (intervalReflectedCosh R) μ -
    geometricMoment 4 (intervalSinh R) μ - geometricMoment 4 (intervalReflectedSinh R) μ

/-- J in Section 4.1, the logarithm of the ratio in Theorem 3.1. -/
def hyperbolicObjective (R : ℝ) (μ : ProbabilityMeasure (Interval R)) : ℝ :=
  Real.log (hyperbolicNumerator R μ) - Real.log (2 * Real.cosh R) -
    ∫ p, intervalCenteredLogCosh R p ∂μ

theorem strictMono_real_tanh : StrictMono Real.tanh := by
  apply strictMono_of_deriv_pos
  intro p
  rw [(hasDerivAt_tanh p).deriv]
  linarith only [Real.tanh_sq_lt_one p]

theorem tanh_pos {R : ℝ} (hR : 0 < R) : 0 < Real.tanh R := by
  simpa only [Real.tanh_zero] using strictMono_real_tanh hR

theorem sinh_le_tanh_mul_cosh {R p : ℝ} (hp : p ≤ R) :
    Real.sinh p ≤ Real.tanh R * Real.cosh p := by
  have ht := strictMono_real_tanh.monotone hp
  rw [Real.tanh_eq_sinh_div_cosh p] at ht
  exact (div_le_iff₀ (Real.cosh_pos p)).mp ht

theorem geometricMoment_sinh_le (R : ℝ) (hR : 0 < R)
    (μ : ProbabilityMeasure (Interval R)) :
    geometricMoment 4 (intervalSinh R) μ ≤
      Real.tanh R ^ 4 * geometricMoment 4 (intervalCosh R) μ := by
  let scaled : C(Interval R, ℝ) :=
    ⟨fun p => Real.tanh R * intervalCosh R p, continuous_const.mul (intervalCosh R).continuous⟩
  have hmono := geometricMoment_mono 4 (by norm_num)
    (f := intervalSinh R) (g := scaled)
    (fun p => sinh_le_tanh_mul_cosh p.property.2) μ
  have hscale := geometricMoment_nat_const_mul_of_lower_bound 4 (intervalCosh R) μ
    (tanh_pos hR) (by norm_num : (0 : ℝ) < 1) (fun p => Real.one_le_cosh (p : ℝ))
  exact hmono.trans_eq hscale

theorem geometricMoment_reflectedSinh_le (R : ℝ) (hR : 0 < R)
    (μ : ProbabilityMeasure (Interval R)) :
    geometricMoment 4 (intervalReflectedSinh R) μ ≤
      Real.tanh R ^ 4 * geometricMoment 4 (intervalReflectedCosh R) μ := by
  let scaled : C(Interval R, ℝ) :=
    ⟨fun p => Real.tanh R * intervalReflectedCosh R p,
      continuous_const.mul (intervalReflectedCosh R).continuous⟩
  have hmono := geometricMoment_mono 4 (by norm_num)
    (f := intervalReflectedSinh R) (g := scaled)
    (fun p => sinh_le_tanh_mul_cosh (by linarith [p.property.1])) μ
  have hscale := geometricMoment_nat_const_mul_of_lower_bound 4 (intervalReflectedCosh R) μ
    (tanh_pos hR) (by norm_num : (0 : ℝ) < 1) (fun p => Real.one_le_cosh (R - (p : ℝ)))
  exact hmono.trans_eq hscale

theorem tanh_fourth_lt_one (R : ℝ) : Real.tanh R ^ 4 < 1 := by
  have h₁ := Real.tanh_sq_lt_one R
  have h₂ : 0 < (1 - Real.tanh R ^ 2) * (1 + Real.tanh R ^ 2) :=
    mul_pos (by linarith) (by nlinarith only [sq_nonneg (Real.tanh R)])
  nlinarith only [h₂]

/-- Uniform positive lower bound from Lemma 4.1, including the zero sinh means. -/
theorem hyperbolicNumerator_lower_bound (R : ℝ) (hR : 0 < R)
    (μ : ProbabilityMeasure (Interval R)) :
    2 * (1 - Real.tanh R ^ 4) ≤ hyperbolicNumerator R μ := by
  have hA := one_le_geometricMoment_of_one_le 4 (by norm_num) (intervalCosh R) μ
    (fun p => Real.one_le_cosh (p : ℝ))
  have hC := one_le_geometricMoment_of_one_le 4 (by norm_num) (intervalReflectedCosh R) μ
    (fun p => Real.one_le_cosh (R - (p : ℝ)))
  have hB := geometricMoment_sinh_le R hR μ
  have hD := geometricMoment_reflectedSinh_le R hR μ
  have hq : 0 ≤ 1 - Real.tanh R ^ 4 := (sub_pos.mpr (tanh_fourth_lt_one R)).le
  have h₁ := mul_nonneg hq (sub_nonneg.mpr hA)
  have h₂ := mul_nonneg hq (sub_nonneg.mpr hC)
  unfold hyperbolicNumerator
  nlinarith only [hB, hD, h₁, h₂]

theorem hyperbolicNumerator_pos (R : ℝ) (hR : 0 < R)
    (μ : ProbabilityMeasure (Interval R)) : 0 < hyperbolicNumerator R μ :=
  (mul_pos (by norm_num) (sub_pos.mpr (tanh_fourth_lt_one R))).trans_le
    (hyperbolicNumerator_lower_bound R hR μ)

theorem lowerSemicontinuous_hyperbolicNumerator (R : ℝ) :
    LowerSemicontinuous (hyperbolicNumerator R) := by
  have hA := continuous_geometricMoment_of_lower_bound 4 (by norm_num) (intervalCosh R)
    (by norm_num : (0 : ℝ) < 1) (fun p => Real.one_le_cosh (p : ℝ))
  have hC := continuous_geometricMoment_of_lower_bound 4 (by norm_num) (intervalReflectedCosh R)
    (by norm_num : (0 : ℝ) < 1) (fun p => Real.one_le_cosh (R - (p : ℝ)))
  have hB := upperSemicontinuous_geometricMoment 4 (intervalSinh R)
  have hD := upperSemicontinuous_geometricMoment 4 (intervalReflectedSinh R)
  have h := ((hA.lowerSemicontinuous.add hC.lowerSemicontinuous).add hB.neg).add hD.neg
  change LowerSemicontinuous (fun μ => geometricMoment 4 (intervalCosh R) μ +
    geometricMoment 4 (intervalReflectedCosh R) μ - geometricMoment 4 (intervalSinh R) μ -
      geometricMoment 4 (intervalReflectedSinh R) μ)
  have heq : (fun μ : ProbabilityMeasure (Interval R) =>
      geometricMoment 4 (intervalCosh R) μ + geometricMoment 4 (intervalReflectedCosh R) μ -
        geometricMoment 4 (intervalSinh R) μ - geometricMoment 4 (intervalReflectedSinh R) μ) =
      (fun μ => geometricMoment 4 (intervalCosh R) μ + geometricMoment 4 (intervalReflectedCosh R) μ +
        -(geometricMoment 4 (intervalSinh R) μ) + -(geometricMoment 4 (intervalReflectedSinh R) μ)) := by
    funext μ
    ring
  rw [heq]
  exact h

theorem lowerSemicontinuous_hyperbolicObjective (R : ℝ) (hR : 0 < R) :
    LowerSemicontinuous (hyperbolicObjective R) := by
  let δ : ℝ := 2 * (1 - Real.tanh R ^ 4)
  have hδ : 0 < δ := mul_pos (by norm_num) (sub_pos.mpr (tanh_fourth_lt_one R))
  have hclip : Continuous (fun t : ℝ => Real.log (max δ t)) :=
    (continuous_const.max continuous_id).log (fun t => (hδ.trans_le (le_max_left δ t)).ne')
  have hmono : Monotone (fun t : ℝ => Real.log (max δ t)) := by
    intro x y hxy
    exact Real.log_le_log (hδ.trans_le (le_max_left δ x)) (max_le_max_left δ hxy)
  have hlog := hclip.comp_lowerSemicontinuous
    (lowerSemicontinuous_hyperbolicNumerator R) hmono
  have heq : (fun t : ℝ => Real.log (max δ t)) ∘ hyperbolicNumerator R =
      fun μ => Real.log (hyperbolicNumerator R μ) := by
    funext μ
    dsimp only [Function.comp_apply]
    rw [max_eq_right (hyperbolicNumerator_lower_bound R hR μ)]
  rw [heq] at hlog
  have hrest : Continuous (fun μ : ProbabilityMeasure (Interval R) =>
      -Real.log (2 * Real.cosh R) - ∫ p, intervalCenteredLogCosh R p ∂μ) :=
    continuous_const.sub (ProbabilityMeasure.continuous_integral_continuousMap (intervalCenteredLogCosh R))
  convert hlog.add hrest.lowerSemicontinuous using 1
  ext μ
  unfold hyperbolicObjective
  ring

/-- The arbitrary-measure objective attains a global minimum on the full
probability-measure space. No finite-support assumption is made here. -/
theorem exists_minimizer_hyperbolicObjective (R : ℝ) (hR : 0 < R) :
    ∃ μ : ProbabilityMeasure (Interval R),
      ∀ ν : ProbabilityMeasure (Interval R), hyperbolicObjective R μ ≤ hyperbolicObjective R ν := by
  let p₀ : Interval R := ⟨0, ⟨le_rfl, hR.le⟩⟩
  let μ₀ : ProbabilityMeasure (Interval R) := ⟨Measure.dirac p₀, inferInstance⟩
  obtain ⟨μ, hμ, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn
    ⟨μ₀, mem_univ μ₀⟩ isCompact_univ
    ((lowerSemicontinuous_hyperbolicObjective R hR).lowerSemicontinuousOn univ)
  exact ⟨μ, fun ν => (isMinOn_iff.mp hmin) ν (mem_univ ν)⟩

end PaperVerification.Hyperbolic

#print axioms PaperVerification.Hyperbolic.hyperbolicNumerator_lower_bound
#print axioms PaperVerification.Hyperbolic.exists_minimizer_hyperbolicObjective
