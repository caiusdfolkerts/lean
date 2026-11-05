module
public import PaperVerification.HyperbolicSupport
public import PaperVerification.HyperbolicCompactMinimum
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
@[expose] public section
/-! # Exact atomic representation and the arbitrary-measure bridge

Support at two points is converted into an equality of Borel probability
measures with explicit real weights.  The geometric moment calculation keeps
zero values and zero weights, and consequently includes endpoint atoms.
-/

noncomputable section

namespace PaperVerification.Hyperbolic

open Real Set MeasureTheory Filter Topology

section MixtureLaws

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [CompactSpace X] [OpensMeasurableSpace X]

@[simp] theorem mixProbability_zero (μ ν : ProbabilityMeasure X) (h : (0 : ℝ) ∈ Icc 0 1) :
    mixProbability μ ν 0 h = μ := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [coe_mixProbability, sub_zero, ENNReal.ofReal_one, ENNReal.ofReal_zero,
    one_smul, zero_smul, add_zero]

@[simp] theorem mixProbability_one (μ ν : ProbabilityMeasure X) (h : (1 : ℝ) ∈ Icc 0 1) :
    mixProbability μ ν 1 h = ν := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [coe_mixProbability, sub_self, ENNReal.ofReal_one, ENNReal.ofReal_zero,
    one_smul, zero_smul, zero_add]

@[simp] theorem mixProbability_same (μ : ProbabilityMeasure X) (t : ℝ) (ht : t ∈ Icc 0 1) :
    mixProbability μ μ t ht = μ := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [coe_mixProbability, ← add_smul, ← ENNReal.ofReal_add (sub_nonneg.mpr ht.2) ht.1]
  simp only [sub_add_cancel, ENNReal.ofReal_one, one_smul]

theorem mixProbability_comm (μ ν : ProbabilityMeasure X) (t : ℝ) (ht : t ∈ Icc 0 1) :
    mixProbability μ ν t ht =
      mixProbability ν μ (1 - t) ⟨sub_nonneg.mpr ht.2, by linarith [ht.1]⟩ := by
  apply ProbabilityMeasure.toMeasure_injective
  erw [coe_mixProbability, coe_mixProbability]
  simp only [sub_sub_cancel, add_comm]

theorem geometricMoment_pair [MeasurableSingletonClass X]
    (k : ℝ) (hk : 0 ≤ k) (f : C(X, ℝ)) (p q : X)
    (hp : 0 ≤ f p) (hq : 0 ≤ f q) (t : ℝ) (ht : t ∈ Icc 0 1) :
    geometricMoment k f (mixProbability (diracProbability p) (diracProbability q) t ht) =
      f p ^ (k * (1 - t)) * f q ^ (k * t) := by
  rw [geometricMoment_mix k hk, geometricMoment_dirac k hk f p hp,
    geometricMoment_dirac k hk f q hq, ← Real.rpow_mul hp, ← Real.rpow_mul hq]

end MixtureLaws

theorem probability_eq_pair_mixture {R : ℝ} (μ : ProbabilityMeasure (Interval R))
    (p q : Interval R) (hs : (μ : Measure (Interval R)).support ⊆ {p, q}) :
    ∃ t : ℝ, ∃ ht : t ∈ Icc 0 1,
      μ = mixProbability (diracProbability p) (diracProbability q) t ht := by
  classical
  have hae : ∀ᵐ x ∂(μ : Measure (Interval R)), x = p ∨ x = q := by
    filter_upwards [(μ : Measure (Interval R)).support_mem_ae] with x hx
    simpa only [mem_insert_iff, mem_singleton_iff] using hs hx
  by_cases hpq : p = q
  · subst q
    have hae' : ∀ᵐ x ∂(μ : Measure (Interval R)), x ∈ ({p} : Finset (Interval R)) := by
      simpa only [or_self, Finset.mem_singleton] using hae
    have hm : (μ : Measure (Interval R)) = (μ : Measure (Interval R)) {p} • Measure.dirac p := by
      simpa only [Finset.sum_singleton] using Measure.ae_mem_finset_iff.mp hae'
    have hmass : (μ : Measure (Interval R)) {p} = 1 := by
      have h := congrArg (fun ν : Measure (Interval R) => ν univ) hm
      simpa only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one] using h.symm
    refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
    erw [mixProbability_zero]
    apply ProbabilityMeasure.toMeasure_injective
    rw [coe_diracProbability, hm, hmass, one_smul]
  · have hm := (Measure.ae_eq_or_eq_iff_eq_dirac_add_dirac hpq).mp hae
    have hpfin : (μ : Measure (Interval R)) {p} ≠ ⊤ := measure_ne_top _ _
    have hqfin : (μ : Measure (Interval R)) {q} ≠ ⊤ := measure_ne_top _ _
    have hmass : (μ : Measure (Interval R)) {p} + (μ : Measure (Interval R)) {q} = 1 := by
      have h := congrArg (fun ν : Measure (Interval R) => ν univ) hm
      simpa only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one] using h.symm
    have hmassR : ((μ : Measure (Interval R)) {p}).toReal + ((μ : Measure (Interval R)) {q}).toReal = 1 := by
      rw [← ENNReal.toReal_add hpfin hqfin, hmass, ENNReal.toReal_one]
    let t := ((μ : Measure (Interval R)) {q}).toReal
    have ht : t ∈ Icc 0 1 := ⟨ENNReal.toReal_nonneg, by
      have hp0 : 0 ≤ ((μ : Measure (Interval R)) {p}).toReal := ENNReal.toReal_nonneg
      dsimp [t]
      linarith⟩
    refine ⟨t, ht, ?_⟩
    apply ProbabilityMeasure.toMeasure_injective
    rw [coe_mixProbability, coe_diracProbability, coe_diracProbability]
    have hq' : ENNReal.ofReal t = (μ : Measure (Interval R)) {q} := ENNReal.ofReal_toReal hqfin
    have hp' : ENNReal.ofReal (1 - t) = (μ : Measure (Interval R)) {p} := by
      have hpt : 1 - t = ((μ : Measure (Interval R)) {p}).toReal := by dsimp [t]; linarith
      rw [hpt, ENNReal.ofReal_toReal hpfin]
    rw [hp', hq']
    exact hm

theorem ordered_pair_mixture_of_minimizer
    (R : ℝ) (hR : 0 < R) (μ : ProbabilityMeasure (Interval R))
    (hmin : ∀ ν : ProbabilityMeasure (Interval R), hyperbolicObjective R μ ≤ hyperbolicObjective R ν) :
    ∃ p q : Interval R, p ≤ q ∧ ∃ t : ℝ, ∃ ht : t ∈ Icc 0 1,
      μ = mixProbability (diracProbability p) (diracProbability q) t ht := by
  obtain ⟨p, q, hs⟩ := support_subset_pair_of_minimizer R hR μ hmin
  rcases le_total p q with hpq | hqp
  · obtain ⟨t, ht, hm⟩ := probability_eq_pair_mixture μ p q hs
    exact ⟨p, q, hpq, t, ht, hm⟩
  · have hs' : (μ : Measure (Interval R)).support ⊆ {q, p} := by simpa only [Set.pair_comm] using hs
    obtain ⟨t, ht, hm⟩ := probability_eq_pair_mixture μ q p hs'
    exact ⟨q, p, hqp, t, ht, hm⟩

theorem hyperbolicNumerator_pair (R : ℝ) (p q : Interval R) (t : ℝ) (ht : t ∈ Icc 0 1) :
    hyperbolicNumerator R (mixProbability (diracProbability p) (diracProbability q) t ht) =
      twoPointNumerator R p q (1 - t) := by
  have hpc : 0 ≤ intervalCosh R p := (Real.cosh_pos _).le
  have hqc : 0 ≤ intervalCosh R q := (Real.cosh_pos _).le
  have hpr : 0 ≤ intervalReflectedCosh R p := (Real.cosh_pos _).le
  have hqr : 0 ≤ intervalReflectedCosh R q := (Real.cosh_pos _).le
  have hps : 0 ≤ intervalSinh R p := Real.sinh_nonneg_iff.mpr p.property.1
  have hqs : 0 ≤ intervalSinh R q := Real.sinh_nonneg_iff.mpr q.property.1
  have hpt : 0 ≤ intervalReflectedSinh R p := Real.sinh_nonneg_iff.mpr (sub_nonneg.mpr p.property.2)
  have hqt : 0 ≤ intervalReflectedSinh R q := Real.sinh_nonneg_iff.mpr (sub_nonneg.mpr q.property.2)
  unfold hyperbolicNumerator
  rw [geometricMoment_pair 4 (by norm_num) _ p q hpc hqc t ht,
    geometricMoment_pair 4 (by norm_num) _ p q hpr hqr t ht,
    geometricMoment_pair 4 (by norm_num) _ p q hps hqs t ht,
    geometricMoment_pair 4 (by norm_num) _ p q hpt hqt t ht]
  simp only [twoPointNumerator, intervalCosh, intervalReflectedCosh, intervalSinh,
    intervalReflectedSinh, ContinuousMap.coe_mk, sub_sub_cancel]

theorem hyperbolicObjective_pair (R : ℝ) (p q : Interval R) (t : ℝ) (ht : t ∈ Icc 0 1) :
    hyperbolicObjective R (mixProbability (diracProbability p) (diracProbability q) t ht) =
      twoPointObjective R p q (1 - t) := by
  unfold hyperbolicObjective
  rw [hyperbolicNumerator_pair, integral_mixProbability]
  simp only [coe_diracProbability, integral_dirac]
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.cosh_pos R).ne']
  unfold twoPointObjective
  simp only [intervalCenteredLogCosh, ContinuousMap.coe_mk, sub_sub_cancel]
  ring

theorem hyperbolicObjective_pair_nonneg (R : ℝ) (p q : Interval R) (hpq : p ≤ q)
    (t : ℝ) (ht : t ∈ Icc 0 1) :
    0 ≤ hyperbolicObjective R (mixProbability (diracProbability p) (diracProbability q) t ht) := by
  have hw : 1 - t ∈ Icc (0 : ℝ) 1 := ⟨sub_nonneg.mpr ht.2, by linarith [ht.1]⟩
  rw [hyperbolicObjective_pair, twoPointObjective_eq_log_ratio p.property q.property hw]
  exact Real.log_nonneg (twoPointRatio_ge_one p.property q.property hpq hw)

def reflectInterval (R : ℝ) (p : Interval R) : Interval R :=
  ⟨R - (p : ℝ), ⟨sub_nonneg.mpr p.property.2, by linarith [p.property.1]⟩⟩

/-- Exactly the equality measures in Theorem 3.1. -/
def HyperbolicEquality (R : ℝ) (μ : ProbabilityMeasure (Interval R)) : Prop :=
  (∃ p : Interval R, μ = diracProbability p) ∨
    ∃ p : Interval R, μ = mixProbability (diracProbability p)
      (diracProbability (reflectInterval R p)) (1 / 2) ⟨by norm_num, by norm_num⟩

theorem hyperbolicObjective_dirac_zero (R : ℝ) (p : Interval R) :
    hyperbolicObjective R (diracProbability p) = 0 := by
  have h := hyperbolicObjective_pair R p p 0 ⟨le_rfl, zero_le_one⟩
  erw [mixProbability_zero] at h
  rw [h, twoPointObjective_eq_log_ratio p.property p.property
    (by norm_num : (1 - (0 : ℝ)) ∈ Icc 0 1), twoPointRatio_same p.property, Real.log_one]

theorem hyperbolicObjective_balanced_zero (R : ℝ) (p : Interval R) :
    hyperbolicObjective R (mixProbability (diracProbability p)
      (diracProbability (reflectInterval R p)) (1 / 2) ⟨by norm_num, by norm_num⟩) = 0 := by
  erw [hyperbolicObjective_pair, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
    twoPointObjective_eq_log_ratio p.property (reflectInterval R p).property
      (by norm_num : (1 / 2 : ℝ) ∈ Icc 0 1)]
  have he : twoPointRatio R p (reflectInterval R p) (1 / 2) = 1 :=
    (twoPointRatio_half_eq_one_iff _ _ _).mpr (Or.inr (by change (p : ℝ) + (R - (p : ℝ)) = R; ring))
  rw [he, Real.log_one]

theorem equality_of_pair_objective_zero (R : ℝ) (p q : Interval R) (hpq : p ≤ q)
    (t : ℝ) (ht : t ∈ Icc 0 1)
    (hzero : hyperbolicObjective R (mixProbability (diracProbability p) (diracProbability q) t ht) = 0) :
    HyperbolicEquality R (mixProbability (diracProbability p) (diracProbability q) t ht) := by
  have hw : 1 - t ∈ Icc (0 : ℝ) 1 := ⟨sub_nonneg.mpr ht.2, by linarith [ht.1]⟩
  rw [hyperbolicObjective_pair, twoPointObjective_eq_log_ratio p.property q.property hw] at hzero
  have heq : twoPointRatio R p q (1 - t) = 1 := by
    have h := congrArg Real.exp hzero
    rwa [Real.exp_log (twoPointRatio_pos p.property q.property hw), Real.exp_zero] at h
  rcases (twoPointRatio_eq_one_iff p.property q.property hpq hw).mp heq with h | h | h | ⟨h, hs⟩
  · have ht1 : t = 1 := by linarith
    subst t
    exact Or.inl ⟨q, mixProbability_one _ _ _⟩
  · have ht0 : t = 0 := by linarith
    subst t
    exact Or.inl ⟨p, mixProbability_zero _ _ _⟩
  · have hpq' : p = q := Subtype.ext h
    subst q
    exact Or.inl ⟨p, mixProbability_same _ _ _⟩
  · have ht' : t = 1 / 2 := by linarith
    have hq' : q = reflectInterval R p := Subtype.ext (by change (q : ℝ) = R - (p : ℝ); linarith)
    subst t
    subst q
    exact Or.inr ⟨p, rfl⟩

end PaperVerification.Hyperbolic

#print axioms PaperVerification.Hyperbolic.ordered_pair_mixture_of_minimizer
#print axioms PaperVerification.Hyperbolic.hyperbolicObjective_pair_nonneg
