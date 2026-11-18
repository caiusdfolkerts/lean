module
public import PaperVerification.HyperbolicFirstVariation
public import PaperVerification.HyperbolicPotential
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
@[expose] public section
/-! # Full support localization for minimizers

The exponential of minus the potential extends continuously across the singular
endpoints as a product of nonnegative real powers. This proves the support
statement, including accumulation at endpoints of measure zero, rather than
only an almost-everywhere statement.
-/

noncomputable section

namespace PaperVerification.Hyperbolic

open Real Set MeasureTheory Filter Topology

/-- Continuous exponential transform of the potential, with its correct zero
values at endpoints where the potential tends to positive infinity. -/
def potentialKernel (R A C B D F p : ℝ) : ℝ :=
  Real.cosh (2 * p - R) * Real.cosh p ^ (-(4 / F * A)) *
    Real.cosh (R - p) ^ (-(4 / F * C)) * Real.sinh p ^ (4 / F * B) *
      Real.sinh (R - p) ^ (4 / F * D)

theorem continuous_potentialKernel (R A C B D F : ℝ)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hF : 0 < F) :
    Continuous (potentialKernel R A C B D F) := by
  have hscale : 0 ≤ 4 / F := (div_pos (by norm_num) hF).le
  exact ((((Real.continuous_cosh.comp ((continuous_const.mul continuous_id).sub continuous_const)).mul
    (Real.continuous_cosh.rpow_const (fun p => Or.inl (Real.cosh_pos p).ne'))).mul
    ((Real.continuous_cosh.comp (continuous_const.sub continuous_id)).rpow_const
      (fun p => Or.inl (Real.cosh_pos (R - p)).ne'))).mul
    (Real.continuous_sinh.rpow_const (fun _ => Or.inr (mul_nonneg hscale hB)))).mul
    ((Real.continuous_sinh.comp (continuous_const.sub continuous_id)).rpow_const
      (fun _ => Or.inr (mul_nonneg hscale hD)))

private theorem rpow_eq_exp_log_mul_of_admissible (x k : ℝ) (h : 0 < x ∨ k = 0) :
    x ^ k = Real.exp (Real.log x * k) := by
  rcases h with h | rfl
  · exact Real.rpow_def_of_pos h _
  · simp only [Real.rpow_zero, mul_zero, Real.exp_zero]

theorem potentialKernel_eq_exp_neg (R A C B D F p : ℝ)
    (hB : B = 0 ∨ 0 < p) (hD : D = 0 ∨ p < R) :
    potentialKernel R A C B D F p = Real.exp (-variationPotential R A C B D F p) := by
  have hb : 0 < Real.sinh p ∨ 4 / F * B = 0 := by
    rcases hB with h | h
    · exact Or.inr (by rw [h, mul_zero])
    · exact Or.inl (Real.sinh_pos_iff.mpr h)
  have hd : 0 < Real.sinh (R - p) ∨ 4 / F * D = 0 := by
    rcases hD with h | h
    · exact Or.inr (by rw [h, mul_zero])
    · exact Or.inl (Real.sinh_pos_iff.mpr (sub_pos.mpr h))
  unfold potentialKernel
  rw [Real.rpow_def_of_pos (Real.cosh_pos p), Real.rpow_def_of_pos (Real.cosh_pos (R - p)),
    rpow_eq_exp_log_mul_of_admissible _ _ hb, rpow_eq_exp_log_mul_of_admissible _ _ hd]
  nth_rw 1 [← Real.exp_log (Real.cosh_pos (2 * p - R))]
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  unfold variationPotential
  ring

theorem admissible_of_potentialKernel_pos (R A C B D F : ℝ) (p : Interval R)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hF : 0 < F)
    (hK : 0 < potentialKernel R A C B D F p) :
    (B = 0 ∨ 0 < (p : ℝ)) ∧ (D = 0 ∨ (p : ℝ) < R) := by
  constructor
  · by_cases hz : B = 0
    · exact Or.inl hz
    · right
      by_contra hp
      have hp0 : (p : ℝ) = 0 := le_antisymm (le_of_not_gt hp) p.property.1
      have hb : 0 < 4 / F * B :=
        mul_pos (div_pos (by norm_num) hF) (lt_of_le_of_ne hB (Ne.symm hz))
      simp only [potentialKernel, hp0, Real.sinh_zero, Real.zero_rpow hb.ne', mul_zero,
        zero_mul] at hK
      exact lt_irrefl _ hK
  · by_cases hz : D = 0
    · exact Or.inl hz
    · right
      by_contra hp
      have hpR : (p : ℝ) = R := le_antisymm p.property.2 (le_of_not_gt hp)
      have hd : 0 < 4 / F * D :=
        mul_pos (div_pos (by norm_num) hF) (lt_of_le_of_ne hD (Ne.symm hz))
      simp only [potentialKernel, hpR, sub_self, Real.sinh_zero,
        Real.zero_rpow hd.ne', mul_zero] at hK
      exact lt_irrefl _ hK

def measureKernel (R : ℝ) (μ : ProbabilityMeasure (Interval R)) (p : ℝ) : ℝ :=
  potentialKernel R (geometricMoment 4 (intervalCosh R) μ)
    (geometricMoment 4 (intervalReflectedCosh R) μ)
    (geometricMoment 4 (intervalSinh R) μ)
    (geometricMoment 4 (intervalReflectedSinh R) μ) (hyperbolicNumerator R μ) p

theorem support_admissible_and_potential_eq_entropy
    (R : ℝ) (hR : 0 < R) (μ : ProbabilityMeasure (Interval R))
    (hmin : ∀ ν : ProbabilityMeasure (Interval R), hyperbolicObjective R μ ≤ hyperbolicObjective R ν)
    (p : Interval R) (hp : p ∈ (μ : Measure (Interval R)).support) :
    AdmissiblePoint R μ p ∧ measurePotential R μ p = potentialEntropy R μ := by
  have hcont : Continuous (fun q : Interval R => measureKernel R μ q) :=
    (continuous_potentialKernel R _ _ _ _ _
      (geometricMoment_nonneg 4 (intervalSinh R) μ)
      (geometricMoment_nonneg 4 (intervalReflectedSinh R) μ)
      (hyperbolicNumerator_pos R hR μ)).comp continuous_subtype_val
  have hae : ∀ᵐ (q : Interval R) ∂(μ : Measure (Interval R)),
      measureKernel R μ q = Real.exp (-potentialEntropy R μ) := by
    filter_upwards [ae_admissiblePoint R μ, ae_measurePotential_eq_entropy_of_minimizer R hR μ hmin]
      with q hq hlevel
    have he := potentialKernel_eq_exp_neg R (geometricMoment 4 (intervalCosh R) μ)
      (geometricMoment 4 (intervalReflectedCosh R) μ)
      (geometricMoment 4 (intervalSinh R) μ) (geometricMoment 4 (intervalReflectedSinh R) μ)
      (hyperbolicNumerator R μ) (q : ℝ) hq.1 hq.2
    change measureKernel R μ q = Real.exp (-measurePotential R μ q) at he
    rw [he, hlevel]
  have hclosed : IsClosed {q : Interval R | measureKernel R μ q = Real.exp (-potentialEntropy R μ)} :=
    isClosed_eq hcont continuous_const
  have heq := (Measure.support_subset_of_isClosed hclosed hae) hp
  have hpositive : 0 < measureKernel R μ p := heq.symm ▸ Real.exp_pos _
  have hadm : AdmissiblePoint R μ p :=
    admissible_of_potentialKernel_pos R _ _ _ _ _ p
      (geometricMoment_nonneg 4 (intervalSinh R) μ)
      (geometricMoment_nonneg 4 (intervalReflectedSinh R) μ)
      (hyperbolicNumerator_pos R hR μ) hpositive
  refine ⟨hadm, ?_⟩
  have hexp := (potentialKernel_eq_exp_neg R (geometricMoment 4 (intervalCosh R) μ)
    (geometricMoment 4 (intervalReflectedCosh R) μ)
    (geometricMoment 4 (intervalSinh R) μ) (geometricMoment 4 (intervalReflectedSinh R) μ)
    (hyperbolicNumerator R μ) (p : ℝ) hadm.1 hadm.2).symm.trans heq
  have hneg := Real.exp_injective hexp
  change -measurePotential R μ p = -potentialEntropy R μ at hneg
  linarith

/-- There are no three ordered support points of a minimizing probability measure. -/
theorem no_three_support_points_of_minimizer
    (R : ℝ) (hR : 0 < R) (μ : ProbabilityMeasure (Interval R))
    (hmin : ∀ ν : ProbabilityMeasure (Interval R), hyperbolicObjective R μ ≤ hyperbolicObjective R ν)
    (a b c : Interval R)
    (ha : a ∈ (μ : Measure (Interval R)).support)
    (hb : b ∈ (μ : Measure (Interval R)).support)
    (hc : c ∈ (μ : Measure (Interval R)).support) (hab : a < b) (hbc : b < c) : False := by
  obtain ⟨haadm, halevel⟩ := support_admissible_and_potential_eq_entropy R hR μ hmin a ha
  obtain ⟨hbadm, hblevel⟩ := support_admissible_and_potential_eq_entropy R hR μ hmin b hb
  obtain ⟨hcadm, hclevel⟩ := support_admissible_and_potential_eq_entropy R hR μ hmin c hc
  have hA := one_le_geometricMoment_of_one_le 4 (by norm_num) (intervalCosh R) μ
    (fun p => Real.one_le_cosh (p : ℝ))
  have hC := one_le_geometricMoment_of_one_le 4 (by norm_num) (intervalReflectedCosh R) μ
    (fun p => Real.one_le_cosh (R - (p : ℝ)))
  apply no_three_minima_variationPotential R
    (geometricMoment 4 (intervalCosh R) μ) (geometricMoment 4 (intervalReflectedCosh R) μ)
    (geometricMoment 4 (intervalSinh R) μ) (geometricMoment 4 (intervalReflectedSinh R) μ)
    (hyperbolicNumerator R μ) a b c (by linarith) (by linarith)
    (geometricMoment_nonneg 4 (intervalSinh R) μ)
    (geometricMoment_nonneg 4 (intervalReflectedSinh R) μ)
    (hyperbolicNumerator_pos R hR μ) a.property.1 c.property.2 hab hbc haadm.1 hcadm.2
  · intro x hx
    let q : Interval R := ⟨x, ⟨a.property.1.trans hx.1, hx.2.trans c.property.2⟩⟩
    have hq : AdmissiblePoint R μ q := by
      constructor
      · exact haadm.1.imp id (fun h => h.trans_le hx.1)
      · exact hcadm.2.imp id (fun h => hx.2.trans_lt h)
    change measurePotential R μ a ≤ measurePotential R μ q
    rw [halevel]
    exact potentialEntropy_le_measurePotential_of_minimizer R hR μ hmin q hq
  · exact hblevel.trans halevel.symm
  · exact hclevel.trans halevel.symm

private theorem subset_pair_of_no_three_ordered {α : Type*} [LinearOrder α]
    {s : Set α} (hno : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, a < b → b < c → False)
    {p q : α} (hp : p ∈ s) (hq : q ∈ s) (hpq : p < q) : s ⊆ {p, q} := by
  intro z hz
  by_cases hzp : z = p
  · simp only [hzp, mem_insert_iff, true_or]
  by_cases hzq : z = q
  · simp only [hzq, mem_insert_iff, mem_singleton_iff, or_true]
  by_cases hzp' : z < p
  · exact False.elim (hno z hz p hp q hq hzp' hpq)
  have hpz : p < z := lt_of_le_of_ne (le_of_not_gt hzp') (Ne.symm hzp)
  by_cases hzq' : z < q
  · exact False.elim (hno p hp z hz q hq hpz hzq')
  have hqz : q < z := lt_of_le_of_ne (le_of_not_gt hzq') (Ne.symm hzq)
  exact False.elim (hno p hp q hq z hz hpq hqz)

/-- Lemma 4.1: every global minimizer is supported on at most two points,
with no restriction on the original probability measure. -/
theorem support_subset_pair_of_minimizer
    (R : ℝ) (hR : 0 < R) (μ : ProbabilityMeasure (Interval R))
    (hmin : ∀ ν : ProbabilityMeasure (Interval R), hyperbolicObjective R μ ≤ hyperbolicObjective R ν) :
    ∃ p q : Interval R, (μ : Measure (Interval R)).support ⊆ {p, q} := by
  classical
  let s := (μ : Measure (Interval R)).support
  have hμ : (μ : Measure (Interval R)) ≠ 0 := by
    intro hz
    have hu : (μ : Measure (Interval R)) univ = 1 := measure_univ
    simpa [hz] using hu
  obtain ⟨p, hp⟩ := Measure.nonempty_support hμ
  by_cases hs : s.Subsingleton
  · refine ⟨p, p, ?_⟩
    intro q hq
    have hqp := hs hq hp
    simp only [hqp, mem_insert_iff, true_or]
  · have hex : ∃ q ∈ s, q ≠ p := by
      by_contra hn
      apply hs
      intro x hx y hy
      have hx' : x = p := by by_contra h; exact hn ⟨x, hx, h⟩
      have hy' : y = p := by by_contra h; exact hn ⟨y, hy, h⟩
      exact hx'.trans hy'.symm
    obtain ⟨q, hq, hqp⟩ := hex
    have hno : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, a < b → b < c → False :=
      fun a ha b hb c hc hab hbc => no_three_support_points_of_minimizer R hR μ hmin a b c ha hb hc hab hbc
    rcases lt_or_gt_of_ne hqp with hqp | hpq
    · exact ⟨q, p, subset_pair_of_no_three_ordered hno hq hp hqp⟩
    · exact ⟨p, q, subset_pair_of_no_three_ordered hno hp hq hpq⟩

end PaperVerification.Hyperbolic

#print axioms PaperVerification.Hyperbolic.support_subset_pair_of_minimizer
