module
public import PaperVerification.HyperbolicStieltjes
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Normed.Group.Bounded
@[expose] public section
/-! # Strict scale comparison

Differentiation of the compact resolvent integral is justified by a uniform
bound on a compact rectangle. The Stieltjes identities then give the exact
strict monotonicity in both weight ranges.
-/

noncomputable section

namespace PaperVerification.Hyperbolic

open Real Set MeasureTheory intervalIntegral Filter Topology

/-- A compact-rectangle form of differentiation under an interval integral. -/
theorem hasDerivAt_integral_of_compact_rectangle
    {a b l u x : ℝ} (hab : a ≤ b) (hx : x ∈ Ioo l u)
    {F F' : ℝ → ℝ → ℝ}
    (hF : ∀ y ∈ Icc l u, ContinuousOn (F y) (Icc a b))
    (hF' : ContinuousOn (fun p : ℝ × ℝ => F' p.1 p.2) (Icc l u ×ˢ Icc a b))
    (hd : ∀ y ∈ Icc l u, ∀ s ∈ Icc a b, HasDerivAt (fun y => F y s) (F' y s) y) :
    HasDerivAt (fun y => ∫ s in a..b, F y s) (∫ s in a..b, F' x s) x := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hF'
  have hxi : x ∈ Icc l u := ⟨hx.1.le, hx.2.le⟩
  have hF'x : ContinuousOn (F' x) (Icc a b) :=
    hF'.comp (continuousOn_const.prodMk continuousOn_id) (fun s hs => ⟨hxi, hs⟩)
  apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := fun _ => C) (Ioo_mem_nhds hx.1 hx.2) ?_
    ((hF x hxi).intervalIntegrable_of_Icc hab) ?_ ?_ intervalIntegrable_const ?_).2
  · filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    rw [uIoc_of_le hab]
    exact ((hF y ⟨hy.1.le, hy.2.le⟩).mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · rw [uIoc_of_le hab]
    exact (hF'x.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · apply Filter.Eventually.of_forall
    intro s hs y hy
    rw [uIoc_of_le hab] at hs
    exact hC (y, s) ⟨⟨hy.1.le, hy.2.le⟩, ⟨hs.1.le, hs.2⟩⟩
  · apply Filter.Eventually.of_forall
    intro s hs y hy
    apply hd y ⟨hy.1.le, hy.2.le⟩ s
    rw [uIoc_of_le hab] at hs
    exact ⟨hs.1.le, hs.2⟩

def resolventIntegral (a b r x : ℝ) : ℝ :=
  ∫ s in a..b, branchDensity a b r s * resolventKernel s x

def resolventDomain (a b : ℝ) : Set ℝ := Ioo 0 (min (a ^ 2) (1 / b ^ 2))

theorem resolventDomain_iff {a b x : ℝ} (hb : 0 < b) :
    x ∈ resolventDomain a b ↔ 0 < x ∧ x < a ^ 2 ∧ b ^ 2 * x < 1 := by
  have hb2 : 0 < b ^ 2 := sq_pos_of_ne_zero hb.ne'
  simp only [resolventDomain, mem_Ioo, lt_min_iff]
  constructor
  · rintro ⟨hx, hxa, hxb⟩
    exact ⟨hx, hxa, by simpa only [mul_comm] using (lt_div_iff₀ hb2).mp hxb⟩
  · rintro ⟨hx, hxa, hxb⟩
    exact ⟨hx, hxa, (lt_div_iff₀ hb2).mpr (by simpa only [mul_comm] using hxb)⟩

theorem continuousOn_resolventKernel_in_s {a b x : ℝ}
    (ha : 0 < a) (hx : 0 < x) (hxa : x < a ^ 2) (hxb : b ^ 2 * x < 1) :
    ContinuousOn (fun s => resolventKernel s x) (Icc a b) := by
  have hs0 : ∀ s ∈ Icc a b, s ≠ 0 := fun s hs => (ha.trans_le hs.1).ne'
  have hden : ∀ s ∈ Icc a b, (s ^ 2 - x) * (1 - s ^ 2 * x) ≠ 0 := by
    intro s hs
    obtain ⟨h₁, h₂⟩ := resolvent_denominators_pos ha hx hxa hxb hs
    exact mul_ne_zero h₁.ne' h₂.ne'
  unfold resolventKernel
  fun_prop (disch := aesop)

theorem continuousOn_density_resolventKernel {a b r x : ℝ}
    (ha : 0 < a) (hr : r ∈ Ioo 0 2) (hx : 0 < x)
    (hxa : x < a ^ 2) (hxb : b ^ 2 * x < 1) :
    ContinuousOn (fun s => branchDensity a b r s * resolventKernel s x) (Icc a b) :=
  (continuous_branchDensity a b r ⟨hr.1, by linarith [hr.2]⟩).continuousOn.mul
    (continuousOn_resolventKernel_in_s ha hx hxa hxb)

theorem hasDerivAt_resolventIntegral {a b r x : ℝ}
    (ha : 0 < a) (hab : a < b) (hr : r ∈ Ioo 0 2)
    (hx : x ∈ resolventDomain a b) :
    HasDerivAt (resolventIntegral a b r)
      (∫ s in a..b, branchDensity a b r s * resolventSlope s x) x := by
  have hb : 0 < b := ha.trans hab
  obtain ⟨hx0, hxa, hxb⟩ := (resolventDomain_iff hb).mp hx
  let M := min (a ^ 2) (1 / b ^ 2)
  let l := x / 2
  let u := (x + M) / 2
  have hxM : x < M := hx.2
  have hlu : x ∈ Ioo l u := by dsimp [l, u]; constructor <;> linarith
  have hdom : ∀ y ∈ Icc l u, y ∈ resolventDomain a b := by
    intro y hy
    change 0 < y ∧ y < M
    change x / 2 ≤ y ∧ y ≤ (x + M) / 2 at hy
    constructor <;> linarith only [hy.1, hy.2, hx0, hxM]
  have hcontF : ∀ y ∈ Icc l u,
      ContinuousOn (fun s => branchDensity a b r s * resolventKernel s y) (Icc a b) := by
    intro y hy
    obtain ⟨hy0, hya, hyb⟩ := (resolventDomain_iff hb).mp (hdom y hy)
    exact continuousOn_density_resolventKernel ha hr hy0 hya hyb
  have hcontF' : ContinuousOn
      (fun p : ℝ × ℝ => branchDensity a b r p.2 * resolventSlope p.2 p.1)
      (Icc l u ×ˢ Icc a b) := by
    apply ((continuous_branchDensity a b r ⟨hr.1, by linarith [hr.2]⟩).comp continuous_snd).continuousOn.mul
    unfold resolventSlope
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro p hp
      obtain ⟨hy0, hya, hyb⟩ := (resolventDomain_iff hb).mp (hdom p.1 hp.1)
      obtain ⟨h₁, h₂⟩ := resolvent_denominators_pos ha hy0 hya hyb hp.2
      exact mul_ne_zero (pow_ne_zero _ h₁.ne') (pow_ne_zero _ h₂.ne')
  exact hasDerivAt_integral_of_compact_rectangle hab.le hlu hcontF hcontF'
    (fun y hy s hs => by
      obtain ⟨hy0, hya, hyb⟩ := (resolventDomain_iff hb).mp (hdom y hy)
      obtain ⟨h₁, h₂⟩ := resolvent_denominators_pos ha hy0 hya hyb hs
      exact (hasDerivAt_resolventKernel s y (ha.trans_le hs.1).ne' h₁.ne' h₂.ne').const_mul _)

theorem strictAntiOn_resolventIntegral {a b r : ℝ}
    (ha : 0 < a) (hab : a < b) (hab1 : a * b < 1) (hr : r ∈ Ioo 0 2) :
    StrictAntiOn (resolventIntegral a b r) (resolventDomain a b) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo _ _)
    (fun x hx => (hasDerivAt_resolventIntegral ha hab hr hx).continuousAt.continuousWithinAt)
  intro x hx
  have hx' : x ∈ resolventDomain a b := interior_subset hx
  rw [(hasDerivAt_resolventIntegral ha hab hr hx').deriv]
  obtain ⟨hx0, hxa, hxb⟩ := (resolventDomain_iff (ha.trans hab)).mp hx'
  exact integral_resolventSlope_neg ha hab hab1 hr hx0 hxa hxb

theorem scale_square_mem_resolventDomain {a b z : ℝ}
    (ha : 0 < a) (hab : a < b) (hz : ScaleDomain a b z) :
    z ^ 2 ∈ resolventDomain a b := by
  apply (resolventDomain_iff (ha.trans hab)).mpr
  refine ⟨sq_pos_of_ne_zero hz.1.ne', (sq_lt_sq₀ hz.1.le ha.le).mpr hz.2.1, ?_⟩
  have hprod : 0 < b * z := mul_pos (ha.trans hab) hz.1
  have hsq : (b * z) ^ 2 < 1 :=
    (sq_lt_one_iff_abs_lt_one (b * z)).mpr (by rw [abs_of_pos hprod]; exact hz.2.2)
  simpa only [mul_pow] using hsq

theorem integral_kernel_difference {a b r z y : ℝ}
    (ha : 0 < a) (hab : a < b) (hr : r ∈ Ioo 0 2)
    (hz : z ∈ resolventDomain a b) (hy : y ∈ resolventDomain a b) :
    (∫ u in a..b, branchDensity a b r u * (resolventKernel u z - resolventKernel u y)) =
      resolventIntegral a b r z - resolventIntegral a b r y := by
  obtain ⟨hz0, hza, hzb⟩ := (resolventDomain_iff (ha.trans hab)).mp hz
  obtain ⟨hy0, hya, hyb⟩ := (resolventDomain_iff (ha.trans hab)).mp hy
  unfold resolventIntegral
  simp_rw [mul_sub]
  exact intervalIntegral.integral_sub
    ((continuousOn_density_resolventKernel ha hr hz0 hza hzb).intervalIntegrable_of_Icc hab.le)
    ((continuousOn_density_resolventKernel ha hr hy0 hya hyb).intervalIntegrable_of_Icc hab.le)

/-- Strict increase in the exponential scale for the entire lower-weight range. -/
theorem quarticTransform_lt_of_r_lt_one {a b r z y : ℝ}
    (ha : 0 < a) (hab : a < b) (hab1 : a * b < 1) (hr : r ∈ Ioo 0 1)
    (hz : ScaleDomain a b z) (hy : ScaleDomain a b y) (hzy : z < y) :
    quarticTransform z (branchPower a b r) < quarticTransform y (branchPower a b r) := by
  have hr2 : r ∈ Ioo 0 2 := ⟨hr.1, hr.2.trans (by norm_num)⟩
  have hz2 := scale_square_mem_resolventDomain ha hab hz
  have hy2 := scale_square_mem_resolventDomain ha hab hy
  have hsq : z ^ 2 < y ^ 2 := (sq_lt_sq₀ hz.1.le hy.1.le).mpr hzy
  have hdiff := strictAntiOn_resolventIntegral ha hab hab1 hr2 hz2 hy2 hsq
  apply sub_neg.mp
  rw [quarticTransform_difference_stieltjes01 ha hab hr hz hy,
    integral_kernel_difference ha hab hr2 hz2 hy2]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos (inv_pos.mpr (stieltjesNormalizer_pos hr)))
    (sub_pos.mpr hdiff)

/-- Strict decrease in the exponential scale for the entire upper-weight range. -/
theorem quarticTransform_lt_of_one_lt_r {a b r z y : ℝ}
    (ha : 0 < a) (hab : a < b) (hab1 : a * b < 1) (hr : r ∈ Ioo 1 2)
    (hz : ScaleDomain a b z) (hy : ScaleDomain a b y) (hzy : z < y) :
    quarticTransform y (branchPower a b r) < quarticTransform z (branchPower a b r) := by
  have hr2 : r ∈ Ioo 0 2 := ⟨zero_lt_one.trans hr.1, hr.2⟩
  have hz2 := scale_square_mem_resolventDomain ha hab hz
  have hy2 := scale_square_mem_resolventDomain ha hab hy
  have hsq : z ^ 2 < y ^ 2 := (sq_lt_sq₀ hz.1.le hy.1.le).mpr hzy
  have hdiff := strictAntiOn_resolventIntegral ha hab hab1 hr2 hz2 hy2 hsq
  apply sub_pos.mp
  rw [quarticTransform_difference_stieltjes12 ha hab hr hz hy,
    integral_kernel_difference ha hab hr2 hz2 hy2]
  exact mul_pos (inv_pos.mpr (stieltjesNormalizer_pos (by constructor <;> linarith [hr.1, hr.2])))
    (sub_pos.mpr hdiff)

end PaperVerification.Hyperbolic

#print axioms PaperVerification.Hyperbolic.strictAntiOn_resolventIntegral
#print axioms PaperVerification.Hyperbolic.quarticTransform_lt_of_r_lt_one
#print axioms PaperVerification.Hyperbolic.quarticTransform_lt_of_one_lt_r
