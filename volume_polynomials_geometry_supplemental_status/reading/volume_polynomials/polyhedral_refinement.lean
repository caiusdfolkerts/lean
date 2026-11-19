module

public import VolumePolynomials.SimpleSupportChamber
public import VolumePolynomials.BodyOperations
public import VolumePolynomials.LinearFrame
public import Mathlib.Tactic.Ring

@[expose] public section
set_option autoImplicit false

/-!
# Simple refinements of a fixed bounded halfspace system

The neighborhood used to choose a generic perturbation excludes every basis
that was infeasible in the original system. At a simple vertex, maximizing
linear functionals have nonnegative coefficients in the active normal basis.
This is proved by actual short feasible segments, without invoking an
unformalized normal-cone or linear-programming theorem.
-/

noncomputable section
open Set Filter Module Metric
open scoped Topology Pointwise BigOperators

namespace VolumePolynomials.PolyhedralSupport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

def toBody (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hpos : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (h : ι → ℝ) (hh : ∀ i, 0 < h i) : ConvexBody E where
  carrier := body l h
  convex' := body_convex l h
  isCompact' := isCompact_body_of_positive_reference l h₀ hpos hc h
  nonempty' := ⟨0, fun i => by simpa only [map_zero] using (hh i).le⟩

theorem toBody_isFiniteHull (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hpos : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (h : ι → ℝ) (hh : ∀ i, 0 < h i) :
    PolytopeGeometry.IsFiniteHull (toBody l h₀ hpos hc h hh : Set E) := by
  first
  | exact ⟨(body l h).extremePoints ℝ, finite_extremePoints l h,
      body_eq_convexHull_extremePoints l h
        (isCompact_body_of_positive_reference l h₀ hpos hc h)⟩

def refinementRegion (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ) : Set (ι → ℝ) :=
  {h | feasibleBases l h ⊆ feasibleBases l h₀}

theorem isClosed_feasibleBasis (l : ι → E →L[ℝ] ℝ) (b : BasisIndex l) :
    IsClosed {h | b ∈ feasibleBases l h} := by
  first
  | change IsClosed {h | ∀ i, l i (vertexMap l b h) ≤ h i}
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i =>
      isClosed_le ((l i).continuous.comp (vertexMap l b).continuous) (continuous_apply i)

theorem isOpen_refinementRegion (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ) :
    IsOpen (refinementRegion l h₀) := by
  first
  | classical
    have he : refinementRegion l h₀ = ⋂ b : BasisIndex l,
        if b ∈ feasibleBases l h₀ then Set.univ else {h | b ∈ feasibleBases l h}ᶜ := by
      ext h
      simp only [refinementRegion, mem_setOf_eq, Set.subset_def, mem_iInter]
      apply forall_congr'
      intro b
      by_cases hb : b ∈ feasibleBases l h₀ <;> simp [hb]
    rw [he]
    apply isOpen_iInter_of_finite
    intro b
    split_ifs
    · exact isOpen_univ
    · exact (isClosed_feasibleBasis l b).isOpen_compl

theorem isOpen_positiveHeights : IsOpen {h : ι → ℝ | ∀ i, 0 < h i} := by
  first
  | simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)

/-- A bounded system with positive heights has a generic positive refinement
whose every feasible normal basis was already feasible in the original body. -/
theorem exists_generic_refinement (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hpos : ∀ i, 0 < h₀ i) :
    ∃ h : ι → ℝ, Generic l h ∧ (∀ i, 0 < h i) ∧
      feasibleBases l h ⊆ feasibleBases l h₀ := by
  first
  | have ho : IsOpen ({h : ι → ℝ | ∀ i, 0 < h i} ∩ refinementRegion l h₀) :=
      isOpen_positiveHeights.inter (isOpen_refinementRegion l h₀)
    obtain ⟨h, hg, hh⟩ := (dense_generic l).exists_mem_open ho ⟨h₀, hpos, Set.Subset.rfl⟩
    exact ⟨h, hg, hh.1, hh.2⟩

def StrictFacets (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ) : Prop :=
  ∀ i, ∃ x : E, l i x = h i ∧ ∀ j, j ≠ i → l j x < h j

theorem eventually_strictFacets (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    (hn : ∀ i, l i ≠ 0) (hs : StrictFacets l h₀) :
    ∀ᶠ h : ι → ℝ in 𝓝 h₀, StrictFacets l h := by
  first
  | choose v hv using fun i => LinearFrame.exists_unit_value (l i) (hn i)
    choose x hxi hxj using hs
    have he : ∀ᶠ h : ι → ℝ in 𝓝 h₀, ∀ i j, j ≠ i →
        l j (x i + (h i - h₀ i) • v i) < h j := by
      apply Filter.eventually_all.mpr
      intro i
      apply Filter.eventually_all.mpr
      intro j
      by_cases hji : j = i
      · exact Filter.Eventually.of_forall fun _ hn => (hn hji).elim
      · have ht : ∀ᶠ h : ι → ℝ in 𝓝 h₀,
            l j (x i + (h i - h₀ i) • v i) < h j :=
          (isOpen_lt (by fun_prop) (continuous_apply j)).mem_nhds (by
            change l j (x i + (h₀ i - h₀ i) • v i) < h₀ j
            simpa only [sub_self, zero_smul, add_zero] using hxj i j hji)
        filter_upwards [ht] with h hh
        exact fun _ => hh
    filter_upwards [he] with h hh
    intro i
    refine ⟨x i + (h i - h₀ i) • v i, ?_, hh i⟩
    rw [map_add, map_smul, smul_eq_mul, hxi i, hv i, mul_one]
    ring

/-- Generic perturbation preserving every genuine facet, not merely the
bounded body. This supplies strictly positive facet measures in the operator. -/
theorem exists_generic_refinement_strictFacets (l : ι → E →L[ℝ] ℝ)
    (h₀ : ι → ℝ) (hn : ∀ i, l i ≠ 0) (hpos : ∀ i, 0 < h₀ i)
    (hs : StrictFacets l h₀) :
    ∃ h : ι → ℝ, Generic l h ∧ (∀ i, 0 < h i) ∧
      feasibleBases l h ⊆ feasibleBases l h₀ ∧ StrictFacets l h := by
  first
  | have he : ∀ᶠ h : ι → ℝ in 𝓝 h₀,
        (∀ i, 0 < h i) ∧ feasibleBases l h ⊆ feasibleBases l h₀ ∧ StrictFacets l h := by
      filter_upwards [isOpen_positiveHeights.mem_nhds hpos,
        (isOpen_refinementRegion l h₀).mem_nhds (show h₀ ∈ refinementRegion l h₀ from Set.Subset.rfl),
        eventually_strictFacets l h₀ hn hs] with h hp hr hf
      exact ⟨hp, hr, hf⟩
    obtain ⟨U, hUsub, hUopen, hUmem⟩ := _root_.mem_nhds_iff.mp he
    obtain ⟨h, hg, hh⟩ := (dense_generic l).exists_mem_open hUopen ⟨h₀, hUmem⟩
    exact ⟨h, hg, hUsub hh⟩

def basisDirection (l : ι → E →L[ℝ] ℝ) (b : BasisIndex l) (j : b.val) : E :=
  (coordinates l b).symm (Pi.single j 1)

@[simp] theorem normal_basisDirection (l : ι → E →L[ℝ] ℝ)
    (b : BasisIndex l) (i j : b.val) :
    l i (basisDirection l b j) = if i = j then 1 else 0 := by
  first
  | change (coordinates l b ((coordinates l b).symm (Pi.single j 1))) i = _
    simp only [ContinuousLinearEquiv.apply_symm_apply, Pi.single_apply]

theorem sum_basisDirection (l : ι → E →L[ℝ] ℝ) (b : BasisIndex l) (x : E) :
    (∑ j : b.val, l j x • basisDirection l b j) = x := by
  first
  | apply (coordinates l b).injective
    ext i
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, coordinates_apply,
      normal_basisDirection, smul_eq_mul, mul_ite, mul_one, mul_zero]
    simp

theorem functional_expansion (l : ι → E →L[ℝ] ℝ) (b : BasisIndex l)
    (f : E →L[ℝ] ℝ) (x : E) :
    f x = ∑ j : b.val, f (basisDirection l b j) * l j x := by
  first
  | conv_lhs => rw [← sum_basisDirection l b x]
    simp only [map_sum, map_smul, smul_eq_mul, mul_comm]

theorem strict_inactive_of_generic (l : ι → E →L[ℝ] ℝ)
    (h : ι → ℝ) (hg : Generic l h) (b : BasisIndex l)
    (hb : b ∈ feasibleBases l h) (i : ι) (hi : i ∉ b.val) :
    l i (vertexMap l b h) < h i := by
  first
  | have hz := slack_ne_zero_of_generic l h hg b hi
    rw [slack_apply] at hz
    have hs : 0 ≤ h i - l i (vertexMap l b h) := sub_nonneg.mpr (hb i)
    exact sub_pos.mp (lt_of_le_of_ne hs (Ne.symm hz))

theorem exists_negative_basis_step (l : ι → E →L[ℝ] ℝ)
    (h : ι → ℝ) (b : BasisIndex l) (hb : b ∈ feasibleBases l h)
    (hstrict : ∀ i ∉ b.val, l i (vertexMap l b h) < h i) (j : b.val) :
    ∃ t : ℝ, 0 < t ∧ vertexMap l b h - t • basisDirection l b j ∈ body l h := by
  first
  | have hnear : ∀ᶠ t : ℝ in 𝓝 0, ∀ i ∉ b.val,
        l i (vertexMap l b h - t • basisDirection l b j) < h i := by
      apply Filter.eventually_all.mpr
      intro i
      by_cases hi : i ∈ b.val
      · exact Filter.Eventually.of_forall fun _ hn => (hn hi).elim
      · have he : ∀ᶠ t : ℝ in 𝓝 0,
            l i (vertexMap l b h - t • basisDirection l b j) < h i :=
          (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by
            change l i (vertexMap l b h - (0 : ℝ) • basisDirection l b j) < h i
            simpa only [zero_smul, sub_zero] using hstrict i hi)
        filter_upwards [he] with t ht
        exact fun _ => ht
    obtain ⟨ε, hε, hs⟩ := Metric.eventually_nhds_iff.mp hnear
    have ht : dist (ε / 2) 0 < ε := by
      rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
      linarith
    refine ⟨ε / 2, half_pos hε, fun i => ?_⟩
    by_cases hi : i ∈ b.val
    · rw [map_sub, map_smul, smul_eq_mul, vertexMap_active l b h ⟨i, hi⟩,
        normal_basisDirection l b ⟨i, hi⟩ j]
      split_ifs <;> nlinarith
    · exact (hs ht i hi).le

/-- The usual normal-cone statement at a simple vertex, with explicit
coefficients in the actual active normal basis. -/
theorem maximizing_coefficients_nonnegative (l : ι → E →L[ℝ] ℝ)
    (h : ι → ℝ) (b : BasisIndex l) (hb : b ∈ feasibleBases l h)
    (hstrict : ∀ i ∉ b.val, l i (vertexMap l b h) < h i)
    (f : E →L[ℝ] ℝ) (hf : ∀ x ∈ body l h, f x ≤ f (vertexMap l b h)) :
    ∀ j : b.val, 0 ≤ f (basisDirection l b j) := by
  first
  | intro j
    obtain ⟨t, ht, hstep⟩ := exists_negative_basis_step l h b hb hstrict j
    have he := hf _ hstep
    rw [map_sub, map_smul, smul_eq_mul] at he
    nlinarith

theorem functional_le_vertex_of_normal_bounds (l : ι → E →L[ℝ] ℝ)
    (b : BasisIndex l) (f : E →L[ℝ] ℝ)
    (hf : ∀ j : b.val, 0 ≤ f (basisDirection l b j))
    (h : ι → ℝ) {x : E} (hx : ∀ j : b.val, l j x ≤ h j) :
    f x ≤ f (vertexMap l b h) := by
  first
  | rw [functional_expansion l b f x, functional_expansion l b f (vertexMap l b h)]
    apply Finset.sum_le_sum
    intro j _
    rw [vertexMap_active]
    exact mul_le_mul_of_nonneg_left (hx j) (hf j)

theorem exists_maximizing_basis (l : ι → E →L[ℝ] ℝ)
    (h : ι → ℝ) (hc : IsCompact (body l h)) (hne : (body l h).Nonempty)
    (f : E →L[ℝ] ℝ) :
    ∃ b : BasisIndex l, b ∈ feasibleBases l h ∧
      ∀ x ∈ body l h, f x ≤ f (vertexMap l b h) := by
  first
  | have he : IsExposed ℝ (body l h) (f.toExposed (body l h)) :=
      ContinuousLinearMap.toExposed.isExposed
    have hface : (f.toExposed (body l h)).Nonempty :=
      PolytopeFaces.exposed_nonempty f hc hne
    obtain ⟨x, hx⟩ := (he.isCompact hc).extremePoints_nonempty hface
    have hxbody := he.isExtreme.extremePoints_subset_extremePoints hx
    obtain ⟨b, hb⟩ := extreme_eq_vertexMap_without_generic l h hxbody
    refine ⟨b, ?_, ?_⟩
    · change vertexMap l b h ∈ body l h
      rw [hb]
      exact hxbody.1
    · intro y hy
      rw [hb]
      exact hx.1.2 y hy

end VolumePolynomials.PolyhedralSupport
