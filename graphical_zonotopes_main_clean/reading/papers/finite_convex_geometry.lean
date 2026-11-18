module
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
# Finite convex hulls and one-dimensional exposed faces

The argument for `mem_hull_of_maximizers` is adapted from Daniele Cappello's
Apache-2.0-licensed `FacciaArgmax` module; see THIRD_PARTY.md. Its proof needs
only a normed vector space, so the stronger inner-product hypothesis in that
source is omitted here.
-/

noncomputable section
namespace Papers.Geometry
open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mem_hull_of_maximizers (s : Finset E) (l : E →L[ℝ] ℝ) {y : E}
    (hy : y ∈ convexHull ℝ (s : Set E))
    (hmax : ∀ w ∈ convexHull ℝ (s : Set E), l w ≤ l y) :
    y ∈ convexHull ℝ {x ∈ (s : Set E) | l x = l y} := by
  classical
  rw [Finset.convexHull_eq] at hy
  obtain ⟨w, hw0, hw1, hwy⟩ := hy
  have hM : ∀ x ∈ s, l x ≤ l y := fun x hx =>
    hmax x (subset_convexHull ℝ _ hx)
  have hyrep : y = ∑ x ∈ s, w x • x := by
    rw [← hwy, Finset.centerMass_eq_of_sum_1 _ _ hw1]
    rfl
  have hly : l y = ∑ x ∈ s, w x * l x := by
    rw [hyrep, map_sum]
    congr 1
    funext x
    rw [map_smul]
    rfl
  have hactive : ∀ x ∈ s, 0 < w x → l x = l y := by
    intro x hx hwx
    by_contra hne
    have hlt : l x < l y := lt_of_le_of_ne (hM x hx) hne
    have hsum : ∑ z ∈ s, w z * l z < ∑ z ∈ s, w z * l y := by
      apply Finset.sum_lt_sum
      · intro z hz
        exact mul_le_mul_of_nonneg_left (hM z hz) (hw0 z hz)
      · exact ⟨x, hx, mul_lt_mul_of_pos_left hlt hwx⟩
    rw [← Finset.sum_mul, hw1, one_mul] at hsum
    rw [hly] at hsum
    exact lt_irrefl _ hsum
  have hzero : ∀ x ∈ s, ¬l x = l y → w x = 0 := by
    intro x hx hne
    by_contra hw
    exact hne (hactive x hx (lt_of_le_of_ne (hw0 x hx) (Ne.symm hw)))
  let sf : Finset E := s.filter (fun x => l x = l y)
  have hsub : sf ⊆ s := Finset.filter_subset _ _
  have hw1' : ∑ x ∈ sf, w x = 1 := by
    rw [← hw1]
    symm
    apply (Finset.sum_subset hsub ?_).symm
    intro x hx hnx
    apply hzero x hx
    intro heq
    exact hnx (Finset.mem_filter.mpr ⟨hx, heq⟩)
  have hyrep' : y = ∑ x ∈ sf, w x • x := by
    rw [hyrep]
    symm
    apply Finset.sum_subset hsub
    intro x hx hnx
    have : w x = 0 := by
      apply hzero x hx
      intro heq
      exact hnx (Finset.mem_filter.mpr ⟨hx, heq⟩)
    rw [this, zero_smul]
  have hmem : y ∈ convexHull ℝ (sf : Set E) := by
    rw [Finset.convexHull_eq]
    refine ⟨w, fun z hz => hw0 z (hsub hz), hw1', ?_⟩
    rw [Finset.centerMass_eq_of_sum_1 _ _ hw1']
    exact hyrep'.symm
  have hset : (sf : Set E) = {x ∈ (s : Set E) | l x = l y} := by
    ext x
    simp [sf]
  rw [← hset]
  exact hmem

theorem mem_hull_of_minimizers (s : Finset E) (l : E →L[ℝ] ℝ) {y : E}
    (hy : y ∈ convexHull ℝ (s : Set E))
    (hmin : ∀ w ∈ convexHull ℝ (s : Set E), l y ≤ l w) :
    y ∈ convexHull ℝ {x ∈ (s : Set E) | l x = l y} := by
  simpa only [ContinuousLinearMap.neg_apply, neg_inj] using
    mem_hull_of_maximizers s (-l) hy (by
      simpa only [ContinuousLinearMap.neg_apply, neg_le_neg_iff] using hmin)

theorem linear_lower_bound_on_convexHull (s : Set E) (l : E →L[ℝ] ℝ)
    (a : ℝ) (ha : ∀ x ∈ s, a ≤ l x) :
    ∀ x ∈ convexHull ℝ s, a ≤ l x :=
  convexHull_min ha (convex_halfSpace_ge (LinearMap.isLinear l.toLinearMap) a)

/-- A finite convex hull contained in an affine line is a genuine closed
segment with endpoints among its generators. Degenerate segments are allowed. -/
theorem finite_hull_parallel_eq_segment (s : Finset E) (hs : s.Nonempty)
    (δ : E) (hδ : δ ≠ 0)
    (hparallel : ∀ x ∈ s, ∀ y ∈ s, x - y ∈ Submodule.span ℝ {δ}) :
    ∃ x ∈ s, ∃ y ∈ s, convexHull ℝ (s : Set E) = segment ℝ x y := by
  classical
  have hnot : δ ∉ (⊥ : Submodule ℝ E) := by simpa using hδ
  obtain ⟨g, hg, _⟩ := Submodule.exists_le_ker_of_notMem hnot
  let l : E →ₗ[ℝ] ℝ := (g δ)⁻¹ • g
  have hl : l δ = 1 := by simp [l, hg]
  obtain ⟨x, hx, hxmin⟩ := s.exists_min_image l hs
  obtain ⟨y, hy, hymax⟩ := s.exists_max_image l hs
  have hform (z : E) (hz : z ∈ s) : z - x = (l z - l x) • δ := by
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hparallel z hz x hx)
    have he : a = l z - l x := by
      have h := congrArg l ha
      simpa only [map_smul, map_sub, smul_eq_mul, hl, mul_one] using h
    exact (he ▸ ha).symm
  have hgen : (s : Set E) ⊆ segment ℝ x y := by
    intro z hz
    have hlow := hxmin z hz
    have hupp := hymax z hz
    have hxy := hxmin y hy
    by_cases hb : l y - l x = 0
    · have hzval : l z - l x = 0 := by linarith
      have hzx : z = x := by
        have h := hform z hz
        rw [hzval, zero_smul, sub_eq_zero] at h
        exact h
      rw [hzx]
      exact left_mem_segment ℝ x y
    · have hbpos : 0 < l y - l x := lt_of_le_of_ne (sub_nonneg.mpr hxy) (Ne.symm hb)
      rw [segment_eq_image']
      refine ⟨(l z - l x) / (l y - l x), ⟨div_nonneg (sub_nonneg.mpr hlow) hbpos.le,
        (div_le_one hbpos).mpr (by linarith)⟩, ?_⟩
      change x + ((l z - l x) / (l y - l x)) • (y - x) = z
      rw [hform y hy, smul_smul, div_mul_cancel₀ _ hb, ← hform z hz]
      module
  refine ⟨x, hx, y, hy, Set.Subset.antisymm
    (convexHull_min hgen (convex_segment x y)) ?_⟩
  exact (convex_convexHull ℝ (s : Set E)).segment_subset
    (subset_convexHull ℝ _ hx) (subset_convexHull ℝ _ hy)

end Papers.Geometry
