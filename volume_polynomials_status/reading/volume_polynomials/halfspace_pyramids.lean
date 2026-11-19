module

public import VolumePolynomials.PyramidVolume
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Tactic.Linarith

@[expose] public section
set_option autoImplicit false

/-!
# Volume decomposition of a bounded finite halfspace intersection

Inequalities are normalized to `lᵢ x ≤ 1`, so the origin is strictly feasible.
Every nonzero point lies on a radial segment to an active face. Distinct radial
pyramids overlap only in the kernel of a nonzero linear functional, hence in a
Lebesgue-null set. This proves the full facet-pyramid volume identity from set
geometry and measure additivity; no triangulation or divergence theorem is used.
-/

noncomputable section
open Set MeasureTheory MeasureTheory.Measure
open scoped Pointwise BigOperators

namespace VolumePolynomials.HalfspacePyramids

open PyramidVolume

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

def body (l : ι → E →L[ℝ] ℝ) : Set E := {x | ∀ i, l i x ≤ 1}

def face (l : ι → E →L[ℝ] ℝ) (i : ι) : Set E :=
  {x | x ∈ body l ∧ l i x = 1}

theorem zero_mem_body (l : ι → E →L[ℝ] ℝ) : (0 : E) ∈ body l := by
  first
  | intro i
    simp

theorem face_compact (l : ι → E →L[ℝ] ℝ) (hC : IsCompact (body l)) (i : ι) :
    IsCompact (face l i) :=
  hC.inter_right (isClosed_eq (l i).continuous continuous_const)

theorem radialHull_face_subset (l : ι → E →L[ℝ] ℝ) (i : ι) :
    radialHull (face l i) ⊆ body l := by
  first
  | rintro x ⟨⟨r, y⟩, ⟨hr, hy⟩, rfl⟩ j
    change l j (r • y) ≤ 1
    rw [map_smul, smul_eq_mul]
    exact (mul_le_mul_of_nonneg_left (hy.1 j) hr.1).trans (by simpa using hr.2)

/-- Boundedness excludes a nonzero direction on which all defining functionals
are nonpositive, since its entire positive ray would remain in the body. -/
theorem exists_positive_normal (l : ι → E →L[ℝ] ℝ) (hC : IsCompact (body l))
    {x : E} (hx : x ≠ 0) : ∃ i, 0 < l i x := by
  first
  | by_contra! h
    obtain ⟨R, hR, hbound⟩ := hC.isBounded.exists_pos_norm_le
    have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    let c : ℝ := (R + 1) / ‖x‖
    have hc : 0 < c := div_pos (by linarith) hn
    have hcx : c • x ∈ body l := by
      intro i
      rw [map_smul, smul_eq_mul]
      exact (mul_nonpos_of_nonneg_of_nonpos hc.le (h i)).trans zero_le_one
    have hb := hbound (c • x) hcx
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc] at hb
    dsimp only [c] at hb
    rw [div_mul_cancel₀ _ hn.ne'] at hb
    linarith

/-- The maximum active value provides an exact radial representation. -/
theorem mem_radialHull_face_of_ne_zero
    (l : ι → E →L[ℝ] ℝ) (hC : IsCompact (body l))
    {x : E} (hx : x ∈ body l) (hx0 : x ≠ 0) :
    ∃ i, x ∈ radialHull (face l i) := by
  first
  | classical
    obtain ⟨j, hj⟩ := exists_positive_normal l hC hx0
    obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image Finset.univ (fun i => l i x)
      ⟨j, Finset.mem_univ j⟩
    have hm : 0 < l i x := hj.trans_le (hmax j (Finset.mem_univ j))
    let y : E := (l i x)⁻¹ • x
    have hy : y ∈ face l i := by
      constructor
      · intro k
        change l k ((l i x)⁻¹ • x) ≤ 1
        rw [map_smul, smul_eq_mul]
        have h := mul_le_mul_of_nonneg_left (hmax k (Finset.mem_univ k))
          (inv_nonneg.mpr hm.le)
        simpa only [inv_mul_cancel₀ hm.ne'] using h
      · change l i ((l i x)⁻¹ • x) = 1
        rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hm.ne']
    refine ⟨i, (l i x, y), ⟨⟨hm.le, hx i⟩, hy⟩, ?_⟩
    simp only [y, smul_smul, mul_inv_cancel₀ hm.ne', one_smul]

theorem body_subset_radialHull_union_zero
    (l : ι → E →L[ℝ] ℝ) (hC : IsCompact (body l)) :
    body l ⊆ (⋃ i, radialHull (face l i)) ∪ {0} := by
  first
  | intro x hx
    by_cases hx0 : x = 0
    · exact Or.inr hx0
    · obtain ⟨i, hi⟩ := mem_radialHull_face_of_ne_zero l hC hx hx0
      exact Or.inl (mem_iUnion.mpr ⟨i, hi⟩)

/-- On the intersection of two radial pyramids the normalized facet functionals
agree. This statement also includes the common apex. -/
theorem radialHull_inter_subset_ker (l : ι → E →L[ℝ] ℝ) (i j : ι) :
    radialHull (face l i) ∩ radialHull (face l j) ⊆
      LinearMap.ker ((l i - l j).toLinearMap) := by
  first
  | rintro x ⟨⟨⟨r, a⟩, ⟨hr, ha⟩, hax⟩, ⟨⟨s, b⟩, ⟨hs, hb⟩, hbx⟩⟩
    have hi : l i x = r := by
      rw [← hax, map_smul, smul_eq_mul, ha.2, mul_one]
    have hj : l j x = s := by
      rw [← hbx, map_smul, smul_eq_mul, hb.2, mul_one]
    have hij : l i x ≤ s := by
      rw [← hbx, map_smul, smul_eq_mul]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hb.1 i) hs.1
    have hji : l j x ≤ r := by
      rw [← hax, map_smul, smul_eq_mul]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (ha.1 j) hr.1
    change l i x - l j x = 0
    linarith

section Measure

variable [FiniteDimensional ℝ E] [Nontrivial E] [MeasureSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)]

theorem radialHull_faces_aedisjoint
    (l : ι → E →L[ℝ] ℝ) (hl : Function.Injective l) :
    Pairwise (fun i j => AEDisjoint volume (radialHull (face l i)) (radialHull (face l j))) := by
  first
  | intro i j hij
    change volume (radialHull (face l i) ∩ radialHull (face l j)) = 0
    have hk : LinearMap.ker ((l i - l j).toLinearMap) ≠ ⊤ := by
      intro htop
      apply hij
      apply hl
      ext x
      have hx : x ∈ LinearMap.ker ((l i - l j).toLinearMap) := by
        rw [htop]
        exact Submodule.mem_top
      change l i x - l j x = 0 at hx
      exact sub_eq_zero.mp hx
    exact measure_mono_null (radialHull_inter_subset_ker l i j)
      (Measure.addHaar_submodule volume _ hk)

theorem volume_body_eq_radialHull_union
    (l : ι → E →L[ℝ] ℝ) (hC : IsCompact (body l)) :
    volume (body l) = volume (⋃ i, radialHull (face l i)) := by
  first
  | apply le_antisymm
    · calc
        volume (body l) ≤ volume ((⋃ i, radialHull (face l i)) ∪ {0}) :=
          measure_mono (body_subset_radialHull_union_zero l hC)
        _ ≤ volume (⋃ i, radialHull (face l i)) + volume ({0} : Set E) := measure_union_le _ _
        _ = volume (⋃ i, radialHull (face l i)) := by simp
    · apply measure_mono
      exact iUnion_subset (radialHull_face_subset l)

/-- The full finite pyramid decomposition of actual Lebesgue volume. Redundant
inequalities are allowed; their pyramids automatically have zero volume when
their faces have smaller dimension. -/
theorem realVolume_body_eq_sum_radialHull
    (l : ι → E →L[ℝ] ℝ) (hC : IsCompact (body l)) (hl : Function.Injective l) :
    volume.real (body l) = ∑ i, volume.real (radialHull (face l i)) := by
  first
  | have hmeasure : volume.real (body l) = volume.real (⋃ i, radialHull (face l i)) :=
      congrArg ENNReal.toReal (volume_body_eq_radialHull_union l hC)
    rw [hmeasure]
    classical
    simpa using measureReal_biUnion_finset₀ (μ := volume) (s := Finset.univ)
      (f := fun i => radialHull (face l i))
      (fun i _ j _ hij => radialHull_faces_aedisjoint l hl hij)
      (fun i _ => (radialHull_compact (face_compact l hC i)).measurableSet.nullMeasurableSet)
      (fun i _ => (radialHull_compact (face_compact l hC i)).measure_ne_top)

end Measure
end VolumePolynomials.HalfspacePyramids
