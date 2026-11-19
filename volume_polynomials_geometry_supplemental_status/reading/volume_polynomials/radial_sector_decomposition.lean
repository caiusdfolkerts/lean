module

public import VolumePolynomials.FacetAlmostEverywhere
public import VolumePolynomials.RadialSliceIntegral

@[expose] public section
set_option autoImplicit false

/-! # Fixed radial sectors and actual volume decomposition

The sectors are truncated rays through the old facets. They cover every set
inside a fixed positive dilation of the old polytope and have pairwise null
overlaps. Each sector is integrated in its actual linear Haar frame.
-/

noncomputable section
open Set MeasureTheory Module
open scoped Pointwise BigOperators

namespace VolumePolynomials.RadialSectorDecomposition

open HalfspacePyramids LinearFrame FacetAlmostEverywhere ClippedConeVolume

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

def radialTruncation (R : ℝ) (A : Set E) : Set E :=
  (fun p : ℝ × E => p.1 • p.2) '' (Icc (0 : ℝ) R ×ˢ A)

theorem radialTruncation_compact (R : ℝ) {A : Set E} (hA : IsCompact A) :
    IsCompact (radialTruncation R A) :=
  (isCompact_Icc.prod hA).image (by fun_prop)

theorem smul_body_subset_sectors (l : ι → E →L[ℝ] ℝ)
    (hC : IsCompact (body l)) {R : ℝ} (hR : 0 ≤ R) :
    R • body l ⊆ (⋃ i, radialTruncation R (face l i)) ∪ {0} := by
  first
  | rintro x ⟨y, hy, rfl⟩
    by_cases hy0 : y = 0
    · right
      simp only [hy0, smul_zero, mem_singleton_iff]
    · obtain ⟨i, ⟨⟨r, q⟩, ⟨hr, hq⟩, hyq⟩⟩ :=
        mem_radialHull_face_of_ne_zero l hC hy hy0
      left
      apply mem_iUnion.mpr
      refine ⟨i, (R * r, q), ⟨⟨mul_nonneg hR hr.1, ?_⟩, hq⟩, ?_⟩
      · simpa only [mul_one] using mul_le_mul_of_nonneg_left hr.2 hR
      · change (R * r) • q = R • y
        have hyq' : r • q = y := hyq
        rw [mul_smul, hyq']

theorem radialTruncation_inter_subset_ker (l : ι → E →L[ℝ] ℝ)
    (R : ℝ) (i j : ι) :
    radialTruncation R (face l i) ∩ radialTruncation R (face l j) ⊆
      LinearMap.ker ((l i - l j).toLinearMap) := by
  first
  | rintro x ⟨⟨⟨r, a⟩, ⟨hr, ha⟩, hax⟩, ⟨⟨s, b⟩, ⟨hs, hb⟩, hbx⟩⟩
    have hi : l i x = r := by
      first
      | rw [← hax, map_smul, smul_eq_mul, ha.2, mul_one]
    have hj : l j x = s := by
      first
      | rw [← hbx, map_smul, smul_eq_mul, hb.2, mul_one]
    have hij : l i x ≤ s := by
      first
      | rw [← hbx, map_smul, smul_eq_mul]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (hb.1 i) hs.1
    have hji : l j x ≤ r := by
      first
      | rw [← hax, map_smul, smul_eq_mul]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (ha.1 j) hr.1
    change l i x - l j x = 0
    linarith

section Measure

variable [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]

theorem radialTruncation_faces_aedisjoint (l : ι → E →L[ℝ] ℝ)
    (hl : Function.Injective l) (R : ℝ) :
    Pairwise (fun i j => AEDisjoint volume
      (radialTruncation R (face l i)) (radialTruncation R (face l j))) := by
  first
  | intro i j hij
    have hker : LinearMap.ker ((l i - l j).toLinearMap) ≠ ⊤ := by
      first
      | intro htop
        apply hij
        apply hl
        ext x
        have hx : x ∈ LinearMap.ker ((l i - l j).toLinearMap) := by
          first
          | rw [htop]
            exact Submodule.mem_top
        change l i x - l j x = 0 at hx
        exact sub_eq_zero.mp hx
    exact measure_mono_null (radialTruncation_inter_subset_ker l R i j)
      (Measure.addHaar_submodule volume _ hker)

theorem realVolume_eq_sum_sector_intersections
    (l : ι → E →L[ℝ] ℝ) (hl : Function.Injective l)
    (hC : IsCompact (body l)) {R : ℝ} (hR : 0 ≤ R)
    {K : Set E} (hK : IsCompact K) (hKR : K ⊆ R • body l) :
    volume.real K = ∑ i, volume.real (K ∩ radialTruncation R (face l i)) := by
  first
  | classical
    let S : ι → Set E := fun i => K ∩ radialTruncation R (face l i)
    have hcover : K ⊆ (⋃ i, S i) ∪ {0} := by
      first
      | intro x hx
        rcases smul_body_subset_sectors l hC hR (hKR hx) with hi | hz
        · obtain ⟨i, hi⟩ := mem_iUnion.mp hi
          exact Or.inl (mem_iUnion.mpr ⟨i, hx, hi⟩)
        · exact Or.inr hz
    have hvol : volume K = volume (⋃ i, S i) := by
      first
      | apply le_antisymm
        · calc
            volume K ≤ volume ((⋃ i, S i) ∪ {0}) := measure_mono hcover
            _ ≤ volume (⋃ i, S i) + volume ({0} : Set E) := measure_union_le _ _
            _ = _ := by simp
        · exact measure_mono (iUnion_subset fun i => inter_subset_left)
    have hcomp (i : ι) : IsCompact (S i) :=
      hK.inter (radialTruncation_compact R (face_compact l hC i))
    have hdis : Pairwise (fun i j => AEDisjoint volume (S i) (S j)) := by
      first
      | intro i j hij
        exact (radialTruncation_faces_aedisjoint l hl R hij).mono inter_subset_right inter_subset_right
    rw [measureReal_def, hvol]
    change volume.real (⋃ i, S i) = _
    simpa only [S, Finset.mem_univ, iUnion_true] using
      measureReal_biUnion_finset₀ (μ := volume) (s := Finset.univ) (f := S)
      (fun i _ j _ hij => hdis hij)
      (fun i _ => (hcomp i).measurableSet.nullMeasurableSet)
      (fun i _ => (hcomp i).measure_ne_top)

end Measure

section Frame

variable [FiniteDimensional ℝ E]

theorem frame_radialMap (l : E →L[ℝ] ℝ) (v : E) (hv : l v = 1)
    (y : LinearMap.ker l.toLinearMap) (r : ℝ) :
    continuousEquiv l v hv (r • (v + y.val)) = radialMap (r, y) := by
  first
  | apply Prod.ext
    · change l (r • (v + y.val)) = r
      simp [map_smul, map_add, hv, y.property]
    · apply Subtype.ext
      change r • (v + y.val) - l (r • (v + y.val)) • v = r • y.val
      have hy0 : l y.val = 0 := y.property
      simp only [map_smul, map_add, hv, hy0, mul_zero, add_zero, smul_eq_mul, mul_one,
        smul_add]
      abel

theorem radialMap_mem_frame_image_iff (l : E →L[ℝ] ℝ) (v : E) (hv : l v = 1)
    (y : LinearMap.ker l.toLinearMap) (r : ℝ) (K : Set E) :
    radialMap (r, y) ∈ continuousEquiv l v hv '' K ↔ r • (v + y.val) ∈ K := by
  first
  | rw [← frame_radialMap l v hv y r]
    constructor
    · rintro ⟨x, hx, heq⟩
      have hxq := (continuousEquiv l v hv).injective heq
      simpa only [hxq] using hx
    · intro hx
      exact ⟨r • (v + y.val), hx, rfl⟩

theorem image_sector_frame (l : ι → E →L[ℝ] ℝ) (i : ι) (v : E)
    (hv : l i v = 1) (R : ℝ) :
    continuousEquiv (l i) v hv '' radialTruncation R (face l i) =
      radialMap '' (Icc (0 : ℝ) R ×ˢ facetBase l i v) := by
  first
  | ext z
    constructor
    · rintro ⟨x, ⟨⟨r, q⟩, ⟨hr, hq⟩, rfl⟩, rfl⟩
      refine ⟨(r, kernelPart (l i) v hv q), ⟨hr, ?_⟩, ?_⟩
      · have he : v + (q - v) = q := by abel
        change v + (q - l i q • v) ∈ body l
        simpa only [hq.2, one_smul, he] using hq.1
      · apply Prod.ext
        · change r = l i (r • q)
          simp only [map_smul, smul_eq_mul, hq.2, mul_one]
        · change r • kernelPart (l i) v hv q = kernelPart (l i) v hv (r • q)
          exact (map_smul (kernelPart (l i) v hv) r q).symm
    · rintro ⟨⟨r, y⟩, ⟨hr, hy⟩, rfl⟩
      refine ⟨r • (v + y.val),
        ⟨(r, v + y.val), ⟨hr, facetBase_point_mem_face l i v hv hy⟩, rfl⟩, ?_⟩
      exact frame_radialMap (l i) v hv y r

theorem image_sector_intersection_frame
    (l : ι → E →L[ℝ] ℝ) (i : ι) (v : E) (hv : l i v = 1)
    (R : ℝ) (K : Set E) :
    continuousEquiv (l i) v hv '' (K ∩ radialTruncation R (face l i)) =
      clippedCone R (facetBase l i v) (continuousEquiv (l i) v hv '' K) := by
  first
  | rw [Set.image_inter (continuousEquiv (l i) v hv).injective, image_sector_frame]
    exact Set.inter_comm _ _

end Frame
end VolumePolynomials.RadialSectorDecomposition
