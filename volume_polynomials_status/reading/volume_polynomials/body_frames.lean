module
public import VolumePolynomials.BodySpan
public import VolumePolynomials.OneBody
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.Tactic.FunProp

@[expose] public section

/-!
# Normalizing segment frames by their actual volume

A finite family of segments is the linear image of a unit cube after
independent translations. A volume-one hypothesis therefore forces the
column map to have determinant modulus one and supplies an invertible
normalizing map. No mixed-volume or determinant formula is assumed.
-/

noncomputable section
open Set MeasureTheory Module
open scoped Pointwise BigOperators

namespace VolumePolynomials

section Segments
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def segmentBody (a b : E) : ConvexBody E where
  carrier := segment ℝ a b
  convex' := convex_segment a b
  isCompact' := by
    first
    | rw [segment_eq_image]
      exact isCompact_Icc.image (by fun_prop)
  nonempty' := ⟨a, left_mem_segment ℝ a b⟩

@[simp] theorem coe_segmentBody (a b : E) :
    (segmentBody a b : Set E) = segment ℝ a b := rfl

@[simp] theorem translate_segmentBody (v a b : E) :
    translateBody v (segmentBody a b) = segmentBody (v + a) (v + b) := by
  first
  | apply ConvexBody.ext
    simp only [coe_translateBody, coe_segmentBody, vadd_segment, vadd_eq_add]

@[simp] theorem map_segmentBody (f : E →L[ℝ] F) (a b : E) :
    mapBody f (segmentBody a b) = segmentBody (f a) (f b) := by
  first
  | apply ConvexBody.ext
    exact image_segment ℝ f.toLinearMap.toAffineMap a b

theorem body_eq_segmentBody {K : ConvexBody E} {a b : E}
    (h : (K : Set E) = segment ℝ a b) : K = segmentBody a b :=
  ConvexBody.ext h

end Segments

def coordinateSegment {d : ℕ} (i : Fin d) : Body d :=
  segmentBody 0 (Pi.single i 1)

@[simp] theorem zero_mem_coordinateSegment {d : ℕ} (i : Fin d) :
    (0 : Space d) ∈ coordinateSegment i := left_mem_segment ℝ _ _

theorem linearHull_segmentBody_zero {d : ℕ} (v : Space d) :
    linearHull (segmentBody 0 v) = ℝ ∙ v := by
  first
  | apply le_antisymm
    · apply Submodule.span_le.mpr
      exact (Submodule.convex (ℝ ∙ v)).segment_subset
        (Submodule.zero_mem _) (Submodule.mem_span_singleton_self v)
    · apply Submodule.span_le.mpr
      intro x hx
      have h : x = v := Set.mem_singleton_iff.mp hx
      rw [h]
      exact mem_linearHull (right_mem_segment ℝ (0 : Space d) v)

theorem linearHull_coordinateSegment_pair {d : ℕ} (i j : Fin d) :
    linearHull (coordinateSegment i + coordinateSegment j) =
      Submodule.span ℝ {Pi.single i (1 : ℝ), Pi.single j 1} := by
  first
  | rw [linearHull_add (zero_mem_coordinateSegment i) (zero_mem_coordinateSegment j)]
    simp only [coordinateSegment, linearHull_segmentBody_zero, ← Submodule.span_union,
      Set.singleton_union]

theorem finrank_coordinateSegment_pair {d : ℕ} (i j : Fin d) (hij : i ≠ j) :
    finrank ℝ (linearHull (coordinateSegment i + coordinateSegment j)) = 2 := by
  first
  | have hli : LinearIndependent ℝ ![(Pi.single i (1 : ℝ) : Space d), Pi.single j 1] := by
      rw [LinearIndependent.pair_iff]
      intro s t h
      constructor
      · have hi := congrFun h i
        simpa [Pi.single_apply, hij, hij.symm] using hi
      · have hj := congrFun h j
        simpa [Pi.single_apply, hij, hij.symm] using hj
    rw [linearHull_coordinateSegment_pair]
    have hrange : Set.range ![(Pi.single i (1 : ℝ) : Space d), Pi.single j 1] =
        {(Pi.single i (1 : ℝ) : Space d), Pi.single j 1} := by
      ext x
      constructor
      · rintro ⟨k, rfl⟩
        fin_cases k <;> simp
      · rintro (rfl | rfl)
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
    have hdim := finrank_span_eq_card hli
    rw [hrange] at hdim
    simpa only [Fintype.card_fin] using hdim

/-- The volume test against two coordinate segments has its literal geometric
meaning: the body has zero remaining coordinate after translation to the
origin. This is the plane constraint used in the nine-body pattern. -/
theorem coordinate_eq_zero_of_volume_zero (K : Body 3) (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hzero : (0 : Space 3) ∈ K)
    (hvol : bodyVolume (K + coordinateSegment i + coordinateSegment j) = 0) :
    ∀ x ∈ K, x k = 0 := by
  first
  | have hvol' : bodyVolume (K + (coordinateSegment i + coordinateSegment j)) = 0 := by
      simpa only [add_assoc] using hvol
    have hsub := body_subset_linearHull_of_volume_zero_sum K
      (coordinateSegment i + coordinateSegment j) hzero
      (zero_mem_body_add (zero_mem_coordinateSegment i) (zero_mem_coordinateSegment j))
      (finrank_coordinateSegment_pair i j hij) hvol'
    intro x hx
    have hmem := hsub hx
    rw [linearHull_coordinateSegment_pair] at hmem
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hmem
    simp [Pi.single_apply, hik, hjk, hik.symm, hjk.symm]

def frameColumnMap {d : ℕ} (v : Fin d → Space d) : Space d →L[ℝ] Space d :=
  (Pi.basisFun ℝ (Fin d)).constrL v

@[simp] theorem frameColumnMap_apply {d : ℕ} (v : Fin d → Space d) (x : Space d) :
    frameColumnMap v x = ∑ i, x i • v i := by
  first
  | simp [frameColumnMap, Basis.constrL_apply]

@[simp] theorem frameColumnMap_basis {d : ℕ} (v : Fin d → Space d) (i : Fin d) :
    frameColumnMap v (Pi.single i 1) = v i := by
  first
  | simpa only [frameColumnMap, Pi.basisFun_apply] using
      (Pi.basisFun ℝ (Fin d)).constrL_basis v i

theorem map_unitCube_eq_sum_segments {d : ℕ} (v : Fin d → Space d) :
    mapBody (frameColumnMap v) (unitCube d) = ∑ i, segmentBody 0 (v i) := by
  first
  | apply ConvexBody.ext
    rw [coe_mapBody, coe_sum_body]
    change (frameColumnMap v) '' Set.Icc 0 1 = ∑ i, segment ℝ 0 (v i)
    rw [← parallelepiped_eq_sum_segment]
    simp only [parallelepiped, frameColumnMap_apply]

theorem bodyVolume_sum_origin_segments {d : ℕ} (v : Fin d → Space d) :
    bodyVolume (∑ i, segmentBody 0 (v i)) =
      |LinearMap.det (frameColumnMap v).toLinearMap| := by
  first
  | rw [← map_unitCube_eq_sum_segments, bodyVolume_map, bodyVolume_unitCube, mul_one]

theorem sum_origin_segments_eq_translate {d : ℕ} (a b : Fin d → Space d) :
    (∑ i, segmentBody 0 (b i - a i)) =
      translateBody (-(∑ i, a i)) (∑ i, segmentBody (a i) (b i)) := by
  first
  | have h := weightedSum_translate (fun i => segmentBody (a i) (b i))
      (fun i => -a i) (fun _ => (1 : ℝ))
    simpa only [weightedSum_one, one_smul, Finset.sum_neg_distrib,
      translate_segmentBody, neg_add_cancel, neg_add_eq_sub] using h

theorem normalize_origin_segment_frame {d : ℕ} (v : Fin d → Space d)
    (hvol : bodyVolume (∑ i, segmentBody 0 (v i)) = 1) :
    ∃ g : Space d ≃L[ℝ] Space d,
      |LinearMap.det g.toLinearEquiv.toLinearMap| = 1 ∧
      ∀ i, g (v i) = Pi.single i 1 := by
  first
  | let f : Space d →L[ℝ] Space d := frameColumnMap v
    have hdet : |LinearMap.det f.toLinearMap| = 1 := by
      rw [← bodyVolume_sum_origin_segments, hvol]
    have hne : LinearMap.det f.toLinearMap ≠ 0 := by
      intro h
      rw [h, abs_zero] at hdet
      exact zero_ne_one hdet
    let e : Space d ≃L[ℝ] Space d := f.toContinuousLinearEquivOfDetNeZero hne
    refine ⟨e.symm, ?_, fun i => ?_⟩
    · change |LinearMap.det e.toLinearEquiv.symm.toLinearMap| = 1
      rw [LinearEquiv.det_coe_symm, abs_inv]
      change |LinearMap.det f.toLinearMap|⁻¹ = 1
      rw [hdet, inv_one]
    · apply e.injective
      rw [e.apply_symm_apply]
      exact (frameColumnMap_basis v i).symm

/-- A volume-one segment frame in any dimension is carried to the standard
coordinate segments by independent translations and a common continuous
linear equivalence whose determinant has modulus one. -/
theorem normalize_segment_frame {d : ℕ} (a b : Fin d → Space d)
    (hvol : bodyVolume (∑ i, segmentBody (a i) (b i)) = 1) :
    ∃ g : Space d ≃L[ℝ] Space d,
      |LinearMap.det g.toLinearEquiv.toLinearMap| = 1 ∧
      ∀ i, mapBody g.toContinuousLinearMap
        (translateBody (-a i) (segmentBody (a i) (b i))) =
          segmentBody 0 (Pi.single i 1) := by
  first
  | have hv : bodyVolume (∑ i, segmentBody 0 (b i - a i)) = 1 := by
      rw [sum_origin_segments_eq_translate, bodyVolume_translate, hvol]
    obtain ⟨g, hg, hgv⟩ := normalize_origin_segment_frame (fun i => b i - a i) hv
    refine ⟨g, hg, fun i => ?_⟩
    rw [translate_segmentBody, neg_add_cancel, neg_add_eq_sub, map_segmentBody,
      map_zero]
    change segmentBody (0 : Space d) (g (b i - a i)) = segmentBody 0 (Pi.single i 1)
    rw [hgv]

end VolumePolynomials
