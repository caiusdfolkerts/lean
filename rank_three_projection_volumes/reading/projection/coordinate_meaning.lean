module

public import Projection.Normalization.Theorem31
public import Projection.StrictTopology
public import VolumePolynomials.ProjectionMixedVolumeTransport
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Euclidean meaning of the coordinate conventions

The coordinate model `Fin n → ℝ` carries the maximum norm and product
Lebesgue measure. Its coordinate bijection with Euclidean space preserves
Lebesgue measure exactly. Coordinate deletion commutes with that bijection,
so all projection volumes and their realization loci agree. The same map
preserves the actual mixed volume and affine dimension. Consequently the
compactification theorem also has the fully Euclidean formulation below.

No comparison of the different unit spheres is made in these statements.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory Module
open scoped Pointwise

namespace RankThreeProjection
open VolumePolynomials

abbrev EuclideanBody (n : ℕ) := ConvexBody (EuclideanSpace ℝ (Fin n))

/-- The identity on coordinates, with the Euclidean norm on the codomain. -/
def coordinateEuclideanEquiv (ι : Type*) [Fintype ι] :
    (ι → ℝ) ≃L[ℝ] EuclideanSpace ℝ ι := (EuclideanSpace.equiv ι ℝ).symm

@[simp] theorem coordinateEuclideanEquiv_apply {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (i : ι) : coordinateEuclideanEquiv ι x i = x i := rfl

@[simp] theorem coordinateEuclideanEquiv_symm_apply {ι : Type*} [Fintype ι]
    (x : EuclideanSpace ℝ ι) (i : ι) : (coordinateEuclideanEquiv ι).symm x i = x i := rfl

theorem coordinateEuclideanEquiv_measurePreserving (ι : Type*) [Fintype ι] :
    MeasurePreserving (coordinateEuclideanEquiv ι) volume volume :=
  PiLp.volume_preserving_toLp ι

theorem coordinateEuclideanEquiv_symm_measurePreserving (ι : Type*) [Fintype ι] :
    MeasurePreserving (coordinateEuclideanEquiv ι).symm volume volume :=
  PiLp.volume_preserving_ofLp ι

/-- The same coordinate convention also preserves topological closure of
finite arrays of real data. -/
theorem coordinateEuclideanEquiv_image_closure (ι : Type*) [Fintype ι]
    (S : Set (ι → ℝ)) :
    coordinateEuclideanEquiv ι '' closure S =
      closure (coordinateEuclideanEquiv ι '' S) :=
  (coordinateEuclideanEquiv ι).toHomeomorph.image_closure S

/-- The scalar in generic Haar transport is exactly one for these standard
coordinate models. -/
theorem coordinateEuclideanEquiv_frameFactor (ι : Type*) [Fintype ι] :
    mixedVolumeFrameFactor volume volume (coordinateEuclideanEquiv ι) = 1 := by
  unfold mixedVolumeFrameFactor
  simpa only [(coordinateEuclideanEquiv_measurePreserving ι).map_eq] using
    (Measure.addHaarScalarFactor_self (volume : Measure (EuclideanSpace ℝ ι)))

def toEuclideanBody {n : ℕ} (K : Body n) : EuclideanBody n :=
  mapBody (coordinateEuclideanEquiv (Fin n)).toContinuousLinearMap K

def fromEuclideanBody {n : ℕ} (K : EuclideanBody n) : Body n :=
  mapBody (coordinateEuclideanEquiv (Fin n)).symm.toContinuousLinearMap K

@[simp] theorem toEuclideanBody_fromEuclideanBody {n : ℕ} (K : EuclideanBody n) :
    toEuclideanBody (fromEuclideanBody K) = K := by
  apply ConvexBody.ext
  change (coordinateEuclideanEquiv (Fin n)) ''
    ((coordinateEuclideanEquiv (Fin n)).symm '' (K : Set (EuclideanSpace ℝ (Fin n)))) = _
  rw [Set.image_image]
  simp only [Function.comp_def, ContinuousLinearEquiv.apply_symm_apply, image_id']

@[simp] theorem fromEuclideanBody_toEuclideanBody {n : ℕ} (K : Body n) :
    fromEuclideanBody (toEuclideanBody K) = K := by
  apply ConvexBody.ext
  change (coordinateEuclideanEquiv (Fin n)).symm ''
    ((coordinateEuclideanEquiv (Fin n)) '' (K : Set (Space n))) = _
  rw [Set.image_image]
  simp only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply, image_id']

/-- Euclidean coordinate projection, with the retained coordinates as its
Euclidean target. Its coordinate formula is proved immediately below. -/
def euclideanDeleteCoordinates {n : ℕ} (I : Finset (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Retained I) :=
  (coordinateEuclideanEquiv (Retained I)).toContinuousLinearMap.comp
    ((deleteCoordinates I).comp
      (coordinateEuclideanEquiv (Fin n)).symm.toContinuousLinearMap)

@[simp] theorem euclideanDeleteCoordinates_apply {n : ℕ} (I : Finset (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) (j : Retained I) :
    euclideanDeleteCoordinates I x j = x j.val := rfl

theorem euclideanDeleteCoordinates_target_dimension {n : ℕ} (I : Finset (Fin n)) :
    finrank ℝ (EuclideanSpace ℝ (Retained I)) = n - I.card := by
  simp only [finrank_euclideanSpace, Retained, Fintype.card_subtype_compl,
    Fintype.card_fin, Fintype.card_coe]

theorem euclideanDeleteCoordinates_commutes {n : ℕ} (I : Finset (Fin n)) :
    (euclideanDeleteCoordinates I).comp
        (coordinateEuclideanEquiv (Fin n)).toContinuousLinearMap =
      (coordinateEuclideanEquiv (Retained I)).toContinuousLinearMap.comp
        (deleteCoordinates I) := by
  ext x j
  rfl

def euclideanCoordinateVolume {n : ℕ} (I : Finset (Fin n))
    (K : EuclideanBody n) : ℝ :=
  volume.real (mapBody (euclideanDeleteCoordinates I) K :
    Set (EuclideanSpace ℝ (Retained I)))

/-- Literal projection volumes are identical in the two coordinate models,
including projections of lower-dimensional bodies. -/
theorem euclideanCoordinateVolume_toEuclideanBody {n : ℕ}
    (I : Finset (Fin n)) (K : Body n) :
    euclideanCoordinateVolume I (toEuclideanBody K) = coordinateVolume I K := by
  have hbody : mapBody (euclideanDeleteCoordinates I) (toEuclideanBody K) =
      mapBody (coordinateEuclideanEquiv (Retained I)).toContinuousLinearMap
        (projectedBody I K) := by
    rw [toEuclideanBody, mapBody_comp, euclideanDeleteCoordinates_commutes,
      ← mapBody_comp]
    rfl
  rw [euclideanCoordinateVolume, hbody, coe_mapBody]
  exact measureReal_image_measurePreserving volume volume
    (coordinateEuclideanEquiv (Retained I))
    (coordinateEuclideanEquiv_measurePreserving (Retained I)) _

theorem coordinateVolume_fromEuclideanBody {n : ℕ}
    (I : Finset (Fin n)) (K : EuclideanBody n) :
    coordinateVolume I (fromEuclideanBody K) = euclideanCoordinateVolume I K := by
  simpa only [toEuclideanBody_fromEuclideanBody] using
    (euclideanCoordinateVolume_toEuclideanBody I (fromEuclideanBody K)).symm

def euclideanAllProjectionArray {n k : ℕ} (K : EuclideanBody n) : Deleted n k → ℝ :=
  fun I => euclideanCoordinateVolume I.val K

def euclideanAllProjectionLocus (n k : ℕ) : Set (Deleted n k → ℝ) :=
  Set.range (euclideanAllProjectionArray (n := n) (k := k))

theorem euclideanAllProjectionArray_toEuclideanBody {n k : ℕ} (K : Body n) :
    euclideanAllProjectionArray (k := k) (toEuclideanBody K) = allProjectionArray K := by
  funext I
  exact euclideanCoordinateVolume_toEuclideanBody I.val K

theorem allProjectionArray_fromEuclideanBody {n k : ℕ} (K : EuclideanBody n) :
    allProjectionArray (k := k) (fromEuclideanBody K) = euclideanAllProjectionArray K := by
  funext I
  exact coordinateVolume_fromEuclideanBody I.val K

/-- Exact equality of the loci for every number of deleted coordinates. -/
theorem euclideanAllProjectionLocus_eq (n k : ℕ) :
    euclideanAllProjectionLocus n k = allProjectionLocus n k := by
  apply Set.Subset.antisymm
  · rintro P ⟨K, rfl⟩
    exact ⟨fromEuclideanBody K, allProjectionArray_fromEuclideanBody K⟩
  · rintro P ⟨K, rfl⟩
    exact ⟨toEuclideanBody K, euclideanAllProjectionArray_toEuclideanBody K⟩

def euclideanProjectionArray {n : ℕ} (K : EuclideanBody n) : Array n :=
  fun i j => if i = j then 0 else euclideanCoordinateVolume {i, j} K

def euclideanProjectionLocus (n : ℕ) : Set (Array n) :=
  Set.range (euclideanProjectionArray (n := n))

def euclideanClosedProjectionLocus (n : ℕ) : Set (Array n) :=
  closure (euclideanProjectionLocus n)

theorem euclideanProjectionArray_toEuclideanBody {n : ℕ} (K : Body n) :
    euclideanProjectionArray (toEuclideanBody K) = projectionArray K := by
  ext i j
  simp only [euclideanProjectionArray, projectionArray,
    euclideanCoordinateVolume_toEuclideanBody]

theorem projectionArray_fromEuclideanBody {n : ℕ} (K : EuclideanBody n) :
    projectionArray (fromEuclideanBody K) = euclideanProjectionArray K := by
  ext i j
  simp only [projectionArray, euclideanProjectionArray, coordinateVolume_fromEuclideanBody]

theorem euclideanProjectionLocus_eq (n : ℕ) :
    euclideanProjectionLocus n = projectionLocus n := by
  apply Set.Subset.antisymm
  · rintro P ⟨K, rfl⟩
    exact ⟨fromEuclideanBody K, projectionArray_fromEuclideanBody K⟩
  · rintro P ⟨K, rfl⟩
    exact ⟨toEuclideanBody K, euclideanProjectionArray_toEuclideanBody K⟩

theorem euclideanClosedProjectionLocus_eq (n : ℕ) :
    euclideanClosedProjectionLocus n = closedProjectionLocus n := by
  rw [euclideanClosedProjectionLocus, euclideanProjectionLocus_eq, closedProjectionLocus]

/-- The actual projection array regarded in the hollow symmetric subspace. -/
def hollowProjectionArray {n : ℕ} (K : Body n) : HollowSymmetricArray n :=
  ⟨projectionArray K, projectionArray_diagonal K, projectionArray_symmetric K⟩

def hollowProjectionLocus (n : ℕ) : Set (HollowSymmetricArray n) :=
  Set.range (hollowProjectionArray (n := n))

theorem val_image_hollowProjectionLocus (n : ℕ) :
    Subtype.val '' hollowProjectionLocus n = projectionLocus n := by
  ext P
  constructor
  · rintro ⟨Q, ⟨K, hK⟩, hQP⟩
    exact ⟨K, (congrArg Subtype.val hK).trans hQP⟩
  · rintro ⟨K, rfl⟩
    exact ⟨hollowProjectionArray K, ⟨K, rfl⟩, rfl⟩

/-- Taking closure intrinsically in hollow symmetric matrices agrees exactly
with the ambient matrix closure used by the principal theorem. -/
theorem hollowProjectionClosure_eq_preimage (n : ℕ) :
    closure (hollowProjectionLocus n) =
      Subtype.val ⁻¹' closedProjectionLocus n := by
  rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,
    val_image_hollowProjectionLocus, closedProjectionLocus]

theorem mem_hollowProjectionClosure_iff {n : ℕ} (P : HollowSymmetricArray n) :
    P ∈ closure (hollowProjectionLocus n) ↔ P.val ∈ closedProjectionLocus n := by
  rw [hollowProjectionClosure_eq_preimage]
  rfl

theorem mem_hollowProjectionClosure_iff_euclidean {n : ℕ}
    (P : HollowSymmetricArray n) :
    P ∈ closure (hollowProjectionLocus n) ↔
      P.val ∈ euclideanClosedProjectionLocus n := by
  rw [euclideanClosedProjectionLocus_eq]
  exact mem_hollowProjectionClosure_iff P

def euclideanMarkedTuple {n k : ℕ} (K : EuclideanBody n)
    (U : Fin n → EuclideanSpace ℝ (Fin n)) (I : Deleted n k) :
    Fin (n - k + k) → EuclideanBody n :=
  Fin.append (fun _ : Fin (n - k) => K)
    (fun j : Fin k => centeredSegment (U (I.val.orderEmbOfFin I.property j)))

def euclideanAllMarkedArray {n k : ℕ} (K : EuclideanBody n)
    (U : Fin n → EuclideanSpace ℝ (Fin n)) : Deleted n k → ℝ :=
  fun I => (n.factorial : ℝ) / ((n - k).factorial : ℝ) *
    mixedVolume volume (euclideanMarkedTuple K U I)

def euclideanBodyDimension {n : ℕ} (K : EuclideanBody n) : ℕ :=
  finrank ℝ (affineSpan ℝ (K : Set (EuclideanSpace ℝ (Fin n)))).direction

theorem euclideanAllMarkedArray_toEuclideanBody {n k : ℕ}
    (K : Body n) (U : Fin n → Space n) :
    euclideanAllMarkedArray (k := k) (toEuclideanBody K)
        (fun i => coordinateEuclideanEquiv (Fin n) (U i)) = allMarkedArray K U := by
  funext I
  have htuple : euclideanMarkedTuple (toEuclideanBody K)
        (fun i => coordinateEuclideanEquiv (Fin n) (U i)) I =
      fun j => mapBody (coordinateEuclideanEquiv (Fin n)).toContinuousLinearMap
        (markedTuple K U I j) := by
    funext j
    refine Fin.addCases ?_ ?_ j
    · intro i
      simp only [euclideanMarkedTuple, markedTuple, Fin.append_left, toEuclideanBody]
    · intro i
      simp only [euclideanMarkedTuple, markedTuple, Fin.append_right, map_centeredSegment]
      rfl
  unfold euclideanAllMarkedArray allMarkedArray
  rw [htuple, mixedVolume_map_measurePreserving volume volume
    (coordinateEuclideanEquiv (Fin n)) (coordinateEuclideanEquiv_measurePreserving (Fin n))]

theorem allMarkedArray_fromEuclideanBody {n k : ℕ}
    (K : EuclideanBody n) (U : Fin n → EuclideanSpace ℝ (Fin n)) :
    allMarkedArray (k := k) (fromEuclideanBody K)
        (fun i => (coordinateEuclideanEquiv (Fin n)).symm (U i)) = euclideanAllMarkedArray K U := by
  have h := euclideanAllMarkedArray_toEuclideanBody (k := k) (fromEuclideanBody K)
    (fun i => (coordinateEuclideanEquiv (Fin n)).symm (U i))
  simpa only [toEuclideanBody_fromEuclideanBody, ContinuousLinearEquiv.apply_symm_apply] using h.symm

theorem euclideanBodyDimension_toEuclideanBody {n : ℕ} (K : Body n) :
    euclideanBodyDimension (toEuclideanBody K) = bodyDimension K := by
  let T := coordinateEuclideanEquiv (Fin n)
  change finrank ℝ
    (affineSpan ℝ (T.toLinearEquiv.toAffineEquiv.toAffineMap '' (K : Set (Space n)))).direction = _
  rw [← AffineSubspace.map_span T.toLinearEquiv.toAffineEquiv.toAffineMap,
    AffineSubspace.map_direction]
  exact T.toLinearEquiv.finrank_map_eq _

theorem bodyDimension_fromEuclideanBody {n : ℕ} (K : EuclideanBody n) :
    bodyDimension (fromEuclideanBody K) = euclideanBodyDimension K := by
  simpa only [toEuclideanBody_fromEuclideanBody] using
    (euclideanBodyDimension_toEuclideanBody (fromEuclideanBody K)).symm

/-- The unrestricted closure formula of Theorem 3.1 in Euclidean coordinates.
The comparison vectors may be zero or linearly dependent, and the initial
body may have any affine dimension. -/
theorem theorem31_euclidean_closure {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n)
    (P : Deleted n k → ℝ) :
    P ∈ closure (euclideanAllProjectionLocus n k) ↔
      ∃ (K : EuclideanBody n) (U : Fin n → EuclideanSpace ℝ (Fin n)),
        euclideanAllMarkedArray K U = P := by
  rw [euclideanAllProjectionLocus_eq, theorem31 hk hkn]
  constructor
  · rintro ⟨K, U, heq⟩
    refine ⟨toEuclideanBody K, fun i => coordinateEuclideanEquiv (Fin n) (U i), ?_⟩
    rw [euclideanAllMarkedArray_toEuclideanBody]
    exact heq
  · rintro ⟨K, U, heq⟩
    refine ⟨fromEuclideanBody K, fun i => (coordinateEuclideanEquiv (Fin n)).symm (U i), ?_⟩
    rw [allMarkedArray_fromEuclideanBody]
    exact heq

/-- The complete compactification statement in canonical Euclidean spaces,
with ordinary Euclidean volume, actual Euclidean mixed volume, and actual
Euclidean affine dimension. -/
theorem theorem31_euclidean {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n)
    (P : Deleted n k → ℝ) :
    P ∈ closure (euclideanAllProjectionLocus n k) ↔
      ∃ (K : EuclideanBody n) (U : Fin n → EuclideanSpace ℝ (Fin n)),
        n - k + 1 ≤ euclideanBodyDimension K ∧ euclideanAllMarkedArray K U = P := by
  rw [euclideanAllProjectionLocus_eq, theorem31_with_dimension hk hkn]
  constructor
  · rintro ⟨K, U, hdim, heq⟩
    refine ⟨toEuclideanBody K, fun i => coordinateEuclideanEquiv (Fin n) (U i), ?_, ?_⟩
    · simpa only [euclideanBodyDimension_toEuclideanBody] using hdim
    · rw [euclideanAllMarkedArray_toEuclideanBody]
      exact heq
  · rintro ⟨K, U, hdim, heq⟩
    refine ⟨fromEuclideanBody K, fun i => (coordinateEuclideanEquiv (Fin n)).symm (U i), ?_, ?_⟩
    · simpa only [bodyDimension_fromEuclideanBody] using hdim
    · rw [allMarkedArray_fromEuclideanBody]
      exact heq

/-- Every unrestricted Euclidean marked representation can be replaced by
one retaining the full dimension bound in the paper. -/
theorem theorem31_euclidean_renormalize_dimension {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k < n) (K : EuclideanBody n)
    (U : Fin n → EuclideanSpace ℝ (Fin n)) :
    ∃ (L : EuclideanBody n) (V : Fin n → EuclideanSpace ℝ (Fin n)),
      n - k + 1 ≤ euclideanBodyDimension L ∧
        euclideanAllMarkedArray (k := k) L V = euclideanAllMarkedArray K U :=
  (theorem31_euclidean hk hkn (euclideanAllMarkedArray K U)).mp
    ((theorem31_euclidean_closure hk hkn (euclideanAllMarkedArray K U)).mpr ⟨K, U, rfl⟩)

end RankThreeProjection
