module

public import Continuation.Runtime.CoordinateChartCover
public import Continuation.Runtime.CoordinateConeChartComparison
public import Continuation.Runtime.ActualCoordinateChartOverlaps

/-!
# The complete smooth fan of an actual coordinate-chart cover

The finite ray sets are the duals of the recovered character bases.
Their intersections are proved from the actual affine overlaps, and
their completeness is proved by applying universal closedness to every
real Hahn-valued torus point. Closing this family under coordinate faces
therefore gives an actual complete smooth fan in the original lattice.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricCharacters PaperVerification.ToricGeometry

namespace PaperVerification.ToricSchemes.CoordinateChartCover

variable {k : Type u} [Field k] {n : ℕ} {X : Scheme.{u}}
    {j : Spec (CommRingCat.of (AddMonoidAlgebra k (Lattice n))) ⟶ X}
    (C : CoordinateChartCover k n X j)

def rays (i : C.Index) : Finset (Lattice n) :=
  (C.coordinates i).image (integralDualBasis (C.basis i))

def coneMap (i : C.Index) : coneChart k (C.rays i) ⟶ X :=
  (coordinateConeChartIso k (C.basis i) (C.coordinates i)).hom ≫ C.map i

instance coneMap_isOpenImmersion (i : C.Index) : IsOpenImmersion (C.coneMap i) := by
  unfold coneMap
  infer_instance

@[reassoc] theorem coneMap_torus (i : C.Index) :
    coneChartFaceMap k (Finset.empty_subset (C.rays i)) ≫ C.coneMap i =
      (zeroConeChartIso k n).hom ≫ j := by
  rw [coneMap, ← Category.assoc, coordinateConeChartIso_torus,
    Category.assoc, C.torus_eq]

theorem coneMap_torus_agree (i l : C.Index) :
    coneChartFaceMap k (Finset.empty_subset (C.rays i)) ≫ C.coneMap i =
      coneChartFaceMap k (Finset.empty_subset (C.rays l)) ≫ C.coneMap l := by
  rw [C.coneMap_torus, C.coneMap_torus]

theorem coneMap_range (i : C.Index) : Set.range (C.coneMap i) = Set.range (C.map i) := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨(coordinateConeChartIso k (C.basis i) (C.coordinates i)).hom z, rfl⟩
  · rintro ⟨z, rfl⟩
    refine ⟨(coordinateConeChartIso k (C.basis i) (C.coordinates i)).inv z, ?_⟩
    simp only [coneMap, Scheme.Hom.comp_apply]
    exact congrArg (C.map i) (congrArg (fun f => f z) (coordinateConeChartIso k (C.basis i) (C.coordinates i)).inv_hom_id)

theorem coneMaps_cover (x : X) : ∃ i z, C.coneMap i z = x := by
  obtain ⟨i, z, hz⟩ := C.covers x
  have hx : x ∈ Set.range (C.coneMap i) := by
    rw [C.coneMap_range]
    exact ⟨z, hz⟩
  exact ⟨i, hx⟩

variable [X.IsSeparated] [IsLocallyNoetherian X]

/-- The overlap condition required by the actual fan colimit is proved
for these original charts, rather than supplied in the cover record. -/
theorem coneMap_overlap (i l : C.Index) :
    Set.range (coneChartFaceMap k
      (Finset.inter_subset_left : C.rays i ∩ C.rays l ⊆ C.rays i)) =
        (C.coneMap i) ⁻¹' Set.range (C.coneMap l) := by
  obtain ⟨K, hKI, hrays, hK⟩ := exists_coordinateOverlap_commonFace k
    (C.basis i) (C.basis l) (C.coordinates i) (C.coordinates l)
    (C.map i) (C.map l) ((C.torus_eq i).trans (C.torus_eq l).symm)
  have hrays' : K.image (integralDualBasis (C.basis i)) = C.rays i ∩ C.rays l := hrays
  rw [C.coneMap_range]
  have hrange := coordinateConeChartIso_face_range k (C.basis i) hKI
  have hrange' : Set.range (coneChartFaceMap k
      (Finset.inter_subset_left : C.rays i ∩ C.rays l ⊆ C.rays i)) =
      (coordinateConeChartIso k (C.basis i) (C.coordinates i)).hom ⁻¹'
        Set.range (monoidChartSpecMap k (coordinateConeMonoid_antitone (C.basis i) hKI)) := by
    have he : Set.range (coneChartFaceMap k
        (Finset.inter_subset_left : C.rays i ∩ C.rays l ⊆ C.rays i)) =
        Set.range (coneChartFaceMap k (Finset.image_subset_image hKI)) := by
      have hcongr {S T U : Finset (Lattice n)} (h : S = T) (hS : S ⊆ U) (hT : T ⊆ U) :
          Set.range (coneChartFaceMap k hS) = Set.range (coneChartFaceMap k hT) := by
        subst T
        rfl
      exact hcongr hrays'.symm _ _
    exact he.trans hrange
  rw [hrange']
  have hK' : Set.range (monoidChartSpecMap k
      (coordinateConeMonoid_antitone (C.basis i) hKI)) =
        (C.map i) ⁻¹' Set.range (C.map l) := congrArg SetLike.coe hK
  rw [hK']
  rfl

theorem rayCones_intersection (i l : C.Index) :
    latticeRayCone (C.rays i) ⊓ latticeRayCone (C.rays l) =
      latticeRayCone (C.rays i ∩ C.rays l) :=
  coordinateChart_cones_intersection k
    (C.basis i) (C.basis l) (C.coordinates i) (C.coordinates l)
    (C.map i) (C.map l) ((C.torus_eq i).trans (C.torus_eq l).symm)

variable (f : X ⟶ Spec (CommRingCat.of k)) [UniversallyClosed f]
    (hj : j ≫ f = Spec.map (CommRingCat.ofHom
      (algebraMap k (AddMonoidAlgebra k (Lattice n)))))

include f hj in
/-- Every real cocharacter lies in one of the actual chart cones. -/
theorem rayCones_cover (x : Ambient n) : ∃ i, x ∈ latticeRayCone (C.rays i) :=
  realCones_cover_of_actual_chartCover k f j hj C.basis C.coordinates C.map
    C.torus_eq C.covers x

/-- The actual complete smooth fan in the original character/cocharacter
lattice, constructed from the finite coordinate-chart cover. -/
def fan : SmoothCompleteFan n :=
  fanOfSmoothConeFamily C.rays
    (fun i => ⟨integralDualBasis (C.basis i), C.coordinates i, rfl⟩)
    C.rayCones_intersection (C.rayCones_cover f hj)

theorem rays_mem_fan (i : C.Index) : C.rays i ∈ (C.fan f hj).cones :=
  (mem_smoothConeFamilyFaces C.rays (C.rays i)).mpr ⟨i, Finset.Subset.refl _⟩

theorem fan_cones_covered (s : Finset (Lattice n)) (hs : s ∈ (C.fan f hj).cones) :
    ∃ i, s ⊆ C.rays i :=
  (mem_smoothConeFamilyFaces C.rays s).mp hs

end PaperVerification.ToricSchemes.CoordinateChartCover

#print axioms PaperVerification.ToricSchemes.CoordinateChartCover.fan
#print axioms PaperVerification.ToricSchemes.CoordinateChartCover.coneMap_overlap
