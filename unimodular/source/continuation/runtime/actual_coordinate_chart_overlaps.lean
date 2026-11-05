module

public import Continuation.Runtime.SmoothChartAffineFaces
public import Continuation.Runtime.ActualCharacterChartIntersections
public import Continuation.Runtime.SmoothRayUniqueness

/-!
# The common-face property of the original affine charts

The overlap of two actual affine open immersions into a separated
locally noetherian scheme is affine. If the immersions agree on the
original character torus, the overlap contains that torus. Normal
coordinate-chart rigidity identifies it with a coordinate localization.
The Hahn-valuative comparison then identifies its real cone with the
intersection of the two chart cones, and primitive-ray uniqueness turns
this into the exact common-ray face required by the fan definition.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricCharacters PaperVerification.ToricGeometry
open scoped Classical

namespace PaperVerification.ToricSchemes

variable (k : Type u) [Field k] {n : ℕ}

/-- The zero coordinate cone has the whole original Laurent algebra. -/
def coordinateZeroChartAlgEquiv (b : Module.Basis (Fin n) ℤ (Lattice n)) :
    monoidChartAlgebra k (coordinateConeMonoid b ∅) ≃ₐ[k]
      AddMonoidAlgebra k (Lattice n) :=
  AlgEquiv.ofBijective (Subalgebra.val _) ⟨Subtype.val_injective, by
    intro f
    refine ⟨⟨f, (mem_monoidChartAlgebra k _ f).mpr ?_⟩, rfl⟩
    intro m hm i hi
    exact (Finset.notMem_empty i hi).elim⟩

instance coordinateZeroChartTorus_isIso (b : Module.Basis (Fin n) ℤ (Lattice n)) :
    IsIso (characterChartTorusMap k (coordinateConeMonoid b ∅)) := by
  change IsIso (Spec.map
    (coordinateZeroChartAlgEquiv k b).toRingEquiv.toCommRingCatIso.hom)
  infer_instance

variable {X : Scheme.{u}} [X.IsSeparated] [IsLocallyNoetherian X]
    (b c : Module.Basis (Fin n) ℤ (Lattice n)) (I J : Finset (Fin n))
    (a : monoidChartScheme k (coordinateConeMonoid b I) ⟶ X)
    (d : monoidChartScheme k (coordinateConeMonoid c J) ⟶ X)
    [IsOpenImmersion a] [IsOpenImmersion d]
    (hT : characterChartTorusMap k (coordinateConeMonoid b I) ≫ a =
      characterChartTorusMap k (coordinateConeMonoid c J) ≫ d)

include hT in
/-- The literal overlap of two affine coordinate charts is a coordinate
face on the first side. No face condition is assumed in the input. -/
theorem exists_coordinateOverlap_face :
    ∃ (K : Finset (Fin n)) (hKI : K ⊆ I),
      coordinateChartFaceOpen k b hKI =
        a ⁻¹ᵁ d.opensRange := by
  let A := monoidChartAlgebra k (coordinateConeMonoid b I)
  let U := a ⁻¹ᵁ d.opensRange
  letI : IsDomain A := coordinateChartAlgebra_isDomain b I k
  letI : UniqueFactorizationMonoid A := coordinateChartAlgebra_uniqueFactorization b I k
  letI : IsIntegrallyClosed A := UniqueFactorizationMonoid.instIsIntegrallyClosed
  letI : IsLocallyNoetherian (monoidChartScheme k (coordinateConeMonoid b I)) :=
    isLocallyNoetherian_of_isOpenImmersion a
  letI : IsLocallyNoetherian (Spec (CommRingCat.of A)) := by
    change IsLocallyNoetherian (monoidChartScheme k (coordinateConeMonoid b I))
    infer_instance
  letI : IsAffine (monoidChartScheme k (coordinateConeMonoid b I)) :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))
  letI : IsAffine (monoidChartScheme k (coordinateConeMonoid c J)) :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of (monoidChartAlgebra k (coordinateConeMonoid c J)))))
  letI : IsNoetherianRing A := (isLocallyNoetherian_Spec (R := CommRingCat.of A)).mp (show IsLocallyNoetherian (Spec (CommRingCat.of A)) from inferInstance)
  letI : IsAffineHom (a ≫ Limits.terminal.from X) := inferInstance
  letI : IsAffineHom a := IsAffineHom.of_comp a (Limits.terminal.from X)
  have hU : IsAffineOpen U := (isAffineOpen_opensRange d).preimage a
  have htorus : coordinateChartFaceOpen k b (Finset.empty_subset I) ≤ U := by
    rintro y ⟨z, rfl⟩
    obtain ⟨t, rfl⟩ :=
      (characterChartTorusMap k (coordinateConeMonoid b ∅)).surjective z
    refine ⟨characterChartTorusMap k (coordinateConeMonoid c J) t, ?_⟩
    have ht := congrArg (fun f => f t) hT.symm
    simpa only [← Scheme.Hom.comp_apply, Category.assoc,
      characterChartTorusMap_comp_face_assoc] using ht
  letI : IsDomain (AddMonoidAlgebra k (Lattice n)) := torusCoordinateRing_isDomain k n
  let t := genericPoint (Spec (CommRingCat.of (AddMonoidAlgebra k (Lattice n))))
  let y := characterChartTorusMap k (coordinateConeMonoid b I) t
  have hy : y ∈ U := by
    refine ⟨characterChartTorusMap k (coordinateConeMonoid c J) t, ?_⟩
    exact congrArg (fun f => f t) hT.symm
  letI : Nonempty U := ⟨⟨y, hy⟩⟩
  obtain ⟨K, hKI, hK⟩ := affineOpen_eq_coordinateChartFace k b I U hU htorus
  exact ⟨K, hKI, hK.symm⟩

include hT in
/-- The cone of an actual overlap face is exactly the intersection of
the two original chart cones, for every real vector. -/
theorem coordinateOverlap_cone_eq
    (K : Finset (Fin n)) (hKI : K ⊆ I)
    (hK : coordinateChartFaceOpen k b hKI =
      a ⁻¹ᵁ d.opensRange) :
    latticeRayCone (K.image (integralDualBasis b)) =
      latticeRayCone (I.image (integralDualBasis b)) ⊓
        latticeRayCone (J.image (integralDualBasis c)) := by
  ext x
  change x ∈ latticeRayCone (K.image (integralDualBasis b)) ↔
    x ∈ latticeRayCone (I.image (integralDualBasis b)) ∧
      x ∈ latticeRayCone (J.image (integralDualBasis c))
  simp only [mem_dualBasisCone_iff_nonnegative_characters]
  letI := coordinateChartSpecMap_isOpenImmersion k b hKI
  exact nonnegative_on_actual_chart_intersection_iff k (latticeRealWeight x)
    (coordinateConeMonoid_antitone b hKI) a d hT hK

include hT in
/-- Both the literal common-ray set and its actual open chart image are
derived from the original open immersions. -/
theorem exists_coordinateOverlap_commonFace :
    ∃ (K : Finset (Fin n)) (hKI : K ⊆ I),
      K.image (integralDualBasis b) =
        I.image (integralDualBasis b) ∩ J.image (integralDualBasis c) ∧
      coordinateChartFaceOpen k b hKI =
        a ⁻¹ᵁ d.opensRange := by
  obtain ⟨K, hKI, hK⟩ := exists_coordinateOverlap_face k b c I J a d hT
  obtain ⟨L, hLJ, hL⟩ := exists_coordinateOverlap_face k c b J I d a hT.symm
  have hKcone := coordinateOverlap_cone_eq k b c I J a d hT K hKI hK
  have hLcone := coordinateOverlap_cone_eq k c b J I d a hT.symm L hLJ hL
  refine ⟨K, hKI, ?_, hK⟩
  apply common_coordinate_faces_eq_intersection
    ⟨integralDualBasis b, I, rfl⟩ ⟨integralDualBasis c, J, rfl⟩
    (Finset.image_subset_image hKI) (Finset.image_subset_image hLJ) hKcone
  simpa only [inf_comm] using hLcone

include k a d hT in
/-- The real cones of every pair of original affine charts meet exactly
in their common primitive-ray face. -/
theorem coordinateChart_cones_intersection :
    latticeRayCone (I.image (integralDualBasis b)) ⊓
        latticeRayCone (J.image (integralDualBasis c)) =
      latticeRayCone (I.image (integralDualBasis b) ∩ J.image (integralDualBasis c)) := by
  obtain ⟨K, hKI, hrays, hK⟩ := exists_coordinateOverlap_commonFace k b c I J a d hT
  rw [← hrays]
  exact (coordinateOverlap_cone_eq k b c I J a d hT K hKI hK).symm

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.exists_coordinateOverlap_commonFace
#print axioms PaperVerification.ToricSchemes.coordinateChart_cones_intersection
