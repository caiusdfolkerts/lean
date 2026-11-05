module

public import Continuation.Runtime.RealValuativeSchemeCharts

/-!
# Coordinate charts and their dual-ray cone charts

The coordinate chart and the corresponding fan cone chart have exactly
equal exponent monoids. Their comparison is only transport along this
proved equality, and preserves the original Laurent inclusion and every
face localization.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricCharacters
open PaperVerification.ToricSchemes

namespace PaperVerification.ToricGeometry

variable (k : Type u) [Field k] {n : ℕ}

theorem dualConeMonoid_dualBasis_eq
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)) :
    dualConeMonoid (I.image (integralDualBasis b)) = coordinateConeMonoid b I := by
  rw [dualConeMonoid_basis_eq, integralDualBasis_involutive]

def monoidChartEqIso {S T : AddSubmonoid (Lattice n)} (h : S = T) :
    monoidChartScheme k S ≅ monoidChartScheme k T :=
  eqToIso (congrArg (monoidChartScheme k) h)

@[reassoc] theorem monoidChartEqIso_torus {S T : AddSubmonoid (Lattice n)} (h : S = T) :
    characterChartTorusMap k S ≫ (monoidChartEqIso k h).hom = characterChartTorusMap k T := by
  subst T
  simp [monoidChartEqIso]

@[reassoc] theorem monoidChartEqIso_face
    {S T S' T' : AddSubmonoid (Lattice n)} (hST : S ≤ T) (hS'T' : S' ≤ T')
    (hS : S = S') (hT : T = T') :
    monoidChartSpecMap k hST ≫ (monoidChartEqIso k hS).hom =
      (monoidChartEqIso k hT).hom ≫ monoidChartSpecMap k hS'T' := by
  subst S'
  subst T'
  simp [monoidChartEqIso]

def coordinateConeChartIso
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)) :
    coneChart k (I.image (integralDualBasis b)) ≅
      monoidChartScheme k (coordinateConeMonoid b I) :=
  monoidChartEqIso k (dualConeMonoid_dualBasis_eq b I)

/-- The standard zero-cone comparison is the actual Laurent inclusion
after restriction to any fan cone chart. -/
@[reassoc] theorem zeroConeChartIso_inv_face (s : Finset (Lattice n)) :
    (zeroConeChartIso k n).inv ≫ coneChartFaceMap k (Finset.empty_subset s) =
      characterChartTorusMap k (dualConeMonoid s) := by
  change Spec.map (CommRingCat.ofHom (zeroConeChartAlgEquiv k n).toRingHom) ≫
    Spec.map (CommRingCat.ofHom
      (monoidChartInclusion k (dualConeMonoid_antitone (Finset.empty_subset s))).toRingHom) = _
  rw [← Spec.map_comp]
  rfl

@[reassoc] theorem coordinateConeChartIso_torus
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)) :
    coneChartFaceMap k (Finset.empty_subset (I.image (integralDualBasis b))) ≫
        (coordinateConeChartIso k b I).hom =
      (zeroConeChartIso k n).hom ≫ characterChartTorusMap k (coordinateConeMonoid b I) := by
  apply (cancel_epi (zeroConeChartIso k n).inv).mp
  rw [← Category.assoc, zeroConeChartIso_inv_face]
  simp only [coordinateConeChartIso, monoidChartEqIso_torus,
    Iso.inv_hom_id_assoc]

@[reassoc] theorem coordinateConeChartIso_face
    (b : Module.Basis (Fin n) ℤ (Lattice n)) {I J : Finset (Fin n)} (hIJ : I ⊆ J) :
    coneChartFaceMap k (Finset.image_subset_image hIJ) ≫
        (coordinateConeChartIso k b J).hom =
      (coordinateConeChartIso k b I).hom ≫
        monoidChartSpecMap k (coordinateConeMonoid_antitone b hIJ) :=
  monoidChartEqIso_face k
    (dualConeMonoid_antitone (Finset.image_subset_image hIJ))
    (coordinateConeMonoid_antitone b hIJ)
    (dualConeMonoid_dualBasis_eq b J) (dualConeMonoid_dualBasis_eq b I)

/-- The comparison preserves the exact open image of each face map. -/
theorem coordinateConeChartIso_face_range
    (b : Module.Basis (Fin n) ℤ (Lattice n)) {I J : Finset (Fin n)} (hIJ : I ⊆ J) :
    Set.range (coneChartFaceMap k (Finset.image_subset_image hIJ)) =
      (coordinateConeChartIso k b J).hom ⁻¹'
        Set.range (monoidChartSpecMap k (coordinateConeMonoid_antitone b hIJ)) := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨(coordinateConeChartIso k b I).hom z, ?_⟩
    exact congrArg (fun f => f z) (coordinateConeChartIso_face k b hIJ).symm
  · rintro ⟨z, hz⟩
    obtain ⟨y, rfl⟩ := (coordinateConeChartIso k b I).hom.homeomorph.surjective z
    refine ⟨y, ?_⟩
    apply (coordinateConeChartIso k b J).hom.homeomorph.injective
    exact (congrArg (fun f => f y) (coordinateConeChartIso_face k b hIJ)).trans hz

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.coordinateConeChartIso_face_range
