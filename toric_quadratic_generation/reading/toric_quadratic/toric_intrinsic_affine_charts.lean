module

public import PaperVerification.ToricSmoothPointedSemigroup
public import PaperVerification.ToricFiniteCharacterSubspaces
public import PaperVerification.ToricFunctionFieldBridge
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

@[expose] public section

/-!
# Ordinary smooth scheme charts give actual unimodular exponent charts

An actual open immersion from the character torus gives the common
function field, with its exact coordinate maps. Ordinary smoothness of
the affine structure morphism gives algebraic smoothness. The pointed
semigroup classification then supplies a genuine primitive lattice basis.
Neither a function-field equality nor a lattice-generation conclusion is
assumed separately.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory

theorem affineOpenCoordinateMap_specMap {A B : CommRingCat.{u}}
    [IsDomain A] [IsDomain B] (φ : A⟶B) [IsOpenImmersion (Spec.map φ)] :
    (affineOpenCoordinateMap B (Spec.map φ)).comp φ.hom=
      affineOpenCoordinateMap A (𝟙 (Spec A)) := by
  ext a
  have hsec : (Spec.map φ).appTop ((Scheme.ΓSpecIso A).inv a)=
      (Scheme.ΓSpecIso B).inv (φ a) := by
    exact congrArg (fun f=>f a) (Scheme.ΓSpecIso_inv_naturality φ).symm
  have h := openImmersionGlobalToFunctionField_restrict (Spec.map φ)
    (𝟙 (Spec A)) ((Scheme.ΓSpecIso A).inv a)
  simpa only [Category.comp_id,hsec,affineOpenCoordinateMap,RingHom.comp_apply] using h

end PaperVerification.ToricSchemes

namespace PaperVerification.ToricCharacters

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricGeometry PaperVerification.ToricSchemes

variable (k : Type u) [Field k] {n : ℕ}
    [IsDomain (AddMonoidAlgebra k (Lattice n))]

theorem affineExponentMonoid_monoidChartAlgebra (S : AddSubmonoid (Lattice n)) :
    affineExponentMonoid k (monoidChartAlgebra k S)=S := by
  ext m
  simp [mem_affineExponentMonoid,mem_monoidChartAlgebra]

/-- This theorem consumes literal scheme smoothness and the literal open
torus inclusion. Its output is an actual equality of exponent monoids. -/
theorem pointed_semigroup_basis_of_smooth_open_torus
    (S : AddSubmonoid (Lattice n)) (hS : IsPointedMonoid S)
    [Smooth (Spec.map (CommRingCat.ofHom
      (algebraMap k (monoidChartAlgebra k S))))]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (monoidChartAlgebra k S).val.toRingHom))] :
    ∃ b : Module.Basis (Fin n) ℤ (Lattice n),
      S=coordinateConeMonoid b Finset.univ := by
  let A := monoidChartAlgebra k S
  let R := AddMonoidAlgebra k (Lattice n)
  let X := Spec (CommRingCat.of A)
  let K := X.functionField
  let j : Spec (CommRingCat.of R)⟶X := Spec.map (CommRingCat.ofHom A.val.toRingHom)
  letI : Algebra A K := affineOpenCoordinateAlgebra (CommRingCat.of A) (𝟙 X)
  letI : IsFractionRing A K := affineOpenCoordinate_isFractionRing (CommRingCat.of A) (𝟙 X)
  letI : Algebra R K := affineOpenCoordinateAlgebra (CommRingCat.of R) j
  letI : IsFractionRing R K := affineOpenCoordinate_isFractionRing (CommRingCat.of R) j
  have hmaps : (algebraMap R K).comp A.val.toRingHom=algebraMap A K :=
    affineOpenCoordinateMap_specMap (CommRingCat.ofHom A.val.toRingHom)
  letI : SMul A K := (inferInstance : Algebra A K).toSMul
  letI : IsScalarTower A R K := IsScalarTower.of_algebraMap_eq (fun a=>
    (congrArg (fun f=>f a) hmaps).symm)
  letI : Algebra k K := ((algebraMap A K).comp (algebraMap k A)).toAlgebra
  letI : IsScalarTower k A K := IsScalarTower.of_algebraMap_eq (fun r=>rfl)
  letI : IsScalarTower k R K := IsScalarTower.of_algebraMap_eq (by
    intro r
    change algebraMap A K (algebraMap k A r)=algebraMap R K (algebraMap k R r)
    rw [← congrArg (fun f=>f (algebraMap k A r)) hmaps]
    rfl)
  letI : Algebra.Smooth k A := by
    apply RingHom.smooth_algebraMap.mp
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mp
      (inferInstance : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k A))))
  have hstable : IsCharacterStable k A.toSubmodule := by
    rw [show A.toSubmodule=characterModule k (S : Set (Lattice n)) from
      monoidChartAlgebra_toSubmodule k S]
    exact characterModule_isCharacterStable k (S : Set (Lattice n))
  have hpointed : IsPointedMonoid (affineExponentMonoid k A) := by
    simpa only [A,affineExponentMonoid_monoidChartAlgebra] using hS
  obtain ⟨b,hb⟩ := smooth_invariant_affineAlgebra_eq_coordinateCone k A hstable hpointed K
  refine ⟨b,?_⟩
  have he := congrArg (affineExponentMonoid k) hb
  simpa only [A,affineExponentMonoid_monoidChartAlgebra] using he

end PaperVerification.ToricCharacters

#print axioms PaperVerification.ToricCharacters.pointed_semigroup_basis_of_smooth_open_torus
