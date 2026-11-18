module

public import ToricPower.ProjectiveSectionRecognition

/-! # Ordinary sections and exact rows from a genuine section quasi-isomorphism

The input is the specified scalar projective-section map. The output
retains its ordinary coefficient map and the exact original projective
rows, including all degree signs in their comparison with signed Hom.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex HomologicalComplex

namespace ToricPower

universe u v
variable (R : Type v) [CommRing R]
  {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  {Z Y : C} (P : ProjectiveResolution Z)

/-- The original projective unit always identifies degree-zero
cohomology with ordinary morphisms. -/
theorem scalarProjectiveSectionMap_identity_quasiIsoAt_zero :
    QuasiIsoAt (scalarProjectiveSectionMap R P
      (𝟙 (((linearCoyoneda R C).obj (op Z)).obj Y))) 0 := by
  letI : QuasiIsoAt (linearHomComplexPrecomp R (projectiveCochainAugmentation P)
      (((𝟭 C).mapHomologicalComplex (.up ℤ)).obj
        ((CochainComplex.singleFunctor C 0).obj Y))) 0 := by
    change QuasiIsoAt (linearHomComplexPrecomp R (projectiveCochainAugmentation P)
      ((CochainComplex.singleFunctor C 0).obj Y)) 0
    exact projectiveAugmentation_precomp_quasiIsoAt_zero P Y R
  dsimp only [scalarProjectiveSectionMap,singleCoefficientSection,
    projectiveCoefficientComplexUnit,ordinaryProjectiveCoefficients]
  infer_instance

variable {V : ModuleCat.{v} R}
  (a : V ⟶ ((linearCoyoneda R C).obj (op Z)).obj Y)

theorem scalarProjectiveSectionMap_factor :
    (CochainComplex.singleFunctor (ModuleCat.{v} R) 0).map a ≫
      scalarProjectiveSectionMap R P
        (𝟙 (((linearCoyoneda R C).obj (op Z)).obj Y)) =
      scalarProjectiveSectionMap R P a := by
  simp only [scalarProjectiveSectionMap,singleCoefficientSection,
    CategoryTheory.Functor.map_id,Category.id_comp,Category.assoc]

/-- A genuine section quasi-isomorphism forces the original ordinary
section map itself to be an isomorphism. -/
theorem scalarProjectiveSectionMap_section_isIso
    [QuasiIso (scalarProjectiveSectionMap R P a)] : IsIso a := by
  letI := scalarProjectiveSectionMap_identity_quasiIsoAt_zero R P (Y := Y)
  haveI : QuasiIsoAt ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).map a ≫
      scalarProjectiveSectionMap R P
        (𝟙 (((linearCoyoneda R C).obj (op Z)).obj Y))) 0 := by
    rw [scalarProjectiveSectionMap_factor]
    infer_instance
  haveI : QuasiIsoAt ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).map a) 0 :=
    quasiIsoAt_of_comp_right
      ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).map a)
      (scalarProjectiveSectionMap R P
        (𝟙 (((linearCoyoneda R C).obj (op Z)).obj Y))) 0
  haveI : IsIso (homologyMap
      ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).map a) 0) :=
    (quasiIsoAt_iff_isIso_homologyMap _ _).mp inferInstance
  haveI : IsIso ((singleObjHomologySelfIso (.up ℤ) 0 V).hom ≫ a) := by
    rw [← singleObjHomologySelfIso_hom_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_left (singleObjHomologySelfIso (.up ℤ) 0 V).hom a

/-- The target of the scalar section map is the full ordinary
projective coefficient complex, with the proved sign normalization. -/
def projectiveSingleOrdinaryIso :
    (projectiveCoefficientComplexFunctor R (𝟭 C) P).obj
      ((CochainComplex.singleFunctor C 0).obj Y) ≅
      (projectiveCoefficientComplex R P Y).extend ComplexShape.embeddingUpNat :=
  (linearHomComplexFunctor R (projectiveCochain P)).mapIso
    ((Functor.mapHomologicalComplexIdIso C (.up ℤ)).app
      ((CochainComplex.singleFunctor C 0).obj Y)) ≪≫
    homToSingleExtendedIso R P.complex Y

/-- Every positive ordinary projective coefficient row is exact.
The conclusion concerns the original projective resolution, rather
than an abstract cohomology group with the same dimension. -/
theorem scalarProjectiveSectionMap_positive_exact
    [QuasiIso (scalarProjectiveSectionMap R P a)] (n : ℕ) :
    (projectiveCoefficientComplex R P Y).ExactAt (n+1) := by
  have source : ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj V).ExactAt
      ((n+1 : ℕ) : ℤ) :=
    HomologicalComplex.exactAt_single_obj (.up ℤ) 0 V ((n+1 : ℕ) : ℤ) (by omega)
  have target := (quasiIsoAt_iff_exactAt (scalarProjectiveSectionMap R P a)
    ((n+1 : ℕ) : ℤ) source).mp inferInstance
  have ordinary := (exactAt_iff_of_quasiIsoAt
    (projectiveSingleOrdinaryIso R P (Y := Y)).hom ((n+1 : ℕ) : ℤ)).mp target
  exact (HomologicalComplex.extend_exactAt_iff
    (projectiveCoefficientComplex R P Y) ComplexShape.embeddingUpNat
      (show ComplexShape.embeddingUpNat.f (n+1) = ((n+1 : ℕ) : ℤ) by rfl)).mp ordinary

end ToricPower

end
