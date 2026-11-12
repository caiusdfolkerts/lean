module

public import ToricPower.LinearHomFromCochainToSingle

/-! # Target naturality of the signed cellular Hom comparison

Every actual coefficient morphism commutes with the original signed
Hom differential and the ordinary contravariant cellular chains.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite
open CochainComplex HomComplex HomologicalComplex

namespace ToricPower

universe u v r
variable (R : Type r) [CommRing R]
  {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  (K : CochainComplex C ℕ)

/-- The ordinary coefficient map induced by an arbitrary target morphism. -/
def ordinaryCochainCoefficientsMap {Y Z : C} (f : Y ⟶ Z) :
    ordinaryCochainCoefficients R K Y ⟶ ordinaryCochainCoefficients R K Z :=
  (NatTrans.mapHomologicalComplex ((linearYoneda R C).map f) (.down ℕ)).app K.op

/-- Unsigned coordinate evaluation commutes with every target map. -/
theorem cochainHomToSingleRawDegreeEquiv_naturality {Y Z : C} (f : Y ⟶ Z) (n : ℕ)
    (z : Cochain (K.extend ComplexShape.embeddingUpNat)
      ((CochainComplex.singleFunctor C 0).obj Y) (-(n : ℤ))) :
    cochainHomToSingleRawDegreeEquiv R K Z n
      (homCochainPostcomp R (K.extend ComplexShape.embeddingUpNat)
        ((CochainComplex.singleFunctor C 0).map f) (-(n : ℤ)) z) =
      cochainHomToSingleRawDegreeEquiv R K Y n z ≫ f := by
  obtain ⟨g, rfl⟩ := Cochain.toSingleMk_surjective z (n : ℤ) (by omega)
  change cochainHomToSingleRawDegreeEquiv R K Z n
    ((Cochain.toSingleMk g _).comp (.ofHom ((CochainComplex.singleFunctor C 0).map f))
      (add_zero (-(n : ℤ)))) = _
  rw [← Cochain.toSingleMk_postcomp, cochainHomToSingleRawDegreeEquiv_toSingleMk,
    cochainHomToSingleRawDegreeEquiv_toSingleMk, Category.assoc]

/-- Naturality of every degree sign, before extending the coefficient complex. -/
theorem cochainHomToSingleRestrictionIso_naturality {Y Z : C} (f : Y ⟶ Z) :
    HomologicalComplex.restrictionMap
        (linearHomComplexMap R (K.extend ComplexShape.embeddingUpNat)
          ((CochainComplex.singleFunctor C 0).map f)) ComplexShape.embeddingDownNat ≫
        (cochainHomToSingleRestrictionIso R K Z).hom =
      (cochainHomToSingleRestrictionIso R K Y).hom ≫ ordinaryCochainCoefficientsMap R K f := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change cochainHomDualSign n • cochainHomToSingleRawDegreeEquiv R K Z n
      (homCochainPostcomp R (K.extend ComplexShape.embeddingUpNat)
        ((CochainComplex.singleFunctor C 0).map f) (-(n : ℤ)) z) =
    (cochainHomDualSign n • cochainHomToSingleRawDegreeEquiv R K Y n z) ≫ f
  rw [cochainHomToSingleRawDegreeEquiv_naturality, Linear.units_smul_comp]

/-- The full signed chain isomorphism is natural in every actual
coefficient map, before localization. -/
theorem cochainHomToSingleExtendedIso_naturality {Y Z : C} (f : Y ⟶ Z) :
    linearHomComplexMap R (K.extend ComplexShape.embeddingUpNat)
        ((CochainComplex.singleFunctor C 0).map f) ≫
        (cochainHomToSingleExtendedIso R K Z).hom =
      (cochainHomToSingleExtendedIso R K Y).hom ≫
        HomologicalComplex.extendMap (ordinaryCochainCoefficientsMap R K f)
          ComplexShape.embeddingDownNat := by
  apply (ComplexShape.embeddingDownNat.homEquiv _ _).injective
  apply Subtype.ext
  change ComplexShape.embeddingDownNat.homRestrict (_ ≫ _) =
    ComplexShape.embeddingDownNat.homRestrict (_ ≫ _)
  rw [ComplexShape.embeddingDownNat.homRestrict_precomp,
    ComplexShape.embeddingDownNat.homRestrict_comp_extendMap]
  change _ ≫ ComplexShape.embeddingDownNat.homRestrict
      (ComplexShape.embeddingDownNat.liftExtend (cochainHomToSingleRestrictionIso R K Z).hom
        (cochainHomToSingleRestriction_hasLift R K Z)) =
    ComplexShape.embeddingDownNat.homRestrict
      (ComplexShape.embeddingDownNat.liftExtend (cochainHomToSingleRestrictionIso R K Y).hom
        (cochainHomToSingleRestriction_hasLift R K Y)) ≫ _
  rw [ComplexShape.embeddingDownNat.homRestrict_liftExtend,
    ComplexShape.embeddingDownNat.homRestrict_liftExtend]
  exact cochainHomToSingleRestrictionIso_naturality R K f

end ToricPower

end
