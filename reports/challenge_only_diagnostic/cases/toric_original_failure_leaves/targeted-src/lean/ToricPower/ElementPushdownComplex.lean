module

public import ToricPower.ElementPushdownNaturality
public import ToricPower.ComplexDiagramFunctor
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-!
# Direct image of diagrams of complexes

Taking the sheet coproduct degree by degree agrees with taking the
coproduct in the category of complexes.  The comparison respects the
actual differentials, incidence maps, and maps of input complexes.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace ToricPower.ElementPushdown

universe u v

variable {C : Type} [SmallCategory C] (B : C ⥤ Type)
  {D : Type u} [Category.{v} D] [HasZeroMorphisms D] [HasCoproducts.{0} D]
  [(functor B (D := D)).PreservesZeroMorphisms]
  {ι : Type*} (shape : ComplexShape ι)

/-- The degreewise coproduct comparison, including its chain-map identity. -/
def complexComparison :
    (functor B (D := D)).mapHomologicalComplex shape ⋙
        HomologicalComplex.complexOfFunctorsToFunctorToComplex ⟶
      HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
        functor B (D := HomologicalComplex D shape) where
  app K :=
    { app c :=
        { f q := (postcomposeComparison B
            (HomologicalComplex.eval D shape q) K.asFunctor).app c
          comm' q r _ := by
            exact (congrArg (fun α => α.app c)
              ((postcomposeFunctorComparison B K.asFunctor).naturality
                (HomologicalComplex.dNatTrans D shape q r))).symm }
      naturality {c d} f := by
        apply HomologicalComplex.Hom.ext
        funext q
        exact (postcomposeComparison B
          (HomologicalComplex.eval D shape q) K.asFunctor).naturality f }
  naturality {K L} f := by
    apply NatTrans.ext
    funext c
    apply HomologicalComplex.Hom.ext
    funext q
    exact congrArg (fun α => α.app c)
      ((postcomposeDiagramComparison B (HomologicalComplex.eval D shape q)).naturality
        (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f))

/-- Evaluation preserves coproducts, so the canonical comparison is an
isomorphism for arbitrary complexes, without boundedness assumptions. -/
def complexIso :
    (functor B (D := D)).mapHomologicalComplex shape ⋙
        HomologicalComplex.complexOfFunctorsToFunctorToComplex ≅
      HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
        functor B (D := HomologicalComplex D shape) := by
  let α := complexComparison B (D := D) shape
  letI : IsIso α := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro K
    rw [NatTrans.isIso_iff_isIso_app]
    intro c
    haveI (q : ι) : IsIso (((α.app K).app c).f q) :=
      postcomposeComparison_app_isIso B (HomologicalComplex.eval D shape q) K.asFunctor c
    exact HomologicalComplex.Hom.isIso_of_components _
  exact asIso α

end ToricPower.ElementPushdown

end
