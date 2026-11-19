module

public import ToricPower.ElementPushdownComplex
public import ToricPower.ComplexDiagramEquivalence

/-!
# Commuting direct image with functors on complexes

This is an isomorphism of whole functors.  Its only preservation
hypothesis is preservation of the actual sheet coproducts in the
category of complexes; finite sheets therefore suffice for an additive
complex functor.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace ToricPower.ElementPushdown

universe u v w z

variable {C : Type} [SmallCategory C] (B : C ⥤ Type)
  {D : Type u} [Category.{v} D] [HasZeroMorphisms D] [HasCoproducts.{0} D]
  {D' : Type w} [Category.{z} D'] [HasZeroMorphisms D'] [HasCoproducts.{0} D']
  [(functor B (D := D)).PreservesZeroMorphisms]
  [(functor B (D := D')).PreservesZeroMorphisms]
  {ι : Type*} (shape : ComplexShape ι)

/-- Actual direct image commutes with pointwise application of a complex
functor preserving the sheet coproducts. -/
def complexFunctorIso
    (F : HomologicalComplex D shape ⥤ HomologicalComplex D' shape)
    [∀ (E : B.Elements ⥤ HomologicalComplex D shape) (c : C),
      PreservesColimit (Discrete.functor (fun r : B.obj c =>
        E.obj (B.elementsMk c r))) F] :
    (functor B (D := D)).mapHomologicalComplex shape ⋙
        complexDiagramPostcompose (L := C) F ≅
      complexDiagramPostcompose (L := B.Elements) F ⋙
        (functor B (D := D')).mapHomologicalComplex shape :=
  Functor.fullyFaithfulCancelRight
    HomologicalComplex.complexOfFunctorsToFunctorToComplex
    (Functor.isoWhiskerLeft ((functor B (D := D)).mapHomologicalComplex shape)
        (complexDiagramPostcomposeAsFunctorIso (L := C) shape F) ≪≫
      Functor.isoWhiskerRight (complexIso B (D := D) shape)
        ((whiskeringRight C _ _).obj F) ≪≫
      Functor.isoWhiskerLeft HomologicalComplex.complexOfFunctorsToFunctorToComplex
        (postcomposeDiagramIso B F) ≪≫
      Functor.isoWhiskerRight
        (complexDiagramPostcomposeAsFunctorIso (L := B.Elements) shape F).symm
        (functor B (D := HomologicalComplex D' shape)) ≪≫
      Functor.isoWhiskerLeft (complexDiagramPostcompose (L := B.Elements) F)
        (complexIso B (D := D') shape).symm)

end ToricPower.ElementPushdown

end
