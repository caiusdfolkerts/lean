module

public import ToricPower.ComplexDiagramFunctor
public import Mathlib.CategoryTheory.Equivalence

/-! # The literal equivalence between complexes of diagrams and diagrams of complexes -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace ToricPower

variable {L C D : Type*} [Category* L] [Category* C] [Category* D]
  [HasZeroMorphisms C] [HasZeroMorphisms D]
  {ι : Type*} (shape : ComplexShape ι)

/-- Both directions retain every differential and every incidence map. -/
def complexDiagramEquivalence :
    HomologicalComplex (L ⥤ C) shape ≌ (L ⥤ HomologicalComplex C shape) where
  functor := HomologicalComplex.complexOfFunctorsToFunctorToComplex
  inverse := complexDiagramTransposeFunctor
  unitIso := NatIso.ofComponents (fun K => Iso.refl K) (by
    intro K M f
    ext q l
    change (f.f q).app l ≫ 𝟙 _ = 𝟙 _ ≫ (f.f q).app l
    simp only [Category.comp_id, Category.id_comp])
  counitIso := NatIso.ofComponents (fun F => complexDiagramTransposeIso F) (by
    intro F G α
    ext l q
    change (α.app l).f q ≫ 𝟙 _ = 𝟙 _ ≫ (α.app l).f q
    simp only [Category.comp_id, Category.id_comp])
  functor_unitIso_comp K := by
    ext l q
    simp [complexDiagramTransposeIso]

instance complexDiagramAsFunctor_full :
    (HomologicalComplex.complexOfFunctorsToFunctorToComplex
      (T := L) (V := C) (c := shape)).Full :=
  (complexDiagramEquivalence (L := L) (C := C) shape).fullyFaithfulFunctor.full

instance complexDiagramAsFunctor_faithful :
    (HomologicalComplex.complexOfFunctorsToFunctorToComplex
      (T := L) (V := C) (c := shape)).Faithful :=
  (complexDiagramEquivalence (L := L) (C := C) shape).fullyFaithfulFunctor.faithful

/-- Pointwise application of a complex functor, followed by transposition,
recovers ordinary postcomposition as a natural isomorphism. -/
def complexDiagramPostcomposeAsFunctorIso
    (F : HomologicalComplex C shape ⥤ HomologicalComplex D shape) :
    complexDiagramPostcompose (L := L) F ⋙
        HomologicalComplex.complexOfFunctorsToFunctorToComplex ≅
      HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
        (whiskeringRight L _ _).obj F :=
  Functor.isoWhiskerLeft
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
        (whiskeringRight L _ _).obj F)
      (complexDiagramEquivalence (L := L) (C := D) shape).counitIso ≪≫
    Functor.rightUnitor _

end ToricPower

end
