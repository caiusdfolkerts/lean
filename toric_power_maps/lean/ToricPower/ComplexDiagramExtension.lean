module

public import ToricPower.ComplexDiagramEquivalence
public import ToricPower.FunctorExtendComplex

/-!
# Extension by zero commutes with literal diagram transposition

The comparison is the identity in every retained degree and the unique
zero-object frame in every omitted degree. It preserves all original
incidence maps and differentials.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace ToricPower

variable {C D : Type*} [Category* C] [Category* D]
  [Preadditive D] [HasZeroObject D]
  {ι ι' : Type*} {shape : ComplexShape ι} {shape' : ComplexShape ι'}
  (F : C ⥤ HomologicalComplex D shape) (e : shape.Embedding shape')

private theorem extensionEvaluation_naturality {c d : C} (f : c ⟶ d) (p : Option ι) :
    (HomologicalComplex.extend.X (complexDiagramTranspose F) p).map f ≫
        (mapExtendXIso ((evaluation C D).obj d) (complexDiagramTranspose F) p).hom =
      (mapExtendXIso ((evaluation C D).obj c) (complexDiagramTranspose F) p).hom ≫
        HomologicalComplex.extend.mapX (F.map f) p := by
  cases p with
  | none => exact (isZero_zero D).eq_of_tgt _ _
  | some p =>
    change (F.map f).f p ≫ 𝟙 _ = 𝟙 _ ≫ (F.map f).f p
    simp only [Category.comp_id,Category.id_comp]

/-- Evaluation of the extended diagram complex is the original
extension of the evaluated complex, naturally in the indexing object. -/
def complexDiagramExtensionEvaluationIso :
    ((complexDiagramTranspose F).extend e).asFunctor ≅ F ⋙ e.extendFunctor D :=
  NatIso.ofComponents
    (fun c => mapExtendIso ((evaluation C D).obj c) (complexDiagramTranspose F) e) (by
      intro c d f
      apply HomologicalComplex.Hom.ext
      funext q
      exact extensionEvaluation_naturality F f (e.r q))

/-- The whole original complex, not just its evaluated homology. -/
def complexDiagramExtensionIso :
    (complexDiagramTranspose F).extend e ≅
      complexDiagramTranspose (F ⋙ e.extendFunctor D) :=
  (complexDiagramEquivalence (L := C) (C := D) shape').fullyFaithfulFunctor.preimageIso
    (complexDiagramExtensionEvaluationIso F e ≪≫
      (complexDiagramTransposeIso (F ⋙ e.extendFunctor D)).symm)

variable {C' D' : Type*} [Category* C'] [Category* D']
  [Preadditive D'] [HasZeroObject D']
  (H : (C ⥤ D) ⥤ (C' ⥤ D')) [H.Additive]

/-- Apply the actual diagram functor and extend, in either order. -/
def complexDiagramMapExtensionIso :
    (H.mapHomologicalComplex shape').obj
      (complexDiagramTranspose (F ⋙ e.extendFunctor D)) ≅
    complexDiagramTranspose
      ((((H.mapHomologicalComplex shape).obj (complexDiagramTranspose F)).asFunctor) ⋙
        e.extendFunctor D') :=
  (H.mapHomologicalComplex shape').mapIso (complexDiagramExtensionIso F e).symm ≪≫
    mapExtendIso H (complexDiagramTranspose F) e ≪≫
    complexDiagramExtensionIso
      (((H.mapHomologicalComplex shape).obj (complexDiagramTranspose F)).asFunctor) e

end ToricPower

end
