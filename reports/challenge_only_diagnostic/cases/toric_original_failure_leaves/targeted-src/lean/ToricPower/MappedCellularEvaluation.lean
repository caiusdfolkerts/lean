module

public import ToricPower.MappedCellularRealizationIso
public import ToricPower.CellularRealizationLinear

/-!
# The actual mapped coend counit on its original generators

Evaluation is the original adjunction counit, transported through the
canonical mapped-coend comparison. Its value on every unrestricted Hom
coefficient is the original coefficient morphism under the given
functor. This identifies the map used in geometric reconstruction.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace ToricPower.Cellular

universe u v w
variable (k : Type u) [Field k] {C : Type u} [Category.{u} C]
  {A : Type v} [Category.{u} A] [Preadditive A] [Linear k A]
  {B : Type w} [Category.{u} B] [Preadditive B] [Linear k B]
  [HasColimitsOfSize.{u,u} A] [HasColimitsOfSize.{u,u} B]
  (F : A ⥤ B) [F.Additive] [F.Linear k] [PreservesColimitsOfSize.{u,u} F]
  (P : Cᵒᵖ ⥤ A)

@[reassoc]
theorem realizationCounit_generator (E : A) (c : C) (h : P.obj (op c) ⟶ E) :
    realizationInclusion k P ((homDiagram k P).obj E) c h ≫
      (realizationHomAdjunction k P).counit.app E = h := by
  change realizationInclusion k P ((homDiagram k P).obj E) c h ≫
    realizationDesc k P (𝟙 ((homDiagram k P).obj E)) = h
  rw [realizationInclusion_desc]
  rfl

/-- The original counit after the genuine coefficient-functor comparison. -/
def mappedRealizationCounit : homDiagram k P ⋙ realization k (P ⋙ F) ⟶ F :=
  Functor.whiskerLeft (homDiagram k P) (mappedRealizationIso k F P).inv ≫
    (Functor.associator (homDiagram k P) (realization k P) F).inv ≫
    Functor.whiskerRight (realizationHomAdjunction k P).counit F ≫
    (Functor.leftUnitor F).hom

@[reassoc]
theorem mappedRealizationCounit_generator (E : A) (c : C) (h : P.obj (op c) ⟶ E) :
    realizationInclusion k (P ⋙ F) ((homDiagram k P).obj E) c h ≫
      (mappedRealizationCounit k F P).app E = F.map h := by
  change realizationInclusion k (P ⋙ F) ((homDiagram k P).obj E) c h ≫
    mappedRealizationComparisonInverse k F P ((homDiagram k P).obj E) ≫
      𝟙 _ ≫ F.map ((realizationHomAdjunction k P).counit.app E) ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]
  erw [mappedRealizationComparisonInverse_generator_assoc, ← F.map_comp,
    realizationCounit_generator]

/-- In the genuine representable coend frame, evaluation is the
original given morphism, with no independent target identification. -/
@[reassoc]
theorem mappedRealizationCounit_representable (E : A) (c : C) (h : P.obj (op c) ⟶ E) :
    (realizationRepresentableIso k (P ⋙ F) c).inv ≫
      (realization k (P ⋙ F)).map (fromValue k ((homDiagram k P).obj E) c h) ≫
        (mappedRealizationCounit k F P).app E = F.map h := by
  change realizationInclusion k (P ⋙ F) (representable k c) c (ModuleCat.freeMk (𝟙 c)) ≫
    (realization k (P ⋙ F)).map (fromValue k ((homDiagram k P).obj E) c h) ≫ _ = _
  rw [realizationInclusion_map_assoc]
  change realizationInclusion k (P ⋙ F) ((homDiagram k P).obj E) c
    (evaluate k ((homDiagram k P).obj E) c
      (fromValue k ((homDiagram k P).obj E) c h)) ≫ _ = _
  rw [evaluate_fromValue, mappedRealizationCounit_generator]

end ToricPower.Cellular

end
