module

public import ToricPower.ElementPushdownPostcompose

/-!
# Direct image and postcomposition, natural in the coefficient diagram

The comparison is the literal coproduct comparison.  Its naturality is
proved on each sheet, and therefore retains the maps between coefficients
as well as the incidence maps in the base category.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace ToricPower.ElementPushdown

universe u v w z

variable {C : Type} [SmallCategory C] (B : C ⥤ Type)
  {D : Type u} [Category.{v} D] [HasCoproducts.{0} D]
  {D' : Type w} [Category.{z} D'] [HasCoproducts.{0} D']

/-- Naturality of the coproduct comparison in the whole input diagram. -/
def postcomposeDiagramComparison (T : D ⥤ D') :
    (whiskeringRight B.Elements D D').obj T ⋙ functor B ⟶
      functor B ⋙ (whiskeringRight C D D').obj T where
  app E := postcomposeComparison B T E
  naturality {E F} α := by
    apply NatTrans.ext
    funext c
    apply Sigma.hom_ext
    intro r
    change inclusion B (E ⋙ T) c r ≫
        (cellMap B (whiskerRight α T) c ≫ (postcomposeComparison B T F).app c) =
      inclusion B (E ⋙ T) c r ≫
        ((postcomposeComparison B T E).app c ≫ T.map (cellMap B α c))
    rw [inclusion_cellMap_assoc, inclusion_postcomposeComparison,
      inclusion_postcomposeComparison_assoc]
    change T.map (α.app (B.elementsMk c r)) ≫ T.map (inclusion B F c r) =
      T.map (inclusion B E c r) ≫ T.map (cellMap B α c)
    rw [← T.map_comp, ← T.map_comp, inclusion_cellMap]

/-- A functor preserving the actual sheet coproducts commutes with direct
image, naturally in every coefficient diagram. -/
def postcomposeDiagramIso (T : D ⥤ D')
    [∀ (E : B.Elements ⥤ D) (c : C),
      PreservesColimit (Discrete.functor (fun r : B.obj c =>
        E.obj (B.elementsMk c r))) T] :
    functor B ⋙ (whiskeringRight C D D').obj T ≅
      (whiskeringRight B.Elements D D').obj T ⋙ functor B := by
  let α := postcomposeDiagramComparison B T
  letI : IsIso α := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro E
    rw [NatTrans.isIso_iff_isIso_app]
    intro c
    exact postcomposeComparison_app_isIso B T E c
  exact (asIso α).symm

end ToricPower.ElementPushdown

end
