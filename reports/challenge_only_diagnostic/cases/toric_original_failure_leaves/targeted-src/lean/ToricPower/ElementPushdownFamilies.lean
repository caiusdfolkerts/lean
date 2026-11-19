module

public import ToricPower.ElementPushdownPostcompose

/-! # Direct image commutes naturally with families of colimit-preserving functors -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace ToricPower.ElementPushdown

universe u v w z a b

variable {C : Type} [SmallCategory C] (B : C ⥤ Type)
  {D : Type u} [Category.{v} D] [HasCoproducts.{0} D]
  {D' : Type w} [Category.{z} D'] [HasCoproducts.{0} D']
  {J : Type a} [Category.{b} J]

/-- The actual coproduct comparison is natural in a whole parameter
category, including every differential when the parameter is a complex. -/
def postcomposeFamilyIso (T : J ⥤ D ⥤ D') (E : B.Elements ⥤ D)
    [∀ j c, PreservesColimit (Discrete.functor (fun r : B.obj c =>
      E.obj (B.elementsMk c r))) (T.obj j)] :
    T ⋙ (whiskeringLeft C D D').obj (obj B E) ≅
      T ⋙ (whiskeringLeft B.Elements D D').obj E ⋙ functor B := by
  let α := whiskerLeft T (postcomposeFunctorComparison B (D' := D') E)
  letI : IsIso α := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro j
    rw [NatTrans.isIso_iff_isIso_app]
    intro c
    exact postcomposeComparison_app_isIso B (T.obj j) E c
  exact (asIso α).symm

end ToricPower.ElementPushdown

end
