module

public import ToricPower.ElementDiagramPushdown

/-! # Exact direct image of element diagrams in an AB4 category -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.ElementPushdown

universe u v

variable {C : Type} [SmallCategory C] (B : C ⥤ Type)
  {D : Type u} [Category.{v} D] [Abelian D] [HasCoproducts.{0} D] [AB4OfSize.{0} D]

instance preservesFiniteLimits : PreservesFiniteLimits (functor B (D := D)) :=
  preservesFiniteLimits_of_evaluation _ (fun c =>
    preservesFiniteLimits_of_natIso (evaluationIso B (D := D) c).symm)

instance preservesFiniteColimits : PreservesFiniteColimits (functor B (D := D)) :=
  preservesFiniteColimits_of_evaluation _ (fun c =>
    preservesFiniteColimits_of_natIso (evaluationIso B (D := D) c).symm)

instance additive : (functor B (D := D)).Additive :=
  (functor B (D := D)).additive_of_preserves_binary_products

end ToricPower.ElementPushdown

end
