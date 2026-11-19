module

public import ToricPower.CovariantCopowerComparison

/-!
# Naturality of label change in every vector diagram

The two actions on the original vector copowers commute. Thus an actual
isomorphism of label diagrams gives an isomorphism of the complete
copower functors, including all maps between arbitrary vector diagrams.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.Cellular

universe u v

variable (k : Type u) [Field k]
  {C : Type u} [Category.{u} C]
  {B : Type v} [Category.{u} B] [Preadditive B] [Linear k B]
  [HasCoproducts.{u} B] {Q Q' : C ⥤ B}

/-- Label maps commute with the original vector-diagram maps. -/
theorem covariantCopowerLabelMap_natural (α : Q ⟶ Q')
    {M M' : C ⥤ ModuleCat.{u} k} (β : M ⟶ M') :
    covariantCopowerMap k Q β ≫ covariantCopowerLabelMap k M' α =
      covariantCopowerLabelMap k M α ≫ covariantCopowerMap k Q' β := by
  ext c
  apply vectorCopower_hom_ext k (Q.obj c) (M.obj c)
  intro x
  change vectorCopowerInclusion k (Q.obj c) (M.obj c) x ≫
      (vectorCopowerFunctor k (Q.obj c)).map (β.app c) ≫
        vectorCopowerMapObject k (α.app c) (M'.obj c) =
    vectorCopowerInclusion k (Q.obj c) (M.obj c) x ≫
      vectorCopowerMapObject k (α.app c) (M.obj c) ≫
        (vectorCopowerFunctor k (Q'.obj c)).map (β.app c)
  rw [vectorCopowerInclusion_map_assoc, vectorCopowerInclusion_mapObject,
    vectorCopowerInclusion_mapObject_assoc, vectorCopowerInclusion_map]

/-- A label isomorphism identifies the whole unrestricted copower
functor, with no dimension or support restriction on its input. -/
def covariantCopowerLabelFunctorIso (e : Q ≅ Q') :
    covariantCopowerFunctor k Q ≅ covariantCopowerFunctor k Q' :=
  NatIso.ofComponents (fun M => (covariantCopowerLabelFunctor k M).mapIso e)
    (fun β => covariantCopowerLabelMap_natural k e.hom β)

end ToricPower.Cellular

end
