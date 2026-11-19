module

public import ToricPower.CellularRealization

/-! # The original coend unit and functorial vector inclusions -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace ToricPower.Cellular

universe u v

variable (k : Type u) [Field k] {C : Type u} [Category.{u} C]
  {A : Type v} [Category.{u} A] [Preadditive A] [Linear k A]
  [HasColimitsOfSize.{u,u} A] (P : Cᵒᵖ ⥤ A)

@[simp]
theorem realizationUnit_app_apply (M : C ⥤ ModuleCat.{u} k)
    (c : C) (x : M.obj c) :
    ((realizationHomAdjunction k P).unit.app M).app c x =
      realizationInclusion k P M c x :=
  Category.comp_id _

@[reassoc]
theorem realizationInclusion_map {M N : C ⥤ ModuleCat.{u} k}
    (f : M ⟶ N) (c : C) (x : M.obj c) :
    realizationInclusion k P M c x ≫ (realization k P).map f =
      realizationInclusion k P N c (f.app c x) := by
  have h := ConcreteCategory.congr_hom
    (congrArg (fun η => η.app c) ((realizationHomAdjunction k P).unit.naturality f)) x
  simp only [NatTrans.comp_app,ModuleCat.comp_apply,Functor.id_map,Functor.comp_map,
    realizationUnit_app_apply,homDiagram_map_app_apply] at h
  change realizationInclusion k P N c (f.app c x) =
    ((realizationHomAdjunction k P).unit.app M).app c x ≫ (realization k P).map f at h
  rw [realizationUnit_app_apply] at h
  exact h.symm

end ToricPower.Cellular

end
