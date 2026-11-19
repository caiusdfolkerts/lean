module

public import ToricPower.CellularRealizationUnit
public import ToricPower.CovariantRepresentableSource

/-! # Linear coend realization and its original representable frames -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

namespace ToricPower.Cellular

universe u v
variable (k : Type u) [Field k] {C : Type u} [Category.{u} C]
  {B : Type v} [Category.{u} B] [Preadditive B] [Linear k B]
  [HasColimitsOfSize.{u,u} B] (P : Cᵒᵖ ⥤ B)

instance realization_linear : (realization k P).Linear k where
  map_smul f r := by
    apply realization_hom_ext k P
    intro c x
    rw [realizationInclusion_map]
    change realizationInclusion k P _ c (r • f.app c x) = _
    rw [_root_.map_smul,Linear.comp_smul,realizationInclusion_map]

@[reassoc]
theorem realizationRepresentableIso_generator {c d : C} (f : c ⟶ d) :
    realizationInclusion k P (representable k c) d (ModuleCat.freeMk f) ≫
      (realizationRepresentableIso k P c).hom = P.map f.op := by
  rw [realizationRepresentableIso,realizationInclusion_desc]
  rw [fromValue_app_freeMk]
  change P.map f.op ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- The canonical frames respect the original contravariant
representable incidence maps. -/
def realizationRepresentableNatIso :
    representableFunctor k ⋙ realization k P ≅ P :=
  NatIso.ofComponents (fun c => realizationRepresentableIso k P c.unop) (by
    intro c d f
    apply (cancel_epi (realizationRepresentableIso k P c.unop).inv).mp
    change realizationInclusion k P (representable k c.unop) c.unop
        (ModuleCat.freeMk (𝟙 c.unop)) ≫
          (realization k P).map (representablePrecompose k f.unop) ≫
            (realizationRepresentableIso k P d.unop).hom = _
    rw [realizationInclusion_map_assoc,representablePrecompose_freeMk,Category.comp_id,
      realizationRepresentableIso_generator]
    change P.map f = (realizationRepresentableIso k P c.unop).inv ≫
      (realizationRepresentableIso k P c.unop).hom ≫ P.map f
    rw [Iso.inv_hom_id_assoc])

end ToricPower.Cellular

end
