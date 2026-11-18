module

public import ToricPower.SheafModuleHomGluing

/-! Restriction of actual local module morphisms to overlaps, with a
sectionwise formula matching the ordinary hom-sheaf gluing condition. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Opposite
namespace ToricPower
universe u v w

section Site
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{w}) {M N : SheafOfModules.{w} R}
  {U V : C}

/-- Restrict an actual local morphism, using the canonical identifications
of iterated slice-site restrictions. -/
def restrictOverHom (inclusion : V ⟶ U) (mapping : M.over U ⟶ N.over U) :
    M.over V ⟶ N.over V :=
  (SheafOfModules.overFunctorMap R inclusion).inv.app M ≫
    (SheafOfModules.overMap R inclusion).map mapping ≫
    (SheafOfModules.overFunctorMap R inclusion).hom.app N

/-- On sections, the restriction is simply evaluation of the original
local morphism at the same smaller open. -/
theorem restrictOverHom_app (inclusion : V ⟶ U) (mapping : M.over U ⟶ N.over U)
    (W : Over V) (value : (M.over V).val.obj (op W)) :
    (restrictOverHom R inclusion mapping).val.app (op W) value =
      mapping.val.app (op ((Over.map inclusion).obj W)) value := by
  rfl

end Site

namespace SheafModuleGluing
open AlgebraicGeometry TopologicalSpace
universe v'
variable {X : Scheme.{u}} {Index : Type v'} (opens : Index → X.Opens)
  {M N : X.Modules} (maps : ∀ index, M.over (opens index) ⟶ N.over (opens index))

/-- Equality of the actual module morphisms on pairwise intersections
implies the hom-sheaf compatibility used by the gluing construction. -/
theorem compatible_of_overlap_restrictions
    (equal : ∀ first second,
      restrictOverHom X.ringCatSheaf (homOfLE (inf_le_left :
        opens first ⊓ opens second ≤ opens first)) (maps first) =
      restrictOverHom X.ringCatSheaf (homOfLE (inf_le_right :
        opens first ⊓ opens second ≤ opens second)) (maps second)) :
    Compatible opens maps := by
  intro first second
  apply CategoryTheory.NatTrans.ext
  funext W
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro value
  change (maps first).val.app
      (op ((Over.map (Opens.infLELeft (opens first) (opens second))).obj W.unop)) value =
    (maps second).val.app
      (op ((Over.map (Opens.infLERight (opens first) (opens second))).obj W.unop)) value
  have onSections := congrArg (fun mapping => mapping.val.app W value) (equal first second)
  exact (restrictOverHom_app X.ringCatSheaf
      (Opens.infLELeft (opens first) (opens second)) (maps first) W.unop value).symm.trans
    (onSections.trans (restrictOverHom_app X.ringCatSheaf
      (Opens.infLERight (opens first) (opens second)) (maps second) W.unop value))

end SheafModuleGluing
end ToricPower
