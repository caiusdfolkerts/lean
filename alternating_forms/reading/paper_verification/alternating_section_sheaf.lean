module

public import PaperVerification.AlternatingSectionPresheaf
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Defs

/-!
# The global sheaf functional defined by an alternating form

The domain is the sheafification of the sectionwise second exterior power.
Thus this is a morphism from the actual exterior-power sheaf, and not just
a collection of formulas in a chosen frame.  The final theorem computes
it on sheafified wedges, retaining the original coefficients and signs.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped BigOperators
open TauCeti.SheafOfModules (ringCatSheaf)

universe u v w

namespace PaperVerification.AlternatingSectionSheaf

variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {R : Sheaf J CommRingCat.{u}}
variable {M : SheafOfModules.{u} (ringCatSheaf R)}
variable {P N : Type u} [Fintype P]
variable (a b : P → N)
variable (coord : N → (M ⟶ SheafOfModules.unit (ringCatSheaf R)))
variable (c : P → (SheafOfModules.unit (ringCatSheaf R)).val.sections)

local instance (X : Cᵒᵖ) : CommRing ((ringCatSheaf R).obj.obj X) :=
  inferInstanceAs (CommRing (R.obj.obj X))

local instance (X : Cᵒᵖ) : CommRing ((SheafOfModules.unit (ringCatSheaf R)).val.obj X) :=
  inferInstanceAs (CommRing (R.obj.obj X))

/-- Sheafification of the local alternating functional, followed by the
canonical identification of the sheafified structure sheaf with itself. -/
def functional :
    (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).obj
        ((PresheafOfModulesOfCommRing.exteriorPower 2).obj M.val) ⟶
      SheafOfModules.unit (ringCatSheaf R) :=
  (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map
      (AlternatingSectionPresheaf.functional a b (fun i ↦ (coord i).val) c) ≫
    (TauCeti.SheafOfModules.sheafificationIso (ringCatSheaf R)
      (SheafOfModules.unit (ringCatSheaf R))).hom

/-- The global functional restricts to the original local functional along
the actual sheafification map. -/
theorem unit_comp_functional :
    (PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).unit.app
        ((PresheafOfModulesOfCommRing.exteriorPower 2).obj M.val) ≫
      (functional a b coord c).val =
    AlternatingSectionPresheaf.functional a b (fun i ↦ (coord i).val) c :=
  TauCeti.SheafOfModules.unit_comp_val_sheafification_map_comp_sheafificationIso_hom _

/-- On every open, the sheaf functional evaluates a sheafified wedge by
the alternating coefficient formula. -/
theorem functional_app_sheafified_wedge (X : Cᵒᵖ) (v : Fin 2 → M.val.obj X) :
    (functional a b coord c).val.app X
        (((PresheafOfModules.sheafificationAdjunction
            (𝟙 (ringCatSheaf R).obj)).unit.app
          ((PresheafOfModulesOfCommRing.exteriorPower 2).obj M.val)).app X
            (ModuleCat.exteriorPower.mk v)) =
      ∑ p, (c p).eval X *
        ((coord (a p)).val.app X (v 0) * (coord (b p)).val.app X (v 1) -
         (coord (b p)).val.app X (v 0) * (coord (a p)).val.app X (v 1)) := by
  have h := ConcreteCategory.congr_hom
    (congrArg (fun f ↦ f.app X) (unit_comp_functional a b coord c))
    (ModuleCat.exteriorPower.mk v)
  exact h.trans
    (AlternatingSectionPresheaf.functional_app_mk a b (fun i ↦ (coord i).val) c X v)

end PaperVerification.AlternatingSectionSheaf
