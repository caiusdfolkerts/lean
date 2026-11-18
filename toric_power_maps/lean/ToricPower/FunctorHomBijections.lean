module

public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.Algebra.Group.Int.Defs

/-! # Transport of actual morphism-map bijections -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace ToricPower

variable {C D : Type*} [Category* C] [Category* D]

theorem functorMap_bijective_iff_of_natIso {F G : C ⥤ D} (e : F ≅ G) (X Y : C) :
    Function.Bijective (F.map : (X ⟶ Y) → _) ↔
      Function.Bijective (G.map : (X ⟶ Y) → _) := by
  let t := (e.app X).homCongr (e.app Y)
  have h : (G.map : (X ⟶ Y) → _) = t ∘ F.map := by
    funext f
    dsimp [t, Iso.homCongr]
    rw [e.hom.naturality, Iso.inv_hom_id_app_assoc]
  rw [h]
  exact (Function.Bijective.of_comp_iff' t.bijective _).symm

theorem functorMap_bijective_iff_of_iso (F : C ⥤ D)
    {X Y X' Y' : C} (eX : X ≅ X') (eY : Y ≅ Y') :
    Function.Bijective (F.map : (X ⟶ Y) → _) ↔
      Function.Bijective (F.map : (X' ⟶ Y') → _) := by
  let source := eX.homCongr eY
  let target := (F.mapIso eX).homCongr (F.mapIso eY)
  have h : (F.map : (X' ⟶ Y') → _) ∘ source = target ∘ F.map := by
    funext f
    simp only [Function.comp_apply, source, target, Iso.homCongr_apply,
      F.map_comp, Functor.mapIso_inv, Functor.mapIso_hom]
  exact ((Function.Bijective.of_comp_iff' target.bijective _).symm.trans
    (by rw [← h])).trans (Function.Bijective.of_comp_iff _ source.bijective)

theorem functorMap_bijective_iff_shift [HasShift C ℤ] [HasShift D ℤ]
    (F : C ⥤ D) [F.CommShift ℤ] (X Y : C) (p : ℤ) :
    Function.Bijective (F.map : (X⟦p⟧ ⟶ Y⟦p⟧) → _) ↔
      Function.Bijective (F.map : (X ⟶ Y) → _) := by
  have source := (Functor.FullyFaithful.ofFullyFaithful (shiftFunctor C p)).map_bijective X Y
  have target := (Functor.FullyFaithful.ofFullyFaithful (shiftFunctor D p)).map_bijective
    (F.obj X) (F.obj Y)
  exact (Function.Bijective.of_comp_iff _ source).symm.trans
    ((functorMap_bijective_iff_of_natIso (F.commShiftIso p) X Y).trans
      (Function.Bijective.of_comp_iff' target _))

end ToricPower

end
