module

public import ToricPower.InternalDualTensorInverse
public import ToricPower.InternalDualUnitMatrix

/-!
# The specified inverse pairing determines the inverse frame

These identities characterize the canonical dual frame by the literal
pairing of the two original frame sections. They also retain the actual
strong monoidal pullback comparison, so the characterization can be
used on a genuine affine chart without replacing any of its maps.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MonoidalCategory MonoidalClosed Opposite

namespace ToricPower

universe u v u' v'

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
  {L D : C} (eDL : D ⊗ L ≅ 𝟙_ C) (eLD : L ⊗ D ≅ 𝟙_ C)
  (frame : 𝟙_ C ≅ L)

/-- The frame obtained by dualizing the given frame and the given
actual inverse pairing. -/
def inversePairingFrame : D ≅ 𝟙_ C :=
  inverseTensorInternalDualIso L D eDL eLD ≪≫
    (internalDual C).mapIso frame.op ≪≫ internalDualUnitIso C

/-- Removing only the final unit identification leaves the specified
transpose and the specified original frame. -/
theorem inversePairingFrame_hom_unit_inv :
    (inversePairingFrame eDL eLD frame).hom ≫ (internalDualUnitIso C).inv =
      curry eLD.hom ≫ (pre frame.hom).app (𝟙_ C) := by
  simp only [inversePairingFrame, Iso.trans_hom, Category.assoc,
    Iso.hom_inv_id, Category.comp_id, Functor.mapIso_hom, Iso.op_hom,
    inverseTensorInternalDualIso_hom]
  rfl

/-- Pairing to the actual unit characterizes the canonical inverse
frame, with no unspecified nonzero scalar. -/
theorem inversePairingFrame_inv_eq_of_pairing (g : 𝟙_ C ⟶ D)
    (paired : (frame.hom ⊗ₘ g) ≫ eLD.hom = (λ_ (𝟙_ C)).hom) :
    g = (inversePairingFrame eDL eLD frame).inv := by
  apply (cancel_mono (inversePairingFrame eDL eLD frame).hom).mp
  rw [Iso.inv_hom_id]
  apply (cancel_mono (internalDualUnitIso C).inv).mp
  rw [Category.assoc, inversePairingFrame_hom_unit_inv, Category.id_comp]
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_pre_app, uncurry_curry]
  change (𝟙_ C) ◁ g ≫ frame.hom ▷ D ≫ eLD.hom =
    uncurry (TauCeti.ihomUnitIso (𝟙_ C) (𝟙_ C)).inv
  rw [TauCeti.ihomUnitIso_inv, uncurry_curry,
    TauCeti.ExactPairing.unit_evaluation]
  rw [← tensorHom_def'_assoc, paired]
  exact unitors_equal

variable {E : Type u'} [Category.{v'} E] [MonoidalCategory E] [MonoidalClosed E]
  (F : C ⥤ E) [F.Monoidal]

/-- The canonical internal-dual comparison is the transpose of the
actual transported evaluation pairing. -/
theorem internalDualComparison_curry (evaluation : L ⊗ D ⟶ 𝟙_ C) :
    F.map (curry evaluation) ≫ (internalDualComparison F).app (op L) =
      curry (Functor.LaxMonoidal.μ F L D ≫ F.map evaluation ≫
        Functor.OplaxMonoidal.η F) := by
  apply uncurry_injective
  change uncurry (F.map (curry evaluation) ≫
    (F.ihomComparison L).natTrans.app (𝟙_ C) ≫
    (ihom (F.obj L)).map (Functor.OplaxMonoidal.η F)) = _
  rw [← Category.assoc, uncurry_natural_right, uncurry_natural_left,
    Functor.uncurry_ihomComparison, uncurry_curry]
  rw [Functor.LaxMonoidal.μ_natural_right_assoc, ← F.map_comp]
  rw [← uncurry_eq, uncurry_curry]
  exact Category.assoc _ _ _

end ToricPower

end
