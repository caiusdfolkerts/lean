module

public import ToricPower.ClosedSupportDetection

/-! # Returning shifted detection maps from the actual closed support -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.Cellular

universe u w w'
variable (R : Type u) [Ring R] {B : Type u} [Preorder B]
  (P : B → Prop) (downward : Antitone P)
  [HasDerivedCategory.{w} (B ⥤ ModuleCat.{u} R)]
  [HasDerivedCategory.{w'} ({b : B // P b} ⥤ ModuleCat.{u} R)]
  (K : CochainComplex (B ⥤ ModuleCat.{u} R) ℤ)
  (vanishes : ∀ b : B, ¬ P b →
    ((((evaluation B (ModuleCat.{u} R)).obj b).mapHomologicalComplex (.up ℤ)).obj K).Acyclic)

/-- Shift the genuine support model through the exact extension
functor, preserving the whole unbounded target. -/
def shiftedClosedSupportModelIso (q : ℤ) :
    (DerivedCategory.Q.obj K)⟦q⟧ ≅
      (closedFaceExtensionFunctor R P downward).mapDerivedCategory.obj
        (((closedFaceRestriction R P).mapDerivedCategory.obj (DerivedCategory.Q.obj K))⟦q⟧) :=
  (shiftFunctor (DerivedCategory (B ⥤ ModuleCat.{u} R)) q).mapIso
      (closedSupportModelIso R P downward K vanishes) ≪≫
    (((closedFaceExtensionFunctor R P downward).mapDerivedCategory.commShiftIso q).app
      ((closedFaceRestriction R P).mapDerivedCategory.obj (DerivedCategory.Q.obj K))).symm

include downward vanishes in
/-- A shifted nonzero test on the actual closed support returns to a
shifted nonzero map into the original target, through its exact unit. -/
theorem extend_shifted_nonzero_from_closed_support
    (E : DerivedCategory (B ⥤ ModuleCat.{u} R)) (q : ℤ)
    (f : (closedFaceRestriction R P).mapDerivedCategory.obj E ⟶
      ((closedFaceRestriction R P).mapDerivedCategory.obj (DerivedCategory.Q.obj K))⟦q⟧)
    (nonzero : f ≠ 0) :
    ∃ g : E ⟶ (DerivedCategory.Q.obj K)⟦q⟧, g ≠ 0 := by
  let e := shiftedClosedSupportModelIso R P downward K vanishes q
  let target := ((closedFaceRestriction R P).mapDerivedCategory.obj
    (DerivedCategory.Q.obj K))⟦q⟧
  let adj := closedFaceDerivedAdjunction R P downward
  let a := adj.homEquiv E target f
  refine ⟨a ≫ e.inv,?_⟩
  intro zero
  have mapped : a = 0 := by
    rw [← cancel_mono e.inv,zero_comp]
    exact zero
  apply nonzero
  apply (adj.homEquiv E target).injective
  exact mapped.trans (adj.homAddEquiv_zero E target).symm

end ToricPower.Cellular

end
