module

public import Mathlib.CategoryTheory.Monoidal.Functor

/-! # A specified local tensor frame, with its exact inverse map -/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

namespace ToricPower

variable {C D : Type*} [Category* C] [Category* D]
  [MonoidalCategory C] [MonoidalCategory D]
  (F : C ⥤ D) [F.LaxMonoidal] (L : C)
  [∀ M : C, IsIso (Functor.LaxMonoidal.μ F M L)]
  (frame : 𝟙_ D ≅ F.obj L)

/-- Only the specified tensor comparisons need to be invertible. -/
def tensorRightLaxCommIso :
    F ⋙ tensorRight (F.obj L) ≅ tensorRight L ⋙ F :=
  NatIso.ofComponents (fun M => asIso (Functor.LaxMonoidal.μ F M L))
    (fun f => Functor.LaxMonoidal.μ_natural_left F f L)

/-- The actual tensor comparison, chosen frame, and right unitor. -/
def tensorRightFrameIso : tensorRight L ⋙ F ≅ F :=
  (tensorRightLaxCommIso F L).symm ≪≫
    Functor.isoWhiskerLeft F ((tensoringRight D).mapIso frame.symm) ≪≫
    Functor.isoWhiskerLeft F (rightUnitorNatIso D) ≪≫
    Functor.rightUnitor F

/-- The inverse inserts the specified frame before the genuine tensor
comparison; this fixes the normalization of the entire natural map. -/
theorem tensorRightFrameIso_inv_app (M : C) :
    (tensorRightFrameIso F L frame).inv.app M =
      (ρ_ (F.obj M)).inv ≫ (F.obj M ◁ frame.hom) ≫
        Functor.LaxMonoidal.μ F M L := by
  simp only [tensorRightFrameIso,tensorRightLaxCommIso,Iso.trans_inv,NatTrans.comp_app,
    Functor.rightUnitor_inv_app,Category.id_comp,Functor.isoWhiskerLeft_inv,
    Functor.mapIso_inv,Iso.symm_inv,
    rightUnitorNatIso_inv_app,NatIso.ofComponents_inv_app,asIso_hom,Iso.symm_inv,
    Category.assoc]
  rfl

end ToricPower

end
