module

public import ToricPower.ClosedContravariantLabels

/-! # Exact coefficient functors on closed inverse-label sums

An additive coefficient functor carries the literal finite supported
biproducts to the same supported biproducts of its values. The comparison
keeps both the original face maps and every coefficient transformation.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Classical

namespace ToricPower.Cellular

universe u v w z x y

variable {C : Type u} [Category.{v} C]
  {B : Type w} [Category.{z} B] [Preadditive B] [HasFiniteBiproducts B]
  {E : Type x} [Category.{y} E] [Preadditive E] [HasFiniteBiproducts E]
  (supported : C → Prop)
  (downward : ∀ {c d : C}, (c ⟶ d) → supported d → supported c)
  (F : B ⥤ E) [F.Additive]

local instance closedCoefficientProofFinite (c : C) : Fintype (PLift (supported c)) :=
  Fintype.ofFinite _

def closedContravariantCoefficientTermIso (D : Cᵒᵖ ⥤ B) (c : Cᵒᵖ) :
    F.obj ((closedContravariantLabels supported downward D).obj c) ≅
      (closedContravariantLabels supported downward (D ⋙ F)).obj c :=
  F.mapBiproduct (fun _ : PLift (supported c.unop) => D.obj c)

@[reassoc]
theorem closedContravariantCoefficientTermIso_inclusion (D : Cᵒᵖ ⥤ B)
    (c : Cᵒᵖ) (h : PLift (supported c.unop)) :
    F.map (biproduct.ι (fun _ : PLift (supported c.unop) => D.obj c) h) ≫
      (closedContravariantCoefficientTermIso supported downward F D c).hom =
      biproduct.ι (fun _ : PLift (supported c.unop) => F.obj (D.obj c)) h := by
  apply (cancel_mono (closedContravariantCoefficientTermIso supported downward F D c).inv).mp
  rw [Category.assoc,Iso.hom_inv_id,Category.comp_id]
  simp only [closedContravariantCoefficientTermIso,Functor.mapBiproduct_inv,biproduct.ι_desc]

def closedContravariantCoefficientIso (D : Cᵒᵖ ⥤ B) :
    closedContravariantLabels supported downward D ⋙ F ≅
      closedContravariantLabels supported downward (D ⋙ F) :=
  NatIso.ofComponents (closedContravariantCoefficientTermIso supported downward F D)
    (by
      intro c d f
      apply (cancel_epi (closedContravariantCoefficientTermIso supported downward F D c).inv).mp
      rw [Iso.inv_hom_id_assoc]
      apply biproduct.hom_ext'
      intro h
      simp only [Functor.comp_map,Functor.comp_obj,← Category.assoc,closedContravariantCoefficientTermIso,
        Functor.mapBiproduct_inv,biproduct.ι_desc]
      rw [← F.map_comp,closedContravariantLabels_map_inclusion,F.map_comp,Category.assoc]
      exact (congrArg (fun t => F.map (D.map f) ≫ t)
        (closedContravariantCoefficientTermIso_inclusion supported downward F D d
          ⟨downward f.unop h.down⟩)).trans
        (closedContravariantLabels_map_inclusion supported downward (D ⋙ F) f h).symm)

@[reassoc]
theorem closedContravariantCoefficientIso_naturality {D E : Cᵒᵖ ⥤ B}
    (α : D ⟶ E) :
    Functor.whiskerRight (closedContravariantLabelsMap supported downward α) F ≫
      (closedContravariantCoefficientIso supported downward F E).hom =
    (closedContravariantCoefficientIso supported downward F D).hom ≫
      closedContravariantLabelsMap supported downward (Functor.whiskerRight α F) := by
  apply NatTrans.ext
  funext c
  apply (cancel_epi (closedContravariantCoefficientTermIso supported downward F D c).inv).mp
  change (closedContravariantCoefficientTermIso supported downward F D c).inv ≫
      F.map (biproduct.map (fun _ : PLift (supported c.unop) => α.app c)) ≫
      (closedContravariantCoefficientTermIso supported downward F E c).hom =
    (closedContravariantCoefficientTermIso supported downward F D c).inv ≫
      (closedContravariantCoefficientTermIso supported downward F D c).hom ≫
      biproduct.map (fun _ : PLift (supported c.unop) => F.map (α.app c))
  rw [Iso.inv_hom_id_assoc]
  apply biproduct.hom_ext'
  intro h
  simp only [Functor.comp_obj,← Category.assoc,closedContravariantCoefficientTermIso,
    Functor.mapBiproduct_inv,biproduct.ι_desc]
  rw [← F.map_comp,biproduct.ι_map,F.map_comp,Category.assoc]
  rw [biproduct.ι_map]
  exact congrArg (fun t => F.map (α.app c) ≫ t)
    (closedContravariantCoefficientTermIso_inclusion supported downward F E c h)

def closedContravariantCoefficientFunctorIso :
    closedContravariantLabelEndofunctor supported downward ⋙
      (Functor.whiskeringRight Cᵒᵖ B E).obj F ≅
    (Functor.whiskeringRight Cᵒᵖ B E).obj F ⋙
      closedContravariantLabelEndofunctor supported downward :=
  NatIso.ofComponents (closedContravariantCoefficientIso supported downward F)
    (fun α => closedContravariantCoefficientIso_naturality supported downward F α)

end ToricPower.Cellular

end

