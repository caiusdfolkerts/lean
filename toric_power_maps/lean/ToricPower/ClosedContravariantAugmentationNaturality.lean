module

public import ToricPower.ClosedContravariantAugmentation
public import ToricPower.ClosedContravariantCoefficient

/-! # Evaluation of the original closed-support coefficient augmentation

The actual finite support-proof biproduct comparison intertwines the
specified coefficient maps under every additive functor.  In particular
this applies to chart evaluation, without choosing new section maps.
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
  (D : Cᵒᵖ ⥤ B) (T : B)
  (components : ∀ (c : C), supported c → (D.obj (op c) ⟶ T))
  (compatible : ∀ {c d : C} (f : c ⟶ d) (h : supported d),
    D.map f.op ≫ components c (downward f h) = components d h)

local instance closedAugmentationNaturalityProofFintype (c : C) :
    Fintype (PLift (supported c)) := Fintype.ofFinite _

theorem closedContravariantAugmentation_map :
    Functor.whiskerRight
        (closedContravariantAugmentation supported downward D T components compatible) F ≫
        (Functor.constComp Cᵒᵖ T F).hom =
      (closedContravariantCoefficientIso supported downward F D).hom ≫
        closedContravariantAugmentation supported downward (D ⋙ F) (F.obj T)
          (fun c h => F.map (components c h))
          (fun f h => by
            change F.map (D.map f.op) ≫ F.map (components _ (downward f h)) =
              F.map (components _ h)
            rw [← CategoryTheory.Functor.map_comp,compatible]) := by
  apply NatTrans.ext
  funext c
  change F.map
      ((closedContravariantAugmentation supported downward D T components compatible).app c) ≫
        𝟙 (F.obj T) =
      (closedContravariantCoefficientTermIso supported downward F D c).hom ≫ _
  erw [Category.comp_id]
  apply (cancel_epi (closedContravariantCoefficientTermIso supported downward F D c).inv).mp
  erw [Iso.inv_hom_id_assoc]
  apply biproduct.hom_ext'
  intro h
  simp only [← Category.assoc,closedContravariantCoefficientTermIso,
    Functor.mapBiproduct_inv,biproduct.ι_desc]
  erw [← CategoryTheory.Functor.map_comp,closedContravariantAugmentation_inclusion]
  exact (closedContravariantAugmentation_inclusion supported downward (D ⋙ F) (F.obj T)
    (fun c h => F.map (components c h)) _ c.unop h.down).symm

end ToricPower.Cellular

end
