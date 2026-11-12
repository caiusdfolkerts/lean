module

public import ToricPower.ClosedContravariantLabels

/-! # Augmentations of actual closed-support coefficient diagrams

The maps are specified on the original coefficients at supported cells.
Their compatibility on every incidence determines a genuine natural
transformation, including the zero coefficients off the closed support.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Classical

namespace ToricPower.Cellular

universe u v w z

variable {C : Type u} [Category.{v} C]
  {B : Type w} [Category.{z} B] [Preadditive B] [HasFiniteBiproducts B]
  (supported : C → Prop)
  (downward : ∀ {c d : C}, (c ⟶ d) → supported d → supported c)
  (D : Cᵒᵖ ⥤ B) (T : B)
  (components : ∀ (c : C), supported c → (D.obj (op c) ⟶ T))
  (compatible : ∀ {c d : C} (f : c ⟶ d) (h : supported d),
    D.map f.op ≫ components c (downward f h) = components d h)

local instance closedAugmentationProofFintype (c : C) : Fintype (PLift (supported c)) :=
  Fintype.ofFinite _

def closedContravariantAugmentation :
    closedContravariantLabels supported downward D ⟶ (Functor.const Cᵒᵖ).obj T where
  app c := biproduct.desc (fun h : PLift (supported c.unop) => components c.unop h.down)
  naturality {c d} f := by
    change (biproduct.desc (fun h : PLift (supported c.unop) =>
          D.map f ≫ biproduct.ι
            (fun _ : PLift (supported d.unop) => D.obj d) ⟨downward f.unop h.down⟩)) ≫
        biproduct.desc (fun h : PLift (supported d.unop) => components d.unop h.down) =
      biproduct.desc (fun h : PLift (supported c.unop) => components c.unop h.down) ≫ 𝟙 T
    apply biproduct.hom_ext'
    intro h
    simp only [biproduct.ι_desc_assoc,biproduct.ι_desc,Category.assoc,Category.comp_id]
    exact compatible f.unop h.down

@[reassoc]
theorem closedContravariantAugmentation_inclusion (c : C) (h : supported c) :
    biproduct.ι (fun _ : PLift (supported c) => D.obj (op c)) ⟨h⟩ ≫
      (closedContravariantAugmentation supported downward D T components compatible).app (op c) =
        components c h := biproduct.ι_desc _ _

end ToricPower.Cellular

end
