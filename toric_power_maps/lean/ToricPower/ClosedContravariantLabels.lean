module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Contravariant labels on a genuinely closed cell support

The support is a downward closed predicate. At each cell the coefficient
is the finite biproduct indexed by its literal support proof. Every face
map and every coefficient transformation is retained.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Classical

namespace ToricPower.Cellular

universe u v w z

variable {C : Type u} [Category.{v} C]
  {B : Type w} [Category.{z} B] [Preadditive B] [HasFiniteBiproducts B]
  (supported : C → Prop)
  (downward : ∀ {c d : C}, (c ⟶ d) → supported d → supported c)

local instance closedLabelsProofFinite (c : C) : Fintype (PLift (supported c)) :=
  Fintype.ofFinite _

def closedContravariantLabels (D : Cᵒᵖ ⥤ B) : Cᵒᵖ ⥤ B where
  obj c := ⨁ fun _ : PLift (supported c.unop) => D.obj c
  map {c d} f := biproduct.desc (fun h : PLift (supported c.unop) =>
    D.map f ≫ biproduct.ι (fun _ : PLift (supported d.unop) => D.obj d)
      ⟨downward f.unop h.down⟩)
  map_id c := by
    apply biproduct.hom_ext'
    intro h
    simp only [biproduct.ι_desc,CategoryTheory.Functor.map_id,Category.id_comp,
      Category.comp_id]
  map_comp {c d e} f g := by
    apply biproduct.hom_ext'
    intro h
    simp only [biproduct.ι_desc,CategoryTheory.Functor.map_comp,Category.assoc,
      biproduct.ι_desc_assoc]

@[reassoc]
theorem closedContravariantLabels_map_inclusion (D : Cᵒᵖ ⥤ B)
    {c d : Cᵒᵖ} (f : c ⟶ d) (h : PLift (supported c.unop)) :
    biproduct.ι (fun _ : PLift (supported c.unop) => D.obj c) h ≫
        (closedContravariantLabels supported downward D).map f =
      D.map f ≫ biproduct.ι (fun _ : PLift (supported d.unop) => D.obj d)
        ⟨downward f.unop h.down⟩ := by
  exact biproduct.ι_desc _ _

def closedContravariantLabelsMap {D E : Cᵒᵖ ⥤ B} (α : D ⟶ E) :
    closedContravariantLabels supported downward D ⟶
      closedContravariantLabels supported downward E where
  app c := biproduct.map (fun _ : PLift (supported c.unop) => α.app c)
  naturality {c d} f := by
    apply biproduct.hom_ext'
    intro h
    simp only [← Category.assoc,closedContravariantLabels_map_inclusion,
      biproduct.ι_map]
    simp only [Category.assoc,biproduct.ι_map,closedContravariantLabels_map_inclusion]
    simpa only [Category.assoc] using congrArg (fun t => t ≫ biproduct.ι
      (fun _ : PLift (supported d.unop) => E.obj d)
        ⟨downward f.unop h.down⟩) (α.naturality f)

def closedContravariantLabelEndofunctor : (Cᵒᵖ ⥤ B) ⥤ (Cᵒᵖ ⥤ B) where
  obj := closedContravariantLabels supported downward
  map := closedContravariantLabelsMap supported downward
  map_id D := by
    apply NatTrans.ext
    funext c
    apply biproduct.hom_ext'
    intro h
    change biproduct.ι _ h ≫ biproduct.map (fun _ : PLift (supported c.unop) =>
      𝟙 (D.obj c)) = biproduct.ι (fun _ : PLift (supported c.unop) => D.obj c) h ≫ 𝟙 _
    simp only [biproduct.ι_map,Category.id_comp,Category.comp_id]
  map_comp α β := by
    apply NatTrans.ext
    funext c
    apply biproduct.hom_ext'
    intro h
    simp only [closedContravariantLabelsMap,NatTrans.comp_app,biproduct.ι_map,
      Category.assoc,biproduct.ι_map_assoc]

instance closedContravariantLabelEndofunctor_additive :
    (closedContravariantLabelEndofunctor (B := B) supported downward).Additive where
  map_add {D E α β} := by
    apply NatTrans.ext
    funext c
    apply biproduct.hom_ext'
    intro h
    simp only [closedContravariantLabelEndofunctor,closedContravariantLabelsMap,
      NatTrans.app_add,biproduct.ι_map,Preadditive.comp_add,Preadditive.add_comp]

end ToricPower.Cellular

end
