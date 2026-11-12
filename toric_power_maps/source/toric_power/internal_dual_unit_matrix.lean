module

public import ToricPower.InternalDualBiproduct

/-!
# Scalar matrices of the actual internal dual

Under the canonical unit pairing a unit endomorphism is its own transpose.
Consequently finite matrices in unit frames are transposed literally.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed Opposite

namespace ToricPower

universe u v w

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
  [Preadditive C] [MonoidalPreadditive C] [HasFiniteBiproducts C]

def internalDualUnitIso : (internalDual C).obj (op (𝟙_ C)) ≅ 𝟙_ C :=
  TauCeti.ihomUnitIso (𝟙_ C) (𝟙_ C)

/-- The canonical unit pairing transposes an actual scalar to itself. -/
theorem internalDualUnitIso_inv_map (f : 𝟙_ C ⟶ 𝟙_ C) :
    (internalDualUnitIso C).inv ≫ (internalDual C).map f.op =
      f ≫ (internalDualUnitIso C).inv := by
  change (TauCeti.ihomUnitIso (𝟙_ C) (𝟙_ C)).inv ≫ (pre f).app (𝟙_ C) =
    f ≫ (TauCeti.ihomUnitIso (𝟙_ C) (𝟙_ C)).inv
  apply uncurry_injective
  rw [uncurry_pre_app, uncurry_natural_left]
  rw [TauCeti.ihomUnitIso_inv, uncurry_curry,
    TauCeti.ExactPairing.unit_evaluation]
  rw [rightUnitor_naturality, ← unitors_equal, leftUnitor_naturality]

theorem internalDualUnitIso_matrix (f : 𝟙_ C ⟶ 𝟙_ C) :
    (internalDualUnitIso C).inv ≫ (internalDual C).map f.op ≫
        (internalDualUnitIso C).hom = f := by
  rw [← Category.assoc, internalDualUnitIso_inv_map, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

variable (I J : Type w) [Fintype I] [Fintype J]

def internalDualUnitBiproductIso :
    (internalDual C).obj (op (⨁ (fun _ : I => 𝟙_ C))) ≅
      ⨁ (fun _ : I => 𝟙_ C) :=
  internalDualBiproductIso (fun _ : I => 𝟙_ C) ≪≫
    biproduct.mapIso (fun _ : I => internalDualUnitIso C)

@[reassoc]
theorem internalDualUnitBiproductIso_hom_π (i : I) :
    (internalDualUnitBiproductIso C I).hom ≫ biproduct.π (fun _ : I => 𝟙_ C) i =
      (internalDual C).map (biproduct.ι (fun _ : I => 𝟙_ C) i).op ≫
        (internalDualUnitIso C).hom := by
  change ((internalDualBiproductIso (fun _ : I => 𝟙_ C)).hom ≫
      biproduct.map (fun _ : I => (internalDualUnitIso C).hom)) ≫
        biproduct.π (fun _ : I => 𝟙_ C) i = _
  rw [Category.assoc, biproduct.map_π, internalDualBiproductIso_hom_π_assoc]

@[reassoc]
theorem internalDualUnitBiproductIso_ι_inv (i : I) :
    biproduct.ι (fun _ : I => 𝟙_ C) i ≫ (internalDualUnitBiproductIso C I).inv =
      (internalDualUnitIso C).inv ≫
        (internalDual C).map (biproduct.π (fun _ : I => 𝟙_ C) i).op := by
  change biproduct.ι (fun _ : I => 𝟙_ C) i ≫
      biproduct.map (fun _ : I => (internalDualUnitIso C).inv) ≫
        (internalDualBiproductIso (fun _ : I => 𝟙_ C)).inv = _
  rw [biproduct.ι_map_assoc, internalDualBiproductIso_ι_inv]

/-- The actual dual map has the literal opposite matrix coefficient. -/
theorem internalDualUnitBiproductIso_matrix
    (f : (⨁ (fun _ : I => 𝟙_ C)) ⟶ ⨁ (fun _ : J => 𝟙_ C)) (i : I) (j : J) :
    biproduct.ι (fun _ : J => 𝟙_ C) j ≫
        (internalDualUnitBiproductIso C J).inv ≫ (internalDual C).map f.op ≫
        (internalDualUnitBiproductIso C I).hom ≫
        biproduct.π (fun _ : I => 𝟙_ C) i =
      biproduct.ι (fun _ : I => 𝟙_ C) i ≫ f ≫
        biproduct.π (fun _ : J => 𝟙_ C) j := by
  rw [internalDualUnitBiproductIso_ι_inv_assoc,
    internalDualUnitBiproductIso_hom_π]
  have scalar := internalDualUnitIso_matrix C
    (biproduct.ι (fun _ : I => 𝟙_ C) i ≫ f ≫ biproduct.π (fun _ : J => 𝟙_ C) j)
  simpa only [op_comp, Functor.map_comp, Category.assoc] using scalar

end ToricPower
