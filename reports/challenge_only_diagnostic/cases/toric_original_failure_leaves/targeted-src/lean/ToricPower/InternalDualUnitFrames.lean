module

public import ToricPower.InternalDualUnitMatrix

/-!
# Internal dual maps in specified finite unit frames

The original frame is dualized canonically. Every original map then has
its actual transposed matrix in these frames.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace ToricPower

universe u v w

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
  [Preadditive C] [MonoidalPreadditive C] [HasFiniteBiproducts C]
  {I J : Type w} [Fintype I] [Fintype J] {M N : C}
  (e : (⨁ (fun _ : I => 𝟙_ C)) ≅ M) (f : (⨁ (fun _ : J => 𝟙_ C)) ≅ N)

def internalDualInUnitFrames :
    (internalDual C).obj (op M) ≅ ⨁ (fun _ : I => 𝟙_ C) :=
  (internalDual C).mapIso e.op ≪≫ internalDualUnitBiproductIso C I

theorem internalDualInUnitFrames_matrix (g : M ⟶ N) (i : I) (j : J) :
    biproduct.ι (fun _ : J => 𝟙_ C) j ≫
        (internalDualInUnitFrames f).inv ≫ (internalDual C).map g.op ≫
        (internalDualInUnitFrames e).hom ≫ biproduct.π (fun _ : I => 𝟙_ C) i =
      biproduct.ι (fun _ : I => 𝟙_ C) i ≫ e.hom ≫ g ≫ f.inv ≫
        biproduct.π (fun _ : J => 𝟙_ C) j := by
  have matrix := internalDualUnitBiproductIso_matrix C I J (e.hom ≫ g ≫ f.inv) i j
  simpa only [internalDualInUnitFrames, Iso.trans_inv, Iso.trans_hom,
    Functor.mapIso_inv, Functor.mapIso_hom, Iso.op_hom, Iso.op_inv,
    op_comp, Functor.map_comp, Category.assoc] using matrix

end ToricPower
