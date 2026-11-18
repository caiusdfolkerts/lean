module

public import ToricPower.AffineFiniteFreeDual
public import ToricPower.AffineFreeFrameComparison

/-!
# Original cell generators in canonical affine dual frames

An actual chosen frame for every finite-sum label determines the dual
frame. The comparison below retains the duals of the original
projections, and identifies them with the original free-dual basis.
No coefficient map or orientation is replaced by a chosen isomorphism.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace ToricPower

universe u v

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

variable (R : CommRingCat.{0}) (I : Type) [Fintype I]
  {C : Type u} [Category.{v} C] [Preadditive C]
  (P : C ⥤ (Spec R).Modules) [P.PreservesZeroMorphisms]
  (L : I → C) [HasBiproduct L] [PreservesBiproduct L P]
  (frame : ∀ i, SheafOfModules.unit (Spec R).ringCatSheaf ≅ P.obj (L i))

/-- The specified total frame has exactly the original coordinate
projections, followed by the specified individual frames. -/
@[reassoc]
theorem affineFreeFrameComparison_projection (i : I) :
    (affineFreeFrameComparison R I P L frame).hom ≫ P.map (biproduct.π L i) =
      (tildeFiniteFreeBiproductIso R I).hom ≫
        biproduct.π (fun _ : I => SheafOfModules.unit (Spec R).ringCatSheaf) i ≫
          (frame i).hom := by
  have projection : (P.mapBiproduct L).hom ≫
      biproduct.π (fun j => P.obj (L j)) i = P.map (biproduct.π L i) :=
    biproduct.lift_π _ _
  rw [← projection]
  simp only [affineFreeFrameComparison, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc, biproduct.mapIso_hom, biproduct.map_π]

/-- In the actual affine free-dual coordinates, the original projection
is the corresponding original basis inclusion. -/
@[reassoc]
theorem affineInternalDualCoordinates_dual_projection (i : I) :
    (internalDualUnitIso (Spec R).Modules).inv ≫
      (internalDual (Spec R).Modules).map
        ((tildeFiniteFreeBiproductIso R I).hom ≫
          biproduct.π (fun _ : I => SheafOfModules.unit (Spec R).ringCatSheaf) i).op =
      biproduct.ι (fun _ : I => SheafOfModules.unit (Spec R).ringCatSheaf) i ≫
        (affineInternalDualCoordinates R I).inv := by
  change (internalDualUnitIso (Spec R).Modules).inv ≫
      (internalDual (Spec R).Modules).map
        ((tildeFiniteFreeBiproductIso R I).hom ≫
          biproduct.π (fun _ : I => 𝟙_ (Spec R).Modules) i).op =
      biproduct.ι (fun _ : I => 𝟙_ (Spec R).Modules) i ≫
        (affineInternalDualCoordinates R I).inv
  simp only [affineInternalDualCoordinates, internalDualInUnitFrames,
    Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv, Iso.symm_inv, Category.assoc,
    internalDualUnitBiproductIso_ι_inv_assoc, op_comp, Functor.map_comp]

end ToricPower

end
