module

public import ToricPower.AffineFreeDualFrameGenerators

/-!
# The original free dual generator as an actual sheaf map

The canonical finite-free dual coordinates turn a basis inclusion into
an actual linear functional. Affine sheafification and the genuine
internal-dual comparison preserve this specified generator map.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped Classical

namespace ToricPower

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

variable (R : CommRingCat.{0}) (I : Type) [Fintype I] (i : I)

/-- The same-index functional in the original finite free dual. -/
def finiteFreeDualGeneratorMap :
    ModuleCat.of R R ⟶ (moduleDual R).obj (op (ModuleCat.of R (I →₀ R))) :=
  ModuleCat.ofHom ((finiteFreeModuleDualEquiv R I).symm.toLinearMap.comp
    (Finsupp.lsingle i : R →ₗ[R] I →₀ R))

@[reassoc]
theorem finiteFreeDualGeneratorMap_coordinates :
    finiteFreeDualGeneratorMap R I i ≫ (finiteFreeModuleDualEquiv R I).toModuleIso.hom =
      ModuleCat.ofHom (Finsupp.lsingle i : R →ₗ[R] I →₀ R) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  exact (finiteFreeModuleDualEquiv R I).apply_symm_apply (Finsupp.single i r)

/-- The actual tilde map is the original same-index inverse-cell
generator in the canonical affine internal-dual frame. -/
@[reassoc]
theorem finiteFreeDualGeneratorMap_tilde :
    (tildeSelf (R := R)).inv ≫ tilde.map (finiteFreeDualGeneratorMap R I i) ≫
        (affineFiniteFreeDualIso R I).hom =
      biproduct.ι (fun _ : I => SheafOfModules.unit (Spec R).ringCatSheaf) i ≫
        (affineInternalDualCoordinates R I).inv := by
  apply (cancel_mono (affineInternalDualCoordinates R I).hom).mp
  simp only [affineFiniteFreeDualIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [affineModuleDualCoordinates, Iso.trans_hom, Functor.mapIso_hom,
    Category.assoc]
  change (tildeSelf (R := R)).inv ≫
      (tilde.functor R).map (finiteFreeDualGeneratorMap R I i) ≫
      (tilde.functor R).map (finiteFreeModuleDualEquiv R I).toModuleIso.hom ≫
      (tildeFiniteFreeBiproductIso R I).hom = _
  rw [← Functor.map_comp_assoc, finiteFreeDualGeneratorMap_coordinates]
  exact tildeFiniteFreeBiproductIso_single R I i

end ToricPower

end
