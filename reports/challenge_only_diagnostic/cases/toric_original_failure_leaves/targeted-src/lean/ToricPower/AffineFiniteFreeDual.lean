module

public import ToricPower.AffineFreeMatrix
public import ToricPower.InternalDualUnitFrames
public import ToricPower.SchemeInternalDual

/-!
# Tilde and the actual dual of finite free modules

The isomorphism is constructed in the literal finite free basis. Its
naturality theorem compares the original linear-Hom map with the actual
sheaf internal-Hom map on every matrix entry. No monoidal structure on
tilde, or exactness of dualization, is postulated.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped Classical

namespace ToricPower

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

variable (R : CommRingCat.{0}) (I J : Type) [Fintype I] [Fintype J]

theorem finiteFreeModuleDualEquiv_symm_single (j : I) :
    (finiteFreeModuleDualEquiv R I).symm (Finsupp.single j 1) =
      ModuleCat.ofHom (Finsupp.lapply j : (I →₀ R) →ₗ[R] R) := by
  apply (finiteFreeModuleDualEquiv R I).injective
  rw [LinearEquiv.apply_symm_apply]
  ext i
  change Finsupp.single j (1 : R) i = Finsupp.single i (1 : R) j
  simp only [Finsupp.single_apply]
  by_cases equal : i = j
  · subst j; simp
  · simp [equal, Ne.symm equal]

theorem finiteFreeModuleDualTranspose_coefficient
    (f : ModuleCat.of R (I →₀ R) ⟶ ModuleCat.of R (J →₀ R)) (i : I) (j : J) :
    finiteFreeModuleDualEquiv R I
        ((moduleDual R).map f.op
          ((finiteFreeModuleDualEquiv R J).symm (Finsupp.single j 1))) i =
      f (Finsupp.single i 1) j := by
  rw [finiteFreeModuleDualEquiv_apply, finiteFreeModuleDualEquiv_symm_single]
  rfl

def affineInternalDualCoordinates :
    (internalDual (Spec R).Modules).obj (op (tilde (ModuleCat.of R (I →₀ R)))) ≅
      ⨁ (fun _ : I => SheafOfModules.unit (Spec R).ringCatSheaf) :=
  internalDualInUnitFrames (tildeFiniteFreeBiproductIso R I).symm

def affineModuleDualCoordinates :
    tilde ((moduleDual R).obj (op (ModuleCat.of R (I →₀ R)))) ≅
      ⨁ (fun _ : I => SheafOfModules.unit (Spec R).ringCatSheaf) :=
  (tilde.functor R).mapIso (finiteFreeModuleDualEquiv R I).toModuleIso ≪≫
    tildeFiniteFreeBiproductIso R I

/-- The actual sheaf internal dual agrees with the tilde of the actual
linear module dual in the complete finite free basis. -/
def affineFiniteFreeDualIso :
    tilde ((moduleDual R).obj (op (ModuleCat.of R (I →₀ R)))) ≅
      (internalDual (Spec R).Modules).obj (op (tilde (ModuleCat.of R (I →₀ R)))) :=
  affineModuleDualCoordinates R I ≪≫ (affineInternalDualCoordinates R I).symm

theorem affineInternalDualCoordinates_matrix
    (f : ModuleCat.of R (I →₀ R) ⟶ ModuleCat.of R (J →₀ R)) (i : I) (j : J) :
    biproduct.ι (fun _ : J => SheafOfModules.unit (Spec R).ringCatSheaf) j ≫
        (affineInternalDualCoordinates R J).inv ≫
        (internalDual (Spec R).Modules).map (tilde.map f).op ≫
        (affineInternalDualCoordinates R I).hom ≫
        biproduct.π (fun _ : I => SheafOfModules.unit (Spec R).ringCatSheaf) i =
      biproduct.ι (fun _ : I => SheafOfModules.unit (Spec R).ringCatSheaf) i ≫
        (tildeFiniteFreeBiproductIso R I).inv ≫ tilde.map f ≫
        (tildeFiniteFreeBiproductIso R J).hom ≫
        biproduct.π (fun _ : J => SheafOfModules.unit (Spec R).ringCatSheaf) j :=
  internalDualInUnitFrames_matrix (tildeFiniteFreeBiproductIso R I).symm
    (tildeFiniteFreeBiproductIso R J).symm (tilde.map f) i j

theorem affineModuleDualCoordinates_matrix
    (f : ModuleCat.of R (I →₀ R) ⟶ ModuleCat.of R (J →₀ R)) (i : I) (j : J) :
    biproduct.ι (fun _ : J => SheafOfModules.unit (Spec R).ringCatSheaf) j ≫
        (affineModuleDualCoordinates R J).inv ≫
        (tilde.functor R).map ((moduleDual R).map f.op) ≫
        (affineModuleDualCoordinates R I).hom ≫
        biproduct.π (fun _ : I => SheafOfModules.unit (Spec R).ringCatSheaf) i =
      biproduct.ι (fun _ : I => SheafOfModules.unit (Spec R).ringCatSheaf) i ≫
        (tildeFiniteFreeBiproductIso R I).inv ≫ tilde.map f ≫
        (tildeFiniteFreeBiproductIso R J).hom ≫
        biproduct.π (fun _ : J => SheafOfModules.unit (Spec R).ringCatSheaf) j := by
  simp only [affineModuleDualCoordinates, Iso.trans_inv, Iso.trans_hom,
    Functor.mapIso_inv, Functor.mapIso_hom, Category.assoc, ← Functor.map_comp_assoc]
  change biproduct.ι (fun _ : J => SheafOfModules.unit (Spec R).ringCatSheaf) j ≫
    (tildeFiniteFreeBiproductIso R J).inv ≫
    tilde.map ((finiteFreeModuleDualEquiv R J).toModuleIso.inv ≫
      (moduleDual R).map f.op ≫ (finiteFreeModuleDualEquiv R I).toModuleIso.hom) ≫
    (tildeFiniteFreeBiproductIso R I).hom ≫
    biproduct.π (fun _ : I => SheafOfModules.unit (Spec R).ringCatSheaf) i = _
  rw [tildeFiniteFreeBiproductIso_matrix, tildeFiniteFreeBiproductIso_matrix]
  congr 2
  exact congrArg (fun r : R => tilde.map (r • 𝟙 (ModuleCat.of R R)))
    (finiteFreeModuleDualTranspose_coefficient R I J f i j)

/-- Full naturality for every actual matrix, before passing to
complexes, homology, or derived categories. -/
theorem affineFiniteFreeDualIso_naturality
    (f : ModuleCat.of R (I →₀ R) ⟶ ModuleCat.of R (J →₀ R)) :
    (tilde.functor R).map ((moduleDual R).map f.op) ≫
        (affineFiniteFreeDualIso R I).hom =
      (affineFiniteFreeDualIso R J).hom ≫
        (internalDual (Spec R).Modules).map (tilde.map f).op := by
  apply (cancel_epi (affineModuleDualCoordinates R J).inv).mp
  apply (cancel_mono (affineInternalDualCoordinates R I).hom).mp
  apply biproduct.hom_ext'
  intro j
  apply biproduct.hom_ext
  intro i
  simp only [affineFiniteFreeDualIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rw [affineModuleDualCoordinates_matrix, affineInternalDualCoordinates_matrix]

end ToricPower
