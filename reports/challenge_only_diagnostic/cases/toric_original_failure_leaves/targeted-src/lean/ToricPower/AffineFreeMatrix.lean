module

public import ToricPower.AffineFreeFrameComparison
public import ToricPower.FiniteFreeModuleDual

/-!
# Actual affine free-module matrix entries

The specified tilde frame carries the original inclusions and coordinate
projections to the corresponding unit-sheaf maps. This computes every
entry of an actual module map without changing its matrix.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Classical

namespace ToricPower

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

variable (R : CommRingCat.{0}) (I J : Type) [Fintype I] [Fintype J]

theorem finsuppModule_matrix
    (f : ModuleCat.of R (I →₀ R) ⟶ ModuleCat.of R (J →₀ R)) (i : I) (j : J) :
    ModuleCat.ofHom (Finsupp.lsingle i : R →ₗ[R] I →₀ R) ≫ f ≫
        ModuleCat.ofHom (Finsupp.lapply j : (J →₀ R) →ₗ[R] R) =
      f (Finsupp.single i 1) j • 𝟙 (ModuleCat.of R R) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change f (Finsupp.single i r) j = f (Finsupp.single i 1) j * r
  have scalar : Finsupp.single i r = r • Finsupp.single i (1 : R) := by simp
  rw [scalar, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]

@[reassoc]
theorem tildeFiniteFreeBiproductIso_ι_inv (i : I) :
    biproduct.ι (fun _ : I => SheafOfModules.unit (Spec R).ringCatSheaf) i ≫
        (tildeFiniteFreeBiproductIso R I).inv =
      (tildeSelf (R := R)).inv ≫
        tilde.map (ModuleCat.ofHom (Finsupp.lsingle i : R →ₗ[R] I →₀ R)) := by
  apply (cancel_mono (tildeFiniteFreeBiproductIso R I).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    tildeFiniteFreeBiproductIso_single]

@[reassoc]
theorem tildeFiniteFreeBiproductIso_projection (i : I) :
    (tildeFiniteFreeBiproductIso R I).hom ≫
        biproduct.π (fun _ : I => SheafOfModules.unit (Spec R).ringCatSheaf) i =
      tilde.map (ModuleCat.ofHom (Finsupp.lapply i : (I →₀ R) →ₗ[R] R)) ≫
        (tildeSelf (R := R)).hom := by
  apply (cancel_epi (tildeFiniteFreeBiproductIso R I).inv).mp
  apply biproduct.hom_ext'
  intro j
  rw [Iso.inv_hom_id_assoc, tildeFiniteFreeBiproductIso_ι_inv_assoc]
  change biproduct.ι (fun _ : I => SheafOfModules.unit (Spec R).ringCatSheaf) j ≫
      biproduct.π (fun _ : I => SheafOfModules.unit (Spec R).ringCatSheaf) i =
    (tildeSelf (R := R)).inv ≫
      (tilde.functor R).map (ModuleCat.ofHom (Finsupp.lsingle j : R →ₗ[R] I →₀ R)) ≫
      (tilde.functor R).map (ModuleCat.ofHom (Finsupp.lapply i : (I →₀ R) →ₗ[R] R)) ≫
      (tildeSelf (R := R)).hom
  rw [← Functor.map_comp_assoc]
  by_cases equal : j = i
  · subst j
    have identity :
        ModuleCat.ofHom (Finsupp.lsingle i : R →ₗ[R] I →₀ R) ≫
          ModuleCat.ofHom (Finsupp.lapply i : (I →₀ R) →ₗ[R] R) = 𝟙 _ := by
      apply ModuleCat.hom_ext
      ext r
      exact Finsupp.single_eq_same
    rw [identity, CategoryTheory.Functor.map_id]
    simp
  · have zero :
        ModuleCat.ofHom (Finsupp.lsingle j : R →ₗ[R] I →₀ R) ≫
          ModuleCat.ofHom (Finsupp.lapply i : (I →₀ R) →ₗ[R] R) = 0 := by
      apply ModuleCat.hom_ext
      ext r
      exact Finsupp.single_eq_of_ne (Ne.symm equal)
    rw [zero, Functor.map_zero]
    simp [equal, Ne.symm equal]

/-- The literal original matrix entry in the specified actual sheaf frame. -/
theorem tildeFiniteFreeBiproductIso_matrix
    (f : ModuleCat.of R (I →₀ R) ⟶ ModuleCat.of R (J →₀ R)) (i : I) (j : J) :
    biproduct.ι (fun _ : I => SheafOfModules.unit (Spec R).ringCatSheaf) i ≫
        (tildeFiniteFreeBiproductIso R I).inv ≫ tilde.map f ≫
        (tildeFiniteFreeBiproductIso R J).hom ≫
        biproduct.π (fun _ : J => SheafOfModules.unit (Spec R).ringCatSheaf) j =
      (tildeSelf (R := R)).inv ≫
        tilde.map (f (Finsupp.single i 1) j • 𝟙 (ModuleCat.of R R)) ≫
        (tildeSelf (R := R)).hom := by
  rw [tildeFiniteFreeBiproductIso_ι_inv_assoc,
    tildeFiniteFreeBiproductIso_projection]
  change (tildeSelf (R := R)).inv ≫
      (tilde.functor R).map (ModuleCat.ofHom (Finsupp.lsingle i : R →ₗ[R] I →₀ R)) ≫
      (tilde.functor R).map f ≫
      (tilde.functor R).map (ModuleCat.ofHom (Finsupp.lapply j : (J →₀ R) →ₗ[R] R)) ≫
      (tildeSelf (R := R)).hom = _
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
    Category.assoc, finsuppModule_matrix]
  rfl

end ToricPower
