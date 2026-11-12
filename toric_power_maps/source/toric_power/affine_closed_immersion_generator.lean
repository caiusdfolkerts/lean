module

public import ToricPower.AffineClosedImmersionUnit
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# A unit-valued generator becomes an isomorphism on a closed affine subscheme

For a quotient ring map, a map from the rank-one free source to the
restricted target ring becomes an isomorphism after scalar extension
precisely when its displayed generator is a unit. The result is then
transported through the actual affine tilde/pullback comparison.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct ChangeOfRings

namespace ToricPower

universe u

variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)

/-- The actual extension of the rank-one free source is the target ring. -/
def scalarExtensionSelfIso :
    (ModuleCat.extendScalars φ).obj (ModuleCat.of R R) ≅ ModuleCat.of S S := by
  letI : Algebra R S := φ.toAlgebra
  exact (TensorProduct.AlgebraTensorModule.rid R S S).toModuleIso

/-- The canonical frame retains the original tensor generator. -/
theorem scalarExtensionSelfIso_tmul (s : S) (r : R) :
    (scalarExtensionSelfIso φ).hom (s ⊗ₜ[R,φ] r) = φ r * s := by
  letI : Algebra R S := φ.toAlgebra
  change TensorProduct.AlgebraTensorModule.rid R S S (s ⊗ₜ[R] r) = φ r * s
  rw [TensorProduct.AlgebraTensorModule.rid_tmul]
  rfl

/-- The original scalar-extension map is invertible when its one
displayed generator is a unit and the ring map is surjective. -/
theorem extendScalars_generator_isIso (surjective : Function.Surjective φ)
    (f : ModuleCat.of R R ⟶ (ModuleCat.restrictScalars φ).obj (ModuleCat.of S S))
    (unit : @IsUnit S _ (f 1)) :
    IsIso ((ModuleCat.extendScalars φ).map f) := by
  obtain ⟨a, generator⟩ := unit
  let e : (ModuleCat.extendScalars φ).obj (ModuleCat.of R R) ≅ ModuleCat.of S S :=
    scalarExtensionSelfIso φ ≪≫ (LinearEquiv.smulOfUnit (M := S) a).toModuleIso
  have mate : ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).symm f = e.hom := by
    apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
    rw [Equiv.apply_symm_apply]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    rw [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply]
    change f r = (LinearEquiv.smulOfUnit (M := S) a)
      ((scalarExtensionSelfIso φ).hom ((1 : S) ⊗ₜ[R,φ] r))
    rw [scalarExtensionSelfIso_tmul, mul_one]
    change f r = (a : S) * φ r
    have linear := f.hom.map_smul r (1 : R)
    rw [ModuleCat.restrictScalars.smul_def] at linear
    simpa only [smul_eq_mul, mul_one, ← generator, mul_comm] using linear
  haveI : IsIso (((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).symm f) := by
    rw [mate]
    infer_instance
  haveI := surjectiveScalarCounit_isIso φ surjective (ModuleCat.of S S)
  haveI : IsIso ((ModuleCat.extendScalars φ).map f ≫
      (ModuleCat.extendRestrictScalarsAdj φ).counit.app (ModuleCat.of S S)) := by
    have equation := (ModuleCat.extendRestrictScalarsAdj φ).homEquiv_counit
      (ModuleCat.of R R) (ModuleCat.of S S) f
    exact equation ▸ (inferInstance :
      IsIso (((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).symm f))
  exact IsIso.of_isIso_comp_right _
    ((ModuleCat.extendRestrictScalarsAdj φ).counit.app (ModuleCat.of S S))

variable {R' S' : CommRingCat.{u}} (ψ : R' ⟶ S')

/-- The same statement concerns the actual geometric pullback of the
actual affine sheaf map, through the canonical natural tilde comparison. -/
theorem affineClosedImmersion_generator_isIso (surjective : Function.Surjective ψ)
    (f : ModuleCat.of R' R' ⟶
      (ModuleCat.restrictScalars ψ.hom).obj (ModuleCat.of S' S'))
    (unit : @IsUnit S' _ (f 1)) :
    IsIso ((Scheme.Modules.pullback (Spec.map ψ)).map (tilde.map f)) := by
  letI := extendScalars_generator_isIso ψ.hom surjective f unit
  change IsIso ((tilde.functor R' ⋙ Scheme.Modules.pullback (Spec.map ψ)).map f)
  apply (NatIso.isIso_map_iff
    (TauCeti.AlgebraicGeometry.tildeFunctorCompPullbackIso ψ) f).mpr
  change IsIso ((tilde.functor S').map ((ModuleCat.extendScalars ψ.hom).map f))
  infer_instance

end ToricPower

end
