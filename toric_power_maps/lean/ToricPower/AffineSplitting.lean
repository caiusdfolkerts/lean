module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.CategoryTheory.Retract

/-! # Affine direct image and actual module splittings

The comparison below identifies ordinary sheaf direct image along `Spec φ`
with restriction of scalars of the underlying module. Its proof uses the
actual tilde–global-sections adjunction. A split module inclusion therefore
gives a split inclusion of the actual affine structure sheaf.

This is a development source until its ordinary compiler record succeeds.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ToricPower

universe u

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- The literal sections of an affine direct image, with their scalar action. -/
def affinePushforwardSectionsIso :
    Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R) ≅
      moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom :=
  Functor.isoWhiskerRight (pushforwardCompModulesSpecToSheafIso φ)
    (TopCat.Sheaf.forget _ _ ⋙ (evaluation _ _).obj (.op ⊤))

@[simp]
theorem affinePushforwardSectionsIso_hom_apply (N : (Spec S).Modules)
    (x : (moduleSpecΓFunctor (R := R)).obj
      ((Scheme.Modules.pushforward (Spec.map φ)).obj N)) :
    ((affinePushforwardSectionsIso φ).hom.app N).hom x = x := rfl

@[simp]
theorem affinePushforwardSectionsIso_inv_apply (N : (Spec S).Modules)
    (x : (ModuleCat.restrictScalars φ.hom).obj
      ((moduleSpecΓFunctor (R := S)).obj N)) :
    ((affinePushforwardSectionsIso φ).inv.app N).hom x = x := rfl

/-- Direct image of an associated sheaf is the associated sheaf of the
restricted module. No exactness or projection formula is assumed here. -/
def affinePushforwardTildeIso (M : ModuleCat.{u} S) :
    (Scheme.Modules.pushforward (Spec.map φ)).obj (tilde M) ≅
      tilde ((ModuleCat.restrictScalars φ.hom).obj M) := by
  letI : IsIso (tilde M).fromTildeΓ := isIso_fromTildeΓ_iff.mpr ⟨M, ⟨Iso.refl _⟩⟩
  letI : IsIso ((Scheme.Modules.pushforward (Spec.map φ)).obj (tilde M)).fromTildeΓ :=
    isIso_fromTildeΓ_pushforward φ (tilde M)
  exact (asIso ((Scheme.Modules.pushforward (Spec.map φ)).obj (tilde M)).fromTildeΓ).symm ≪≫
    (tilde.functor R).mapIso
      ((affinePushforwardSectionsIso φ).app (tilde M) ≪≫
        (ModuleCat.restrictScalars φ.hom).mapIso (tilde.isoTop M).symm)

/-- The actual affine algebra regarded as a module over the base ring. -/
abbrev affineRestrictedRing : ModuleCat.{u} R :=
  (ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of S S)

/-- The ring homomorphism as a base-linear map to its restricted module. -/
def affineRingInclusion : ModuleCat.of R R ⟶ affineRestrictedRing φ :=
  ModuleCat.ofHom (X := ModuleCat.of R R) (Y := affineRestrictedRing φ)
    { toFun := φ
      map_add' := map_add φ.hom
      map_smul' := fun r s => map_mul φ.hom r s }

@[simp]
theorem affineRingInclusion_apply (r : R) : affineRingInclusion φ r = φ r := rfl

/-- The genuine affine structure sheaf is the associated module `R`. -/
abbrev affineStructureSheaf (R : CommRingCat.{u}) : (Spec R).Modules :=
  SheafOfModules.unit (Spec R).ringCatSheaf

/-- The comparison with the literal structure-sheaf direct image. -/
def affinePushforwardStructureIso :
    (Scheme.Modules.pushforward (Spec.map φ)).obj (affineStructureSheaf S) ≅
      tilde (affineRestrictedRing φ) :=
  (Scheme.Modules.pushforward (Spec.map φ)).mapIso (tildeSelf (R := S)).symm ≪≫
    affinePushforwardTildeIso φ (ModuleCat.of S S)

/-- The affine monomial inclusion, viewed as a morphism of actual sheaves. -/
def affineStructureInclusion :
    affineStructureSheaf R ⟶
      (Scheme.Modules.pushforward (Spec.map φ)).obj (affineStructureSheaf S) :=
  (tildeSelf (R := R)).inv ≫ tilde.map (affineRingInclusion φ) ≫
    (affinePushforwardStructureIso φ).inv

/-- A base-linear coefficient projection gives a morphism of actual
affine sheaves. -/
def affineStructureProjection (π : affineRestrictedRing φ ⟶ ModuleCat.of R R) :
    (Scheme.Modules.pushforward (Spec.map φ)).obj (affineStructureSheaf S) ⟶
      affineStructureSheaf R :=
  (affinePushforwardStructureIso φ).hom ≫ tilde.map π ≫ (tildeSelf (R := R)).hom

set_option backward.isDefEq.respectTransparency.types false in
/-- A module retraction is an actual sheaf retraction after affine descent. -/
theorem affineStructureInclusion_projection
    (π : affineRestrictedRing φ ⟶ ModuleCat.of R R)
    (hπ : ∀ r : R, π (φ r) = r) :
    affineStructureInclusion φ ≫ affineStructureProjection φ π =
      𝟙 (affineStructureSheaf R) := by
  have h : affineRingInclusion φ ≫ π = 𝟙 (ModuleCat.of R R) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    exact hπ r
  simp only [affineStructureInclusion, affineStructureProjection, Category.assoc,
    Iso.inv_hom_id_assoc]
  rw [← tilde.map_comp_assoc, h, tilde.map_id_assoc, Iso.inv_hom_id]

/-- The canonical structure sheaf is genuinely a retract of this affine
direct image, under precisely the supplied ring-module retraction. -/
def affineStructureRetract
    (π : affineRestrictedRing φ ⟶ ModuleCat.of R R)
    (hπ : ∀ r : R, π (φ r) = r) :
    Retract (affineStructureSheaf R)
      ((Scheme.Modules.pushforward (Spec.map φ)).obj (affineStructureSheaf S)) where
  i := affineStructureInclusion φ
  r := affineStructureProjection φ π
  retract := affineStructureInclusion_projection φ π hπ

end ToricPower
