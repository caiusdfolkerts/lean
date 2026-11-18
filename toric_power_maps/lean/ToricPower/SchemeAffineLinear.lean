module

public import ToricPower.AffineTildeComplex
public import ToricPower.SchemeModulesBaseLinear
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Affine free modules and actual linear sheaf operations

The scalar action here is the actual multiplication by a global function.
The finite-free comparison is obtained from the actual finite coproduct of
modules, preservation by the tilde functor, and the biproduct universal
property. Its generators are recorded as actual sheaf morphisms.

Development source: all declarations require pinned compilation before any
verification claim.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable (R : Type u) [CommRing R]
  {X Y : Scheme.{u}} [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))]

/-- Pullback of a global base-ring scalar is the same scalar on the source. -/
theorem appTop_baseRingToGlobalSections (f : X ⟶ Y) [f.IsOver (Spec (.of R))]
    (r : R) :
    f.appTop (baseRingToGlobalSections R Y r) = baseRingToGlobalSections R X r := by
  have h := congrArg Scheme.Hom.appTop
    (HomIsOver.comp_over (f := f) (S := Spec (.of R)))
  rw [Scheme.Hom.comp_appTop] at h
  simpa only [baseRingToGlobalSections_apply, ConcreteCategory.comp_apply] using
    ConcreteCategory.congr_hom h ((Scheme.ΓSpecIso (.of R)).inv r)

/-- Actual module-sheaf pullback is linear over the base ring whenever the
scheme morphism respects that base. -/
instance pullbackBaseLinear (f : X ⟶ Y) [f.IsOver (Spec (.of R))] :
    Functor.Linear R (pullback f) where
  map_smul g r := by
    rw [base_smul_eq R Y, Functor.map_comp, pullback_map_globalSectionsSmul,
      appTop_baseRingToGlobalSections R f, base_smul_eq R X]

/-- Actual module-sheaf direct image also respects base-ring scalars. -/
instance pushforwardBaseLinear (f : X ⟶ Y) [f.IsOver (Spec (.of R))] :
    Functor.Linear R (pushforward f) where
  map_smul g r := by
    rw [base_smul_eq R X, ← appTop_baseRingToGlobalSections R f,
      Functor.map_comp, pushforward_map_globalSectionsSmul, base_smul_eq R Y]

end AlgebraicGeometry.Scheme.Modules

namespace ToricPower

universe u

variable (R : CommRingCat.{u})

/-- Tilde sends scalar multiplication on an actual module to multiplication
by the corresponding actual affine global function. -/
theorem tilde_smul_id (M : ModuleCat.{u} R) (r : R) :
    tilde.map (r • 𝟙 M) =
      Scheme.Modules.globalSectionsSmul (tilde M) ((Scheme.ΓSpecIso R).inv r) := by
  apply (tilde.adjunction.homEquiv M (tilde M)).injective
  change tilde.toOpen M ⊤ ≫
      (modulesSpecToSheaf.map (tilde.map (r • 𝟙 M))).1.app (op ⊤) =
    tilde.toOpen M ⊤ ≫
      (modulesSpecToSheaf.map
        (Scheme.Modules.globalSectionsSmul (tilde M)
          ((Scheme.ΓSpecIso R).inv r))).1.app (op ⊤)
  erw [tilde.toOpen_map_app]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change (tilde.toOpen M ⊤) (r • m) =
    (Scheme.Modules.globalSectionsSmul (tilde M)
      ((Scheme.ΓSpecIso R).inv r)).app ⊤ ((tilde.toOpen M ⊤) m)
  rw [map_smul, Scheme.Modules.globalSectionsSmul_app]
  exact Scheme.Modules.smul_Spec_def (M := tilde M) (U := ⊤) r
    ((tilde.toOpen M ⊤) m)

/-- On the actual trivial affine sheaf, the tilde scalar map agrees with
multiplication in the structure sheaf, including the chosen `tildeSelf`
identification. -/
theorem tildeScalarSelf (r : R) :
    tilde.map (r • 𝟙 (ModuleCat.of R R)) ≫ (tildeSelf (R := R)).hom =
      (tildeSelf (R := R)).hom ≫
        Scheme.Modules.globalSectionsSmul (SheafOfModules.unit (Spec R).ringCatSheaf)
          ((Scheme.ΓSpecIso R).inv r) := by
  rw [tilde_smul_id]
  exact Scheme.Modules.globalSectionsSmul_naturality (tildeSelf (R := R)).hom _

/-- The scalar map expressed entirely in the unit sheaf's affine frame. -/
@[simp]
theorem tildeScalarSelf_unit_frame (r : R) :
    (tildeSelf (R := R)).inv ≫ tilde.map (r • 𝟙 (ModuleCat.of R R)) ≫
        (tildeSelf (R := R)).hom =
      Scheme.Modules.globalSectionsSmul (SheafOfModules.unit (Spec R).ringCatSheaf)
        ((Scheme.ΓSpecIso R).inv r) := by
  rw [tildeScalarSelf]
  exact Iso.inv_hom_id_assoc _ _

variable (I : Type u) [Finite I]

/-- Tilde of a finite free module is the actual finite biproduct of copies
of the structure sheaf. This uses the true module coproduct and its
preservation by the tilde functor, and works in arbitrary ambient universes. -/
def tildeFiniteFreeBiproductIso :
    tilde (ModuleCat.of R (I →₀ R)) ≅
      ⨁ (fun _ : I => SheafOfModules.unit (Spec R).ringCatSheaf) :=
  let H : IsColimit ((tilde.functor R).mapCocone (ModuleCat.finsuppCocone R R I)) :=
    isColimitOfPreserves (tilde.functor R) (ModuleCat.finsuppCoconeIsColimit R R I)
  let e : (Discrete.functor (fun _ : I => ModuleCat.of R R)) ⋙ tilde.functor R ≅
      Discrete.functor (fun _ : I => SheafOfModules.unit (Spec R).ringCatSheaf) :=
    Discrete.natIso (fun _ => tildeSelf)
  IsColimit.coconePointUniqueUpToIso
    ((IsColimit.precomposeHomEquiv e.symm _).symm H) (biproduct.isColimit _)

/-- The comparison sends the actual module generator to the corresponding
actual biproduct inclusion, with domain the structure sheaf. -/
@[reassoc (attr := simp)]
theorem tildeFiniteFreeBiproductIso_single (j : I) :
    (tildeSelf (R := R)).inv ≫
      tilde.map (ModuleCat.ofHom (Finsupp.lsingle j : R →ₗ[R] I →₀ R)) ≫
        (tildeFiniteFreeBiproductIso R I).hom =
      biproduct.ι (fun _ : I => SheafOfModules.unit (Spec R).ringCatSheaf) j := by
  let H : IsColimit ((tilde.functor R).mapCocone (ModuleCat.finsuppCocone R R I)) :=
    isColimitOfPreserves (tilde.functor R) (ModuleCat.finsuppCoconeIsColimit R R I)
  let e : (Discrete.functor (fun _ : I => ModuleCat.of R R)) ⋙ tilde.functor R ≅
      Discrete.functor (fun _ : I => SheafOfModules.unit (Spec R).ringCatSheaf) :=
    Discrete.natIso (fun _ => tildeSelf)
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom
    ((IsColimit.precomposeHomEquiv e.symm _).symm H)
    (biproduct.isColimit
      (fun _ : I => SheafOfModules.unit (Spec R).ringCatSheaf)) (Discrete.mk j)
  change ((tildeSelf (R := R)).inv ≫
      tilde.map (ModuleCat.ofHom (Finsupp.lsingle j : R →ₗ[R] I →₀ R))) ≫
        (tildeFiniteFreeBiproductIso R I).hom = _ at h
  simpa only [Category.assoc, Bicone.toCocone_ι_app,
    biproduct.bicone_ι] using h

/-- The generator formula with domain the tilde of the rank-one module. -/
@[reassoc]
theorem tildeFiniteFreeBiproductIso_single_fromTilde (j : I) :
    tilde.map (ModuleCat.ofHom (Finsupp.lsingle j : R →ₗ[R] I →₀ R)) ≫
        (tildeFiniteFreeBiproductIso R I).hom =
      (tildeSelf (R := R)).hom ≫
        biproduct.ι (fun _ : I => SheafOfModules.unit (Spec R).ringCatSheaf) j := by
  apply (cancel_epi (tildeSelf (R := R)).inv).mp
  rw [tildeFiniteFreeBiproductIso_single, Iso.inv_hom_id_assoc]

end ToricPower

end
