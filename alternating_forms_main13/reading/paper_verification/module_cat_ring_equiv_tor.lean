module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Actual tensor products and projective resolutions under a ring isomorphism

Restriction by the inverse ring isomorphism changes the coefficient ring
of every actual module and resolution.  The balanced tensor products are
compared by the map that keeps every pure tensor unchanged.  Applying this
comparison to an actual projective resolution gives a comparison of the
ordinary derived functor Tor.  The formulas on tensor terms are retained
so that internal gradings of specific resolutions can also be compared.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped TensorProduct

namespace PaperVerification.ModuleCatRingEquivTor

open CategoryTheory CategoryTheory.MonoidalCategory HomologicalComplex

universe u
variable {A D : Type u} [CommRing A] [CommRing D] (e : A ≃+* D)

/-- Modules with their actual scalar action changed through the inverse
ring isomorphism.  Their underlying additive groups are unchanged. -/
abbrev scalarChange : ModuleCat.{u} A ⥤ ModuleCat.{u} D :=
  ModuleCat.restrictScalars e.symm.toRingHom

local instance originalModule (X : ModuleCat.{u} A) :
    Module A ((scalarChange e).obj X) := inferInstanceAs (Module A X)

local instance originalChangedCommute (X : ModuleCat.{u} A) :
    SMulCommClass A D ((scalarChange e).obj X) where
  smul_comm a d x := by
    change a • (e.symm d • x)=e.symm d • (a • x)
    exact smul_comm _ _ _

local instance compatibleOriginalChanged (X Y : ModuleCat.{u} A) :
    TensorProduct.CompatibleSMul A D ((scalarChange e).obj X) ((scalarChange e).obj Y) where
  smul_tmul d x y := by
    change (e.symm d • x) ⊗ₜ[A] y=x ⊗ₜ[A] (e.symm d • y)
    exact TensorProduct.smul_tmul _ _ _

local instance compatibleChangedOriginal (X Y : ModuleCat.{u} A) :
    TensorProduct.CompatibleSMul D A ((scalarChange e).obj X) ((scalarChange e).obj Y) where
  smul_tmul a x y := by
    have h := TensorProduct.smul_tmul (R := D) (e a)
      (x : (scalarChange e).obj X) (y : (scalarChange e).obj Y)
    change (e.symm (e a) • x) ⊗ₜ[D] y=x ⊗ₜ[D] (e.symm (e a) • y) at h
    simpa only [e.symm_apply_apply] using h

/-- The literal identity on pure tensors gives the actual change-of-ring
tensor equivalence. -/
def tensorEquiv (X Y : ModuleCat.{u} A) :
    ((scalarChange e).obj X ⊗[D] (scalarChange e).obj Y) ≃ₗ[D]
      (scalarChange e).obj (X ⊗ Y) :=
  TensorProduct.equivOfCompatibleSMul A D D
    ((scalarChange e).obj X) ((scalarChange e).obj Y)

@[simp] theorem tensorEquiv_tmul (X Y : ModuleCat.{u} A)
    (x : X) (y : Y) : tensorEquiv e X Y (x ⊗ₜ[D] y)=x ⊗ₜ[A] y := rfl

def tensorIso (X Y : ModuleCat.{u} A) :
    (scalarChange e).obj X ⊗ (scalarChange e).obj Y ≅
      (scalarChange e).obj (X ⊗ Y) :=
  (tensorEquiv e X Y).toModuleIso

/-- Naturality in the actual second tensor factor. -/
theorem tensorIso_naturality (X : ModuleCat.{u} A) {Y Z : ModuleCat.{u} A}
    (f : Y ⟶ Z) :
    ((tensoringLeft (ModuleCat D)).obj ((scalarChange e).obj X)).map
        ((scalarChange e).map f) ≫ (tensorIso e X Z).hom=
      (tensorIso e X Y).hom ≫ (scalarChange e).map
        (((tensoringLeft (ModuleCat A)).obj X).map f) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  refine TensorProduct.inductionOn z ?_ ?_
  · intro x y
    rfl
  · intro x y hx hy
    simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- The tensor comparison is an isomorphism of actual complexes, with
the actual differentials coming from the original resolution. -/
def tensorComplexIso (X : ModuleCat.{u} A) (C : ChainComplex (ModuleCat.{u} A) ℕ) :
    ((((tensoringLeft (ModuleCat D)).obj ((scalarChange e).obj X)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj
      (((scalarChange e).mapHomologicalComplex (ComplexShape.down ℕ)).obj C)) ≅
    (((scalarChange e).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      ((((tensoringLeft (ModuleCat A)).obj X).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj C)) :=
  HomologicalComplex.Hom.isoOfComponents (fun i ↦ tensorIso e X (C.X i)) (by
    intro i j hij
    exact (tensorIso_naturality e X (C.d i j)).symm)

/-- Actual projective resolutions remain projective resolutions after
changing scalars by a ring isomorphism. -/
def resolution {Y : ModuleCat.{u} A} (P : ProjectiveResolution Y) :
    ProjectiveResolution ((scalarChange e).obj Y) :=
  (scalarChange e).mapProjectiveResolution P

/-- The actual ordinary Tor objects, compared through an actual supplied
projective resolution.  The resolution is data with verified exactness,
not a premise asserting the desired Tor conclusion. -/
def torIso (X Y : ModuleCat.{u} A) (P : ProjectiveResolution Y) (r : ℕ) :
    (((Tor (ModuleCat D) r).obj ((scalarChange e).obj X)).obj ((scalarChange e).obj Y)) ≅
      (scalarChange e).obj (((Tor (ModuleCat A) r).obj X).obj Y) :=
  (resolution e P).isoLeftDerivedObj
      ((tensoringLeft (ModuleCat D)).obj ((scalarChange e).obj X)) r ≪≫
    HomologicalComplex.homologyMapIso (tensorComplexIso e X P.complex) r ≪≫
    (((((tensoringLeft (ModuleCat A)).obj X).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj P.complex).sc r).mapHomologyIso (scalarChange e) ≪≫
    (scalarChange e).mapIso
      (P.isoLeftDerivedObj ((tensoringLeft (ModuleCat A)).obj X) r).symm

section Coefficients

variable {K : Type u} [CommRing K] [Algebra K A] [Algebra K D]
  (f : A ≃ₐ[K] D)

/-- The two actual scalar-restriction functors agree over the original
coefficient ring, with the identity underlying additive map. -/
def coefficientsIso (X : ModuleCat.{u} A) :
    (ModuleCat.restrictScalars (algebraMap K A)).obj X ≅
      (ModuleCat.restrictScalars (algebraMap K D)).obj
        ((scalarChange f.toRingEquiv).obj X) :=
  ModuleCat.restrictScalarsComp'App (algebraMap K D) f.symm.toRingHom
    (algebraMap K A) (by
      apply RingHom.ext
      intro c
      exact (f.symm.commutes c).symm) X

@[simp] theorem coefficientsIso_hom_apply (X : ModuleCat.{u} A) (x : X) :
    (coefficientsIso f X).hom x=x := rfl

@[simp] theorem coefficientsIso_inv_apply (X : ModuleCat.{u} A) (x : X) :
    (coefficientsIso f X).inv x=x := rfl

/-- The tensor comparison over the original coefficient ring keeps
every actual pure tensor unchanged. -/
def tensorIsoOverCoefficients (X Y : ModuleCat.{u} A) :
    (ModuleCat.restrictScalars (algebraMap K D)).obj
        ((scalarChange f.toRingEquiv).obj X ⊗ (scalarChange f.toRingEquiv).obj Y) ≅
      (ModuleCat.restrictScalars (algebraMap K A)).obj (X ⊗ Y) :=
  (ModuleCat.restrictScalars (algebraMap K D)).mapIso
      (tensorIso f.toRingEquiv X Y) ≪≫ (coefficientsIso f (X ⊗ Y)).symm

@[simp] theorem tensorIsoOverCoefficients_hom_tmul (X Y : ModuleCat.{u} A)
    (x : X) (y : Y) :
    (tensorIsoOverCoefficients f X Y).hom (x ⊗ₜ[D] y)=x ⊗ₜ[A] y := rfl

/-- The actual derived tensor comparison, also preserving the original
coefficient-field linear structure. -/
def torIsoOverCoefficients (X Y : ModuleCat.{u} A)
    (P : ProjectiveResolution Y) (r : ℕ) :
    (ModuleCat.restrictScalars (algebraMap K D)).obj
      (((Tor (ModuleCat D) r).obj ((scalarChange f.toRingEquiv).obj X)).obj
        ((scalarChange f.toRingEquiv).obj Y)) ≅
      (ModuleCat.restrictScalars (algebraMap K A)).obj
        (((Tor (ModuleCat A) r).obj X).obj Y) :=
  (ModuleCat.restrictScalars (algebraMap K D)).mapIso
      (torIso f.toRingEquiv X Y P r) ≪≫
    (coefficientsIso f (((Tor (ModuleCat A) r).obj X).obj Y)).symm

end Coefficients

end PaperVerification.ModuleCatRingEquivTor
