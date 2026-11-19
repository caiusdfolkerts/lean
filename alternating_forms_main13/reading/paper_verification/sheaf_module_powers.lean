module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Concrete sections of powers of a module sheaf

Products and kernels are the actual categorical constructions on sheaves of
modules. Evaluation preserves these limits. The comparison below identifies
sections of a power with tuples of sections, compatibly with every projection.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits Opposite

namespace PaperVerification.SheafModulePowers

universe u
variable {X : AlgebraicGeometry.Scheme.{u}}

def power (M : X.Modules) (I : Type u) : X.Modules := ∏ᶜ (fun _ : I => M)

/-- A power of the actual structure module. For finite `I` this is `𝒪^I`. -/
def structurePower (X : AlgebraicGeometry.Scheme.{u}) (I : Type u) : X.Modules :=
  power (X:=X) (SheafOfModules.unit X.ringCatSheaf) I

/-- Coordinate reindexing between genuine categorical powers. -/
def reindex (M : X.Modules) (I J : Type u) (f : J → I) :
    power M I ⟶ power M J :=
  Pi.lift fun j ↦ Pi.π (fun _ : I ↦ M) (f j)

/-- Reindexing retains each specified coordinate projection. -/
theorem reindex_projection (M : X.Modules) (I J : Type u) (f : J → I) (j : J) :
    reindex M I J f ≫ Pi.π (fun _ : J ↦ M) j = Pi.π (fun _ : I ↦ M) (f j) := by
  unfold reindex
  exact Pi.lift_comp_π _ j

/-- The section comparison is induced by the genuine product projections. -/
def sectionsIso (M : X.Modules) (I : Type u) (U : X.Opens) :
    (SheafOfModules.evaluation X.ringCatSheaf (op U)).obj (power M I) ≅
      ModuleCat.of (X.ringCatSheaf.obj.obj (op U))
        (I → M.val.obj (op U)) :=
  PreservesProduct.iso (SheafOfModules.evaluation X.ringCatSheaf (op U))
      (fun _ : I => M) ≪≫
    ModuleCat.piIsoPi (fun _ : I => M.val.obj (op U))

def sectionsEquiv (M : X.Modules) (I : Type u) (U : X.Opens) :
    (power M I).val.obj (op U) ≃ₗ[X.ringCatSheaf.obj.obj (op U)]
      (I → M.val.obj (op U)) :=
  (sectionsIso M I U).toLinearEquiv

@[simp] theorem sectionsEquiv_apply (M : X.Modules) (I : Type u) (U : X.Opens)
    (x : (power M I).val.obj (op U)) (i : I) :
    sectionsEquiv M I U x i = (Pi.π (fun _ : I => M) i).val.app (op U) x := by
  have h : (sectionsIso M I U).hom ≫
      ModuleCat.ofHom (LinearMap.proj i) =
        (SheafOfModules.evaluation X.ringCatSheaf (op U)).map
          (Pi.π (fun _ : I => M) i) := by
    simp only [sectionsIso, Iso.trans_hom, Category.assoc,
      ModuleCat.piIsoPi_hom_ker_subtype, PreservesProduct.iso_hom]
    exact piComparison_comp_π (SheafOfModules.evaluation X.ringCatSheaf (op U))
      (fun _ : I => M) i
  exact congrArg (fun f => f x) h

/-- Equalities of tuples detect equalities of actual sections. -/
theorem sections_ext (M : X.Modules) (I : Type u) (U : X.Opens)
    {x y : (power M I).val.obj (op U)}
    (h : ∀ i, (Pi.π (fun _ : I => M) i).val.app (op U) x =
      (Pi.π (fun _ : I => M) i).val.app (op U) y) : x=y := by
  apply (sectionsEquiv M I U).injective
  funext i
  simpa only [sectionsEquiv_apply] using h i

/-- A section of the genuine product is zero exactly when all components are. -/
theorem section_eq_zero_iff (M : X.Modules) (I : Type u) (U : X.Opens)
    (x : (power M I).val.obj (op U)) :
    x=0 ↔ ∀ i, (Pi.π (fun _ : I => M) i).val.app (op U) x=0 := by
  constructor
  · intro h i
    rw [h,map_zero]
  · intro h
    apply sections_ext M I U
    intro i
    rw [map_zero]
    exact h i

end PaperVerification.SheafModulePowers
