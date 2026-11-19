module

public import PaperVerification.SheafModulePowers
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Sections of the actual kernel sheaf

Evaluation preserves limits of module sheaves. This gives the concrete kernel
of the map on sections, and the comparison commutes with the inclusion.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits Opposite

namespace PaperVerification.SheafModuleKernels

universe u
variable {X : AlgebraicGeometry.Scheme.{u}} {M N : X.Modules}

local instance (U : X.Opens) :
    (SheafOfModules.evaluation X.ringCatSheaf (op U)).Additive := by
  dsimp [SheafOfModules.evaluation]
  infer_instance

/-- Evaluation of the categorical kernel is the ordinary kernel module. -/
def sectionsIso (f : M ⟶ N) (U : X.Opens) :
    (SheafOfModules.evaluation X.ringCatSheaf (op U)).obj (kernel f) ≅
      ModuleCat.of (X.ringCatSheaf.obj.obj (op U))
        ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map f).hom.ker :=
  PreservesKernel.iso (SheafOfModules.evaluation X.ringCatSheaf (op U)) f ≪≫
    ModuleCat.kernelIsoKer ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map f)

/-- The canonical section comparison as a linear equivalence. -/
def sectionsEquiv (f : M ⟶ N) (U : X.Opens) :
    (kernel f).val.obj (op U) ≃ₗ[X.ringCatSheaf.obj.obj (op U)]
      ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map f).hom.ker :=
  (sectionsIso f U).toLinearEquiv

/-- The comparison identifies the actual sheaf inclusion with subtype inclusion. -/
@[simp] theorem sectionsEquiv_coe (f : M ⟶ N) (U : X.Opens)
    (x : (kernel f).val.obj (op U)) :
    (sectionsEquiv f U x).val = (kernel.ι f).val.app (op U) x := by
  have h : (sectionsIso f U).hom ≫ ModuleCat.ofHom
      (((SheafOfModules.evaluation X.ringCatSheaf (op U)).map f).hom.ker.subtype) =
        (SheafOfModules.evaluation X.ringCatSheaf (op U)).map (kernel.ι f) := by
    simp only [sectionsIso, Iso.trans_hom, Category.assoc,
      ModuleCat.kernelIsoKer_hom_ker_subtype, PreservesKernel.iso_hom,
      kernelComparison_comp_ι]
  exact congrArg (fun g => g x) h

end PaperVerification.SheafModuleKernels
