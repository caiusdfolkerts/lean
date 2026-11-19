module

public import ToricPower.MonoidalTensorFrame
public import ToricPower.SchemeRestrictionBaseSections
public import ToricPower.SchemeRestrictionTensor
public import ToricPower.DivisorWeightTensorNaturality
public import ToricPower.SheafTensorBaseLinear
public import Mathlib.Algebra.Homology.Additive

/-!
# Actual chart sections in a specified tensor frame

The comparison uses the original restriction tensor map and the chosen
frame. Its inverse sends a section to its literal tensor with the frame
section. The scalar action, the image open, and the top/open-range
transport are retained. All comparisons extend to arbitrary complexes.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite
open scoped TensorProduct

namespace ToricPower

universe u

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (L : X.Modules) (frame : SheafOfModules.unit U.ringCatSheaf ≅ L.restrict j)

/-- The original module-sheaf comparison, natural in the other factor. -/
def schemeTensorFrameRestrictionIso :
    tensorRight L ⋙ Scheme.Modules.restrictFunctor j ≅ Scheme.Modules.restrictFunctor j :=
  tensorRightFrameIso (Scheme.Modules.restrictFunctor j) L frame

private theorem rightUnitor_inv_actualSection {Y : Scheme.{u}} (M : Y.Modules)
    (V : Y.Opens) (s : Γ(M,V)) :
    Scheme.Modules.Hom.app (ρ_ M).inv V s =
      schemeTensorSection M (SheafOfModules.unit Y.ringCatSheaf) V s (1 : Γ(Y,V)) := by
  have h := ConcreteCategory.congr_hom
    (Functor.LaxMonoidal.right_unitality_inv (Scheme.Modules.sectionsFunctor V) M) s
  rw [Scheme.Modules.sectionsFunctor_ε] at h
  exact h.symm

private theorem restriction_actualTensorSection (M P : X.Modules) (V : U.Opens)
    (s : Γ(M,j ''ᵁ V)) (t : Γ(P,j ''ᵁ V)) :
    Scheme.Modules.Hom.app (Functor.LaxMonoidal.μ (Scheme.Modules.restrictFunctor j) M P) V
      (schemeTensorSection (M.restrict j) (P.restrict j) V s t) =
      schemeTensorSection M P (j ''ᵁ V) s t :=
  TauCeti.SheafOfModules.pushforward_μ_app_tmul
    (Scheme.Modules.restrictRingCatSheafHom j) M P (op V) s t

/-- The complete inverse has exactly the specified pure-tensor value. -/
theorem schemeTensorFrameRestrictionIso_inv_section (M : X.Modules) (V : U.Opens)
    (s : Γ(M,j ''ᵁ V)) :
    Scheme.Modules.Hom.app ((schemeTensorFrameRestrictionIso j L frame).inv.app M) V s =
      schemeTensorSection M L (j ''ᵁ V) s
        (Scheme.Modules.Hom.app frame.hom V (1 : Γ(U,V))) := by
  rw [schemeTensorFrameRestrictionIso,tensorRightFrameIso_inv_app,
    schemeHom_comp_apply,schemeHom_comp_apply,rightUnitor_inv_actualSection,
    ← id_tensorHom]
  exact (congrArg (fun z => Scheme.Modules.Hom.app
      (Functor.LaxMonoidal.μ (Scheme.Modules.restrictFunctor j) M L) V z)
    (schemeTensorSection_naturality (𝟙 (M.restrict j)) frame.hom V s (1 : Γ(U,V)))).trans
      (restriction_actualTensorSection j M L V s _)

variable (k : Type u) [Field k]
  [U.Over (Spec (.of k))] [X.Over (Spec (.of k))] [j.IsOver (Spec (.of k))]

/-- Base-linear sections on the literal image open. -/
def schemeTensorFrameSectionsIso (V : U.Opens) :
    tensorRight L ⋙ FiniteCover.schemeBaseSections k X (j ''ᵁ V) ≅
      FiniteCover.schemeBaseSections k X (j ''ᵁ V) :=
  Functor.isoWhiskerLeft (tensorRight L) (restrictionBaseSectionsIso k j V).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (schemeTensorFrameRestrictionIso j L frame)
      (FiniteCover.schemeBaseSections k U V) ≪≫
    restrictionBaseSectionsIso k j V

/-- The scalar comparison is the same actual inserted section. -/
theorem schemeTensorFrameSectionsIso_inv_apply (M : X.Modules) (V : U.Opens)
    (s : (FiniteCover.schemeBaseSections k X (j ''ᵁ V)).obj M) :
    ((schemeTensorFrameSectionsIso j L frame k V).inv.app M) s =
      schemeTensorSection M L (j ''ᵁ V) s
        (Scheme.Modules.Hom.app frame.hom V (1 : Γ(U,V))) := by
  exact schemeTensorFrameRestrictionIso_inv_section j L frame M V s

/-- Equality of the image of top with the actual open range is transported
on both sides of the specified tensor frame. -/
def schemeTensorFrameGlobalSectionsIso :
    tensorRight L ⋙ FiniteCover.schemeBaseSections k X j.opensRange ≅
      FiniteCover.schemeBaseSections k X j.opensRange :=
  Functor.isoWhiskerLeft (tensorRight L)
      (eqToIso (congrArg (FiniteCover.schemeBaseSections k X) j.image_top_eq_opensRange)).symm ≪≫
    schemeTensorFrameSectionsIso j L frame k ⊤ ≪≫
    eqToIso (congrArg (FiniteCover.schemeBaseSections k X) j.image_top_eq_opensRange)

/-- The same original natural comparison in every cochain degree. -/
def schemeTensorFrameComplexSectionsIso {ι : Type*} (shape : ComplexShape ι) (V : U.Opens) :
    (tensorRight L).mapHomologicalComplex shape ⋙
      (FiniteCover.schemeBaseSections k X (j ''ᵁ V)).mapHomologicalComplex shape ≅
    (FiniteCover.schemeBaseSections k X (j ''ᵁ V)).mapHomologicalComplex shape :=
  Functor.mapHomologicalComplexCompIso (schemeTensorFrameSectionsIso j L frame k V) shape

def schemeTensorFrameComplexGlobalSectionsIso {ι : Type*} (shape : ComplexShape ι) :
    (tensorRight L).mapHomologicalComplex shape ⋙
      (FiniteCover.schemeBaseSections k X j.opensRange).mapHomologicalComplex shape ≅
    (FiniteCover.schemeBaseSections k X j.opensRange).mapHomologicalComplex shape :=
  Functor.mapHomologicalComplexCompIso (schemeTensorFrameGlobalSectionsIso j L frame k) shape

end ToricPower

end
