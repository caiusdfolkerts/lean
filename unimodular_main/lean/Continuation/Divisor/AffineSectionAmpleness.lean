module

public import TauCeti.AlgebraicGeometry.LineBundle.NonvanishingLocus
import all TauCeti.AlgebraicGeometry.LineBundle.NonvanishingLocus

public import Continuation.Divisor.IntrinsicAmple
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Monoidal

/-! An actual affine cover by nonvanishing sections gives ordinary ampleness.
The conclusion uses genuine positive tensor powers and their stalk generation. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite TopologicalSpace
open PaperVerification.ToricSchemes
open TauCeti.AlgebraicGeometry (InvertibleSheaf)

universe u
namespace Unimodular.NefBig

variable {X : Scheme.{u}} [IsIntegral X]

local instance affineAmplenessMonoidal : MonoidalCategory X.Modules :=
  TauCeti.SheafOfModules.monoidalCategory X.sheaf

/-- The ordinary first tensor power is canonically the original sheaf. -/
def ordinaryTensorPowerOneIso (M : X.Modules) : tensorSheafPower M 1 ≅ M :=
  (SheafOfModules.tensorUnderlyingIso (SheafOfModules.unit X.ringCatSheaf) M).symm ≪≫
    λ_ M

/-- An affine nonvanishing cover in degree one implies the ordinary
positive-tensor-power criterion, through the actual first-power unitor. -/
theorem isAmpleModule_of_affine_nonvanishing_cover (L : InvertibleSheaf X)
    (hcompact : CompactSpace X)
    (h : ∀ x : X, ∃ s : Γ(L.obj, ⊤),
      x ∈ L.obj.nonvanishingLocus s ∧ IsAffineOpen (L.obj.nonvanishingLocus s)) :
    IsAmpleModule L.obj := by
  let D := invertibleFractionalPresentation L.obj
    ((isInvertibleModule_iff_standard L.obj).mpr L.property)
  let C := D.localCocycle
  let hInv (m : ℕ) :
      TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X
        (tensorSheafPower L.obj m) :=
    (TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X).prop_of_iso
      ((tensorSheafPowerIso D.presentationIso m) ≪≫ C.tensorSheafPowerIso m).symm
      inferInstance
  refine ⟨hInv, hcompact, ?_⟩
  intro x
  obtain ⟨s, hx, ha⟩ := h x
  letI := hInv 1
  refine ⟨1, Nat.zero_lt_one, (ordinaryTensorPowerOneIso L.obj).inv.app ⊤ s, ?_, ?_⟩
  · have he := Scheme.Modules.nonvanishingLocus_hom_app
      (ordinaryTensorPowerOneIso L.obj).symm s
    change (tensorSheafPower L.obj 1).nonvanishingLocus
      ((ordinaryTensorPowerOneIso L.obj).inv.app ⊤ s) = _ at he
    rw [he]
    exact hx
  · have he := Scheme.Modules.nonvanishingLocus_hom_app
      (ordinaryTensorPowerOneIso L.obj).symm s
    change (tensorSheafPower L.obj 1).nonvanishingLocus
      ((ordinaryTensorPowerOneIso L.obj).inv.app ⊤ s) = _ at he
    rw [he]
    exact ha

end Unimodular.NefBig
