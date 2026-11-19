module

public import ToricPower.CoherentRestriction

/-!
# Coherent images inside arbitrary quasicoherent sheaves

On a locally Noetherian scheme, the kernel of a map from a coherent
sheaf to any quasicoherent sheaf is coherent. Its cokernel is the
actual image. The target need not itself be coherent, which is the
essential point when the target is an open direct image.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Scheme.Modules

namespace ToricPower

universe u

variable {X : Scheme.{u}} [IsLocallyNoetherian X] {M E : X.Modules}
  [M.IsFinitePresentation] [E.IsQuasicoherent]

/-- The source is coherent and the target is only quasicoherent. -/
theorem finitePresentation_kernel_of_coherent_source (f : M ⟶ E) :
    (kernel f).IsFinitePresentation := by
  apply finitePresentation_of_fromSpec
  intro U
  letI : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  let F := restrictFunctor U.2.fromSpec
  letI : (F.obj M).IsFinitePresentation := finitePresentation_restrict U.2.fromSpec M
  letI : (F.obj M).IsQuasicoherent :=
    SheafOfModules.instIsQuasicoherentOfIsFinitePresentation (F.obj M)
  letI : (F.obj M).IsFiniteType :=
    SheafOfModules.instIsFiniteTypeOfIsFinitePresentation (F.obj M)
  letI : (F.obj E).IsQuasicoherent := inferInstance
  letI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  exact (SheafOfModules.isFinitePresentation (Spec Γ(X,U.1)).ringCatSheaf).prop_of_iso
    (PreservesKernel.iso F f).symm
    (Scheme.Modules.isFinitePresentation_kernel_spec (F.map f))

/-- The actual categorical image of a coherent sheaf in a quasicoherent
sheaf is coherent. -/
theorem finitePresentation_image_of_coherent_source (f : M ⟶ E) :
    (image f).IsFinitePresentation := by
  letI := finitePresentation_kernel_of_coherent_source f
  exact (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso
    (Abelian.coimageIsoImage' f) (finitePresentation_cokernel (kernel.ι f))

end ToricPower

end
