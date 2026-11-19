module

public import ToricPower.DivisorWeightTensorNaturality

/-! # Values of the actual sheafified tensor lift

The universal sheafification transpose is evaluated on the genuine
sectionwise pure tensor. This small interface avoids unfolding the
sheaf tensor construction in later projection-formula comparisons.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite
open scoped TensorProduct

namespace ToricPower

universe u

variable {X : Scheme.{u}}

theorem schemeTensorLift_pureSection (M N P : X.Modules)
    (f : M.val ⊗ N.val ⟶ P.val) (U : X.Opens)
    (s : Γ(M,U)) (t : Γ(N,U)) :
    Scheme.Modules.Hom.app
      ((M.tensorUnderlyingIso N).hom ≫
        ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv
          (M.val ⊗ N.val) P).symm f) U
      (schemeTensorSection M N U s t) =
        f.app (op U) (s ⊗ₜ[X.sheaf.obj.obj (op U)] t) := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let h := (adj.homEquiv (M.val ⊗ N.val) P).symm f
  have unit_eq : adj.unit.app (M.val ⊗ N.val) ≫ h.val = f :=
    (adj.homEquiv (M.val ⊗ N.val) P).apply_symm_apply f
  rw [schemeTensorSection_eq_sheafification]
  rw [← schemeHom_comp_apply,← Category.assoc,Iso.inv_hom_id,Category.id_comp]
  exact ConcreteCategory.congr_hom
    (congrArg (fun g => PresheafOfModules.Hom.app g (op U)) unit_eq)
    _

end ToricPower

end
