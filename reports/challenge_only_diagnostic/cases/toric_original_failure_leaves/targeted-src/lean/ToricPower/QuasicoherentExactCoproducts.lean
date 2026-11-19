module

public import ToricPower.QuasicoherentCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules

/-!
# Exact coproducts of actual quasicoherent sheaves

The actual full inclusion preserves colimits and preserves and reflects
finite limits.  Exactness therefore descends from the genuine abelian
category of all module sheaves.  This holds on every scheme.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace ToricPower

universe u

instance quasicoherentAB4 (X : Scheme.{u}) : AB4OfSize.{u} (QCoh X) where
  ofShape I := by
    let F := quasicoherentInclusion X
    letI : F.Full := (SheafOfModules.isQuasicoherent X.ringCatSheaf).fullyFaithfulι.full
    letI : F.Faithful := (SheafOfModules.isQuasicoherent X.ringCatSheaf).fullyFaithfulι.faithful
    letI : ReflectsLimitsOfSize.{0, 0} F := inferInstance
    exact HasExactColimitsOfShape.domain_of_functor (Discrete I) F

end ToricPower

end
