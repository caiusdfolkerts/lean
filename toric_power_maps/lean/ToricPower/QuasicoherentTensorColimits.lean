module

public import ToricPower.QuasicoherentCategory
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-! # Actual tensor products preserve small colimits of quasicoherent sheaves -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace ToricPower

universe u

instance quasicoherentTensorRight_preservesColimits (X : Scheme.{u}) (N : QCoh X) :
    PreservesColimitsOfSize.{u,u} (tensorRight N) where
  preservesColimitsOfShape {J} _ := by
    letI : PreservesColimitsOfShape J (tensorRight N ⋙ quasicoherentInclusion X) := by
      change PreservesColimitsOfShape J (quasicoherentInclusion X ⋙ tensorRight N.obj)
      infer_instance
    exact preservesColimitsOfShape_of_reflects_of_preserves
      (tensorRight N) (quasicoherentInclusion X)

instance quasicoherentTensorLeft_preservesColimits (X : Scheme.{u}) (N : QCoh X) :
    PreservesColimitsOfSize.{u,u} (tensorLeft N) where
  preservesColimitsOfShape {J} _ := by
    letI : PreservesColimitsOfShape J (tensorLeft N ⋙ quasicoherentInclusion X) := by
      change PreservesColimitsOfShape J (quasicoherentInclusion X ⋙ tensorLeft N.obj)
      infer_instance
    exact preservesColimitsOfShape_of_reflects_of_preserves
      (tensorLeft N) (quasicoherentInclusion X)

end ToricPower

end
