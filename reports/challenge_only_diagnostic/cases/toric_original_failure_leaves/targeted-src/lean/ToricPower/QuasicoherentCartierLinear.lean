module

public import ToricPower.QuasicoherentCartierTensor
public import ToricPower.SheafTensorBaseLinear
public import ToricPower.QuasicoherentBaseLinear

/-! # Cartier tensor equivalences preserve the actual base-field scalar actions -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open TauCeti.AlgebraicGeometry.Scheme

namespace ToricPower

universe u

variable (k : Type u) [CommRing k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsIntegral X]

instance quasicoherentCartierTensor_linear (D : CartierDivisor X) :
    (quasicoherentCartierTensorEquivalence D).functor.Linear k where
  map_smul f r := by
    apply ObjectProperty.hom_ext
    exact (tensorLeft D.sheaf).map_smul r f.hom

instance quasicoherentCartierInverseTensor_linear (D : CartierDivisor X) :
    (quasicoherentCartierTensorEquivalence D).inverse.Linear k :=
  inferInstanceAs ((quasicoherentCartierTensorEquivalence (-D)).functor.Linear k)

end ToricPower

end
