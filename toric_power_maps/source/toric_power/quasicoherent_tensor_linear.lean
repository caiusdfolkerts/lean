module

public import ToricPower.QuasicoherentBaseLinear
public import ToricPower.SheafTensorBaseLinear

/-! # The actual scalar action on quasicoherent tensor functors -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory MonoidalCategory

namespace ToricPower

universe u

variable (k : Type u) [CommRing k] (X : Scheme.{u}) [X.Over (Spec (.of k))]

instance quasicoherentTensorRight_linear (M : QCoh X) :
    (tensorRight M).Linear k where
  map_smul f r := by
    letI : Linear k (_root_.SheafOfModules X.ringCatSheaf) := Scheme.Modules.baseLinear k X
    apply ObjectProperty.hom_ext
    exact (schemeTensorRight_baseLinear k X M.obj).map_smul f.hom r

instance quasicoherentTensorLeft_linear (M : QCoh X) :
    (tensorLeft M).Linear k where
  map_smul f r := by
    letI : Linear k (_root_.SheafOfModules X.ringCatSheaf) := Scheme.Modules.baseLinear k X
    apply ObjectProperty.hom_ext
    exact (schemeTensorLeft_baseLinear k X M.obj).map_smul f.hom r

end ToricPower

end
