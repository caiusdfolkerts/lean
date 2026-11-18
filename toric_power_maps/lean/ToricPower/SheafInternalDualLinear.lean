module

public import ToricPower.InternalDualLinear
public import ToricPower.SchemeInternalDual
public import ToricPower.SheafTensorBaseLinear

/-! # The sheaf internal dual retains the actual scheme base scalar -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

namespace ToricPower

universe u

variable (R : Type u) [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))]

/-- Both tensor variables are linear for the genuine scalar action
coming from the scheme's structure morphism. -/
instance schemeMonoidal_baseLinear : MonoidalLinear R X.Modules where
  whiskerLeft_smul M {_ _} r f :=
    (schemeTensorLeft_baseLinear R X M).map_smul f r
  smul_whiskerRight r {_ _} f M :=
    (schemeTensorRight_baseLinear R X M).map_smul f r

end ToricPower

end
