module

public import ToricPower.InternalDualComplex
public import ToricPower.SheafClosed

/-!
# Actual internal duality for scheme modules

The preadditive tensor structure and dualizability below are consequences
of the already proved closed structure and local finite-free comparison.
They supply the categorical interfaces without changing the module sheaf.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

namespace ToricPower

universe u

instance schemeModulesMonoidalPreadditive (X : Scheme.{u}) :
    MonoidalPreadditive X.Modules :=
  TauCeti.monoidalPreadditive_of_monoidalClosed X.Modules

/-- Finite local freeness supplies an actual dual via the proved
dual-tensor comparison for module sheaves. -/
def schemeFiniteLocallyFreeHasLeftDual {X : Scheme.{u}} (M : X.Modules)
    [M.IsLocallyFree] [M.IsFiniteType] : HasLeftDual M where
  leftDual := (ihom M).obj (𝟙_ X.Modules)
  exact := TauCeti.exactPairingOfIsIsoDualTensorIhom

end ToricPower
