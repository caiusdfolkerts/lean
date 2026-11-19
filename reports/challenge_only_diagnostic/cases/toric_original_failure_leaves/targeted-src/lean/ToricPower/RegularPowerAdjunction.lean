module

public import ToricPower.RegularPowerTrace

/-!
# The two actual adjunctions for a smooth affine power map

The residue trace proved perfect in `RegularPowerTrace` identifies actual
extension and coextension of scalars. Thus restriction of scalars is both
a right adjoint and a left adjoint of extension, without a hypothesis on
the coefficient module. The chosen affine trivialization of the relative
dualizing line is encoded by the top-residue trace.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory ModuleCat MonoidAlgebra

namespace ToricPower

universe u

variable (k : Type u) [CommRing k] (ell : ℕ)
  (α β : Type u) [Fintype α] [Fintype β]

local notation "S" => MonoidAlgebra k (Multiplicative (RegularExponents α β))
local notation "φ" => mapDomainRingHom k (exponentPower ell (RegularExponents α β))

/-- The actual extension/coextension comparison, for every coefficient module. -/
def regularPowerExtendCoextendIso (positive : 0 < ell) :
    ModuleCat.extendScalars.{u} φ ≅ ModuleCat.coextendScalars φ := by
  letI : Algebra S S := (φ).toAlgebra
  letI : Module S S := (φ).toModule
  letI : Module.Finite S S := Module.Finite.of_basis (regularPowerBasis k ell α β positive)
  letI : Module.Free S S := Module.Free.of_basis (regularPowerBasis k ell α β positive)
  exact traceExtendCoextendIso (regularPowerTrace ell α β positive k)
    (regularPowerTrace_perfect ell α β positive k)

/-- The actual finite-duality adjunction in a polynomial--Laurent chart. -/
def regularPowerRestrictExtendAdjunction (positive : 0 < ell) :
    ModuleCat.restrictScalars.{u} φ ⊣ ModuleCat.extendScalars φ :=
  (ModuleCat.restrictCoextendScalarsAdj φ).ofNatIsoRight
    (regularPowerExtendCoextendIso k ell α β positive).symm

end ToricPower

end
