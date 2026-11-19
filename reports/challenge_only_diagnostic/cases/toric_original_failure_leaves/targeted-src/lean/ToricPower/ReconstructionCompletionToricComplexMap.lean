module

public import ToricPower.ReconstructionCompletionGeometricAugmentation
public import ToricPower.ReconstructionCompletionFactors

/-! # The genuine toric reconstruction comparison in the derived category

The geometric top quotient is retained throughout totalization,
finite affine cone closure, and localization.  This file isolates the
derived step from its affine rank-one calculation.
-/

@[expose] public noncomputable section

set_option maxHeartbeats 100000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open TauCeti.Toric ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i) [nonempty : Nonempty fan.cones]
  (regular : fan.IsRegular) {n s : ℕ}
  (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "Cells" => IncidenceObject A
local notation "X" => fan.algebraicRealization
local notation "P₀" => arrangementRightQuasicoherentDiagram fan nonempty regular basis rays
local notation "H" => Cellular.homDiagram ℂ P₀
local notation "Φ" => arrangementQuasicoherentCellularRealization fan nonempty regular basis rays
local notation "J" => dualDiagonalLineQuasicoherent fan nonempty regular basis rays

local instance reconstructionComplexMapIntegral : IsIntegral X := toricSchemeIntegral fan nonempty
local instance reconstructionComplexMapBiproducts : HasFiniteBiproducts (QCoh X) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- The actual unbounded finite total of the genuine geometric top map. -/
def reconstructionGeometricComplexComparison :=
  FunctorTotal.reconstructionComplexTopComparison H Φ (tensorLeft J)
    n (n + 1) (Nat.lt_succ_self n)
    (reconstructionGeometricAugmentation fan nonempty regular basis rays)

end ToricPower

end
