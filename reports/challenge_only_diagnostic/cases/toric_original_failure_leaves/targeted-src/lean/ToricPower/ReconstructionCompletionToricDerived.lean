module

public import ToricPower.ReconstructionCompletionToricComparison
public import ToricPower.ReconstructionCompletionSchemeAffineDerivedBridge
public import ToricPower.ReconstructionCompletionNormalizedDerivedInterface

/-! # The genuine toric reconstruction comparison in the derived category

The geometric top quotient is retained throughout totalization,
finite affine cone closure, and localization.  This file isolates the
derived step from its affine rank-one calculation.
-/

@[expose] public noncomputable section

set_option maxHeartbeats 400000
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
local notation "C" => affineConeCoresolution (toricDerivedChartOpen fan) (toricDerivedChartList fan)
local notation "L" => reconstructionNormalizedDerivedInterface fan regular basis rays
local notation "R" => arrangementToricDerivedHom fan nonempty regular basis rays
local notation "E" => arrangementNormalizationEquivalence fan regular (n := n)

local instance reconstructionDerivedIsoIntegral : IsIntegral X := toricSchemeIntegral fan nonempty
local instance reconstructionDerivedIsoBiproducts : HasFiniteBiproducts (QCoh X) :=
  HasFiniteBiproducts.of_hasFiniteProducts
local instance reconstructionDerivedIsoTargetDerived : HasDerivedCategory.{1} (QCoh X) :=
  HasDerivedCategory.standard _
local instance reconstructionDerivedIsoSourceDerived :
    HasDerivedCategory.{1} (Cells ⥤ ModuleCat.{0} ℂ) := HasDerivedCategory.standard _

/-- The original geometric augmentation becomes a natural derived
reconstruction isomorphism after the actual affine calculation. -/
def reconstructionGeometricDerivedIsoOfAffineComparison :=
  schemeDerivedReconstructionOfAffineComparison X (toricDerivedChartOpen fan)
    H Φ (tensorLeft J)
    n (n + 1) (Nat.lt_succ_self n)
    (reconstructionGeometricAugmentation fan nonempty regular basis rays)
    R L (E).functor
    (reconstructionNormalizedInterfaceCellularFactors fan regular basis rays)
    (toricDerivedChartList fan)
    (reconstructionDerivedSourceFactors fan regular basis rays)
    (reconstructionDerivedTargetFactors fan regular basis rays)

end ToricPower

end
