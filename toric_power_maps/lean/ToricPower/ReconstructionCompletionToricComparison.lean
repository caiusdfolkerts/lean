module

public import ToricPower.ReconstructionCompletionToricComplexMap
public import ToricPower.ReconstructionCompletionFiniteAffine
public import ToricPower.ReconstructionCompletionToricFactors

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
local notation "C" => affineConeCoresolution (toricDerivedChartOpen fan) (toricDerivedChartList fan)
local notation "L" => arrangementNormalizedDerivedRealization fan regular basis rays
local notation "R" => arrangementToricDerivedHom fan nonempty regular basis rays
local notation "E" => arrangementNormalizationEquivalence fan regular (n := n)

local instance reconstructionDerivedIntegral : IsIntegral X := toricSchemeIntegral fan nonempty
local instance reconstructionDerivedBiproducts : HasFiniteBiproducts (QCoh X) :=
  HasFiniteBiproducts.of_hasFiniteProducts
local instance reconstructionDerivedTargetDerived : HasDerivedCategory.{1} (QCoh X) :=
  HasDerivedCategory.standard _
local instance reconstructionDerivedSourceDerived :
    HasDerivedCategory.{1} (Cells ⥤ ModuleCat.{0} ℂ) := HasDerivedCategory.standard _

/-- The finite cone closure uses the actual affine comparison on
unbounded complexes, and retains the original comparison on the result. -/
def reconstructionGeometricComplexComparison_coresolution_quasiIso
    (localQuasiIso : _)
    (K : CochainComplex (QCoh X) ℤ) :=
  affineCoresolution_reconstructionComparison_quasiIso
    (toricDerivedChartOpen fan) H Φ (tensorLeft J) n (n + 1) (Nat.lt_succ_self n)
    (reconstructionGeometricAugmentation fan nonempty regular basis rays) L
    (reconstructionCellularDerivedFactors fan regular basis rays) localQuasiIso
    (toricDerivedChartList fan) K

end ToricPower

end
