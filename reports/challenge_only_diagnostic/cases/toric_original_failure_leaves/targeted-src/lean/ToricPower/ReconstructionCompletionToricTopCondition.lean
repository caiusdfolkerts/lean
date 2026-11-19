module

public import ToricPower.ReconstructionCompletionToricDerived
public import ToricPower.ReconstructionCompletionToricFullFaithfulness
public import ToricPower.ReconstructionCompletionLocalConditionTransport

/-! # Derived reconstruction from the original affine top condition

The original top comparison and the named finite-total condition are
identified before invoking the actual derived reconstruction.
-/

@[expose] public noncomputable section

set_option maxHeartbeats 800000
set_option quotPrecheck false
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
local notation "α" => reconstructionGeometricAugmentation fan nonempty regular basis rays
local notation "U" => fun cone : fan.cones => (fan.affineToricChartι cone).opensRange

local instance reconstructionTopConditionIntegral : IsIntegral X :=
  toricSchemeIntegral fan nonempty
local instance reconstructionTopConditionBiproducts : HasFiniteBiproducts (QCoh X) :=
  HasFiniteBiproducts.of_hasFiniteProducts
local instance reconstructionTopConditionRange (cone : fan.cones) :
    IsAffineHom (fan.affineToricChartι cone).opensRange.ι :=
  toricDerivedChartOpen_isAffineHom fan cone
local instance reconstructionTopConditionTargetDerived : HasDerivedCategory.{1} (QCoh X) :=
  HasDerivedCategory.standard _
local instance reconstructionTopConditionSourceDerived :
    HasDerivedCategory.{1} (Cells ⥤ ModuleCat.{0} ℂ) := HasDerivedCategory.standard _

/-- The actual named affine top condition gives genuine derived
reconstruction, with its original functors and augmentation. -/
def reconstructionGeometricDerivedIsoOfTopCondition
    (topCondition : schemeAffineTopComparisonCondition X U H Φ (tensorLeft J)
      n (n + 1) (Nat.lt_succ_self n) α) :=
  reconstructionGeometricDerivedIsoOfAffineComparison fan regular basis rays
    (schemeAffineLocalCondition_of_topComparison X U H Φ (tensorLeft J)
      n (n + 1) (Nat.lt_succ_self n) α topCondition)

/-- The exact actual normalized right adjoint is fully faithful whenever
the original affine top condition is supplied. -/
def arrangementNormalizedDerivedHom_fullyFaithful_of_topCondition
    (topCondition : schemeAffineTopComparisonCondition X U H Φ (tensorLeft J)
      n (n + 1) (Nat.lt_succ_self n) α) :
    (arrangementNormalizedDerivedHom fan regular basis rays).FullyFaithful :=
  arrangementNormalizedDerivedHom_fullyFaithful_of_reconstruction fan regular basis rays
    (reconstructionGeometricDerivedIsoOfTopCondition fan regular basis rays topCondition)

end ToricPower

end
