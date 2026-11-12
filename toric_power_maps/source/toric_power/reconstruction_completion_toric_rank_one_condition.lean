module

public import ToricPower.ReconstructionCompletionGeometricAugmentation
public import ToricPower.ToricDerivedAffineCover
public import ToricPower.ReconstructionCompletionNamedUnitFamilyCondition

/-! # The actual affine rank-one family gives the reconstruction condition

This isolates the extension of the original geometric augmentation to
all unbounded image-open complexes before supplying its rank-one proof.
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

local notation "X" => fan.algebraicRealization
local notation "P₀" => arrangementRightQuasicoherentDiagram fan nonempty regular basis rays
local notation "H" => Cellular.homDiagram ℂ P₀
local notation "Φ" => arrangementQuasicoherentCellularRealization fan nonempty regular basis rays
local notation "J" => dualDiagonalLineQuasicoherent fan nonempty regular basis rays
local notation "α" => reconstructionGeometricAugmentation fan nonempty regular basis rays
local notation "U" => fun cone : fan.cones => (fan.affineToricChartι cone).opensRange

local instance reconstructionRankOneConditionIntegral : IsIntegral X :=
  toricSchemeIntegral fan nonempty
local instance reconstructionRankOneConditionBiproducts : HasFiniteBiproducts (QCoh X) :=
  HasFiniteBiproducts.of_hasFiniteProducts
local instance reconstructionRankOneConditionChart (cone : fan.cones) :
    IsAffineHom (fan.affineToricChartι cone) := toricChartInclusion_isAffineHom fan cone
local instance reconstructionRankOneConditionRange (cone : fan.cones) :
    IsAffineHom (fan.affineToricChartι cone).opensRange.ι :=
  toricDerivedChartOpen_isAffineHom fan cone

/-- The original rank-one premise, with no derived or finite-generation
assumption on the complexes to which it will be extended. -/
def reconstructionAffineUnitComparisonCondition : Prop :=
  reconstructionAffineUnitFamilyCondition
    (fun cone : fan.cones => fan.affineToricChart cone) X
    (fun cone => fan.affineToricChartι cone) α

/-- The genuine rank-one family extends to the exact named all-open
unbounded comparison condition. -/
def reconstructionGeometricAffineTopConditionOfRankOne
    (rankOne : reconstructionAffineUnitComparisonCondition fan regular basis rays) :=
  letI : TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X (J).obj :=
    dualDiagonalLineSheaf_isInvertible fan nonempty regular basis rays
  reconstructionNamedUnitFamily_topComparisonCondition
    (fun cone : fan.cones => affineCoordinateRing fan.lattice cone.1)
    X (fun cone => fan.affineToricChartι cone) P₀ (fun _ => inferInstance) Φ J n α
    (arrangementQuasicoherentCellularRealization_isZero_X_above
      fan nonempty regular basis rays)
    (toricDerivedChartOpen fan) (toricDerivedChartOpen_covers fan).iSup_eq_top
    (fun cone => isAffineOpen_opensRange (fan.affineToricChartι cone))
    rankOne (n + 1) (Nat.lt_succ_self n)

end ToricPower

end
