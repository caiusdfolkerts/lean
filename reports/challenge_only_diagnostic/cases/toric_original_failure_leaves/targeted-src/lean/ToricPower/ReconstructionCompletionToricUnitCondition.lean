module

public import ToricPower.ReconstructionCompletionToricObjectUnitCondition

/-! # The proved original affine unit family for the toric augmentation

The genuine rank-one theorem is packaged in the shared named predicate
using the original chart schemes and the original geometric map.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open TauCeti.Toric ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i) [nonempty : Nonempty fan.cones]
  (regular : fan.IsRegular) {n s : ℕ}
  (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local instance reconstructionToricUnitConditionChart (cone : fan.cones) :
    IsAffineHom (fan.affineToricChartι cone) := toricChartInclusion_isAffineHom fan cone

/-- The original geometric augmentation satisfies the exact named
rank-one condition on every original toric affine chart. -/
def reconstructionGeometricAffineUnitCondition :=
  reconstructionAffineUnitFamilyCondition_of_objectFamily
    (fun cone : fan.cones => fan.affineToricChart cone) fan.algebraicRealization
    (fun cone => fan.affineToricChartι cone)
    (reconstructionGeometricAugmentation fan nonempty regular basis rays)
    (reconstructionGeometricObjectUnitCondition fan regular basis rays)

end ToricPower

end
