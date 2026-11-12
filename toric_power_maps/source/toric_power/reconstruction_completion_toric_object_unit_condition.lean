module

public import ToricPower.ReconstructionCompletionRankOne
public import ToricPower.ReconstructionCompletionObjectFamilyCondition

/-! # The original toric rank-one family in its inferred complex category -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open TauCeti.Toric ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i) [nonempty : Nonempty fan.cones]
  (regular : fan.IsRegular) {n s : ℕ}
  (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local instance reconstructionToricObjectUnitChart (cone : fan.cones) :
    IsAffineHom (fan.affineToricChartι cone) := toricChartInclusion_isAffineHom fan cone

/-- The checked rank-one theorem, packaged with its entire original
complex presentation inferred from the genuine augmentation. -/
def reconstructionGeometricObjectUnitCondition :=
  reconstructionObjectFamilyCondition_of_quasiIso
    (fun cone : fan.cones => quasicoherentAffineUnitImage (fan.affineToricChartι cone))
    (reconstructionGeometricAugmentation fan nonempty regular basis rays)
    (reconstructionAffineUnit_quasiIso fan nonempty regular basis rays)

end ToricPower

end
