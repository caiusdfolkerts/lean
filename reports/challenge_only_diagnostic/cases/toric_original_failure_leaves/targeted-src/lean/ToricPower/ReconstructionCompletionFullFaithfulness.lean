module

public import ToricPower.ReconstructionCompletionToricUnitCondition
public import ToricPower.ReconstructionCompletionToricRankOneCondition
public import ToricPower.ReconstructionCompletionToricTopCondition

/-! # Full faithfulness of the actual normalized derived Hom

The actual affine rank-one calculation extends to arbitrary modules,
unbounded affine complexes, and the full finite affine coresolution.
The genuine geometric augmentation then gives a natural reconstruction
isomorphism.  The original normalized adjunction proves full faithfulness.
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

local instance reconstructionFullFaithfulnessIntegral : IsIntegral X :=
  toricSchemeIntegral fan nonempty
local instance reconstructionFullFaithfulnessBiproducts : HasFiniteBiproducts (QCoh X) :=
  HasFiniteBiproducts.of_hasFiniteProducts
local instance reconstructionFullFaithfulnessChart (cone : fan.cones) :
    IsAffineHom (fan.affineToricChartι cone) := toricChartInclusion_isAffineHom fan cone
local instance reconstructionFullFaithfulnessRange (cone : fan.cones) :
    IsAffineHom (fan.affineToricChartι cone).opensRange.ι :=
  toricDerivedChartOpen_isAffineHom fan cone
local instance reconstructionFullFaithfulnessTargetDerived : HasDerivedCategory.{1} (QCoh X) :=
  HasDerivedCategory.standard _
local instance reconstructionFullFaithfulnessSourceDerived :
    HasDerivedCategory.{1} (Cells ⥤ ModuleCat.{0} ℂ) := HasDerivedCategory.standard _

/-- The actual rank-one geometric theorem gives the original affine
comparison on every unbounded direct-image complex. -/
def reconstructionGeometricAffineTopCondition :=
  reconstructionGeometricAffineTopConditionOfRankOne fan regular basis rays
    (reconstructionGeometricAffineUnitCondition fan regular basis rays)

/-- Genuine reconstruction for every unbounded quasicoherent derived
object on every nonempty smooth finite fan. -/
def reconstructionGeometricDerivedIso :=
  reconstructionGeometricDerivedIsoOfTopCondition fan regular basis rays
    (reconstructionGeometricAffineTopCondition fan regular basis rays)

/-- The paper's actual normalized right adjoint is fully faithful on
the entire unbounded derived category. All geometric inputs are proved. -/
def arrangementNormalizedDerivedHom_fullyFaithful :
    (arrangementNormalizedDerivedHom fan regular basis rays).FullyFaithful :=
  arrangementNormalizedDerivedHom_fullyFaithful_of_topCondition fan regular basis rays
    (reconstructionGeometricAffineTopCondition fan regular basis rays)

end ToricPower

end
