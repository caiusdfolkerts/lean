module

public import ToricPower.ReconstructionCompletionRawAugmentation
public import ToricPower.ReconstructionCompletionRawTopSquare
public import ToricPower.DiagonalDualScalarExact
public import ToricPower.ReconstructionCompletionMappedAugmentationExact

/-! # The genuine affine rank-one reconstruction

The actual geometric augmentation is compared with the actual diagonal
quotient on every original Hom vector and every arbitrary affine section.
The full diagonal exactness and the genuine affine cover then prove its
quasi-isomorphism in the original quasicoherent category.
-/

@[expose] public noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option quotPrecheck false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open HomologicalComplex TauCeti.Toric ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)
  (σ τ : fan.cones)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "X" => fan.algebraicRealization
local notation "Q" => arrangementDualLeftCartierDiagram fan nonempty regular basis rays
local notation "Qq" => arrangementDualLeftQuasicoherentDiagram fan nonempty regular basis rays
local notation "R" => arrangementDualRightCartierDiagram fan nonempty regular basis rays
local notation "P₀" => arrangementRightQuasicoherentDiagram fan nonempty regular basis rays
local notation "Φ" => arrangementQuasicoherentCellularRealization fan nonempty regular basis rays
local notation "jσ" => fan.affineToricChartι σ
local notation "jτ" => fan.affineToricChartι τ
local notation "Uσ" => fan.affineToricChart σ
local notation "Uτ" => fan.affineToricChart τ
local notation "l" => fan.affineToricOverlapLeft σ τ
local notation "r" => fan.affineToricOverlapRight σ τ
local notation "m" => r ≫ jτ
local notation "W" => fan.affineToricChart (σ ⊓ τ)
local notation "Γσ" => FiniteCover.schemeBaseSections ℂ Uσ ⊤
local notation "ΓW" => FiniteCover.schemeBaseSections ℂ W ⊤
local notation "chart" => diagonalProductChartι fan basis rays σ τ
local notation "Z" => Spec (CommRingCat.of (DiagonalChartRing ℂ A
  (fanConeRaySet fan rays σ) (fanConeRaySet fan rays τ)))
local notation "ΓP" => FiniteCover.schemeBaseSections ℂ Z ⊤
local notation "g" => Spec.map (CommRingCat.ofHom (diagonalChartToIntersection fan basis rays σ τ))
local notation "δ" => toricDiagonal fan
local notation "H" => dualDiagonalTopSheaf fan nonempty regular basis rays
local notation "J" => dualDiagonalLineSheaf fan nonempty regular basis rays
local notation "Jq" => dualDiagonalLineQuasicoherent fan nonempty regular basis rays
local notation "E" => quasicoherentAffineUnitImage jτ
local notation "M" => (Cellular.homDiagram ℂ P₀).obj E
local notation "F" => reconstructionRawSectionFunctor fan σ
local notation "α" => (reconstructionGeometricAugmentation fan nonempty regular basis rays).app E

local instance reconstructionRawAugmentationExactChartAffine (κ : fan.cones) : IsAffineHom (fan.affineToricChartι κ) :=
  toricChartInclusion_isAffineHom fan κ
local instance reconstructionRawAugmentationExactOverlapLeft : IsOpenImmersion l :=
  fan.isOpenImmersion_affineToricOverlapLeft σ τ
local instance reconstructionRawAugmentationExactOverlapRight : IsOpenImmersion r :=
  fan.isOpenImmersion_affineToricOverlapRight σ τ
local instance reconstructionRawAugmentationExactQCohBiproducts : HasFiniteBiproducts (QCoh X) :=
  HasFiniteBiproducts.of_hasFiniteProducts
local instance reconstructionRawAugmentationExactSheafBiproducts : HasFiniteBiproducts (X).Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- The whole original affine reconstruction map is a quasi-isomorphism. -/
def reconstructionRawAugmentation_quasiIso :=
  reconstruction_mappedSingleAugmentation_adjusted_quasiIso F α
    (diagonalDualScalarAugmentation fan nonempty regular basis rays σ τ)
    (reconstructionRawKernelIso fan nonempty regular basis rays σ τ)
    (reconstructionRawEvaluationTargetIso fan nonempty regular basis rays σ τ)
    (reconstructionRawDiagonalTargetIso fan nonempty regular basis rays σ τ)
    ((ΓP).map ((Scheme.Modules.pullback chart).map
      (dualDiagonalTopQuotient fan nonempty regular basis rays)))
    (diagonalDualScalarAugmentation_component fan nonempty regular basis rays σ τ)
    (reconstructionRawTopComponent_square fan nonempty regular basis rays σ τ)
    (diagonalDualScalarAugmentation_quasiIso fan nonempty regular basis rays σ τ)

/-- The original affine section map itself is a quasi-isomorphism. -/
def reconstructionRawMapped_quasiIso :=
  reconstruction_mappedSingleAugmentation_quasiIso F α
    (diagonalDualScalarAugmentation fan nonempty regular basis rays σ τ)
    (reconstructionRawKernelIso fan nonempty regular basis rays σ τ)
    (reconstructionRawEvaluationTargetIso fan nonempty regular basis rays σ τ)
    (reconstructionRawDiagonalTargetIso fan nonempty regular basis rays σ τ)
    ((ΓP).map ((Scheme.Modules.pullback chart).map
      (dualDiagonalTopQuotient fan nonempty regular basis rays)))
    (diagonalDualScalarAugmentation_component fan nonempty regular basis rays σ τ)
    (reconstructionRawTopComponent_square fan nonempty regular basis rays σ τ)
    (diagonalDualScalarAugmentation_quasiIso fan nonempty regular basis rays σ τ)

end ToricPower

end
