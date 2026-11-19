module

public import ToricPower.ReconstructionCompletionRawExteriorGenerators
public import ToricPower.ReconstructionCompletionRawPointwiseSquare
public import ToricPower.ReconstructionCompletionRawTopRetraction

/-! # The genuine affine rank-one reconstruction

The actual geometric augmentation is compared with the actual diagonal
quotient on every original Hom vector and every arbitrary affine section.
The full diagonal exactness and the genuine affine cover then prove its
quasi-isomorphism in the original quasicoherent category.
-/

@[expose] public noncomputable section

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
local notation "Qσ" => (Q ⋙ Scheme.Modules.pullback jσ) ⋙
  FiniteCover.schemeBaseSections ℂ
    (Spec (CommRingCat.of (affineCoordinateRing fan.lattice σ.val))) ⊤
local notation "Rτ" => (R ⋙ Scheme.Modules.pullback jτ) ⋙
  FiniteCover.schemeBaseSections ℂ
    (Spec (CommRingCat.of (affineCoordinateRing fan.lattice τ.val))) ⊤
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

local instance reconstructionRawTopPointwiseChartAffine (κ : fan.cones) : IsAffineHom (fan.affineToricChartι κ) :=
  toricChartInclusion_isAffineHom fan κ
local instance reconstructionRawTopPointwiseOverlapLeft : IsOpenImmersion l :=
  fan.isOpenImmersion_affineToricOverlapLeft σ τ
local instance reconstructionRawTopPointwiseOverlapRight : IsOpenImmersion r :=
  fan.isOpenImmersion_affineToricOverlapRight σ τ
local instance reconstructionRawTopPointwiseQCohBiproducts : HasFiniteBiproducts (QCoh X) :=
  HasFiniteBiproducts.of_hasFiniteProducts
local instance reconstructionRawTopPointwiseSheafBiproducts : HasFiniteBiproducts (X).Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- The actual original top cell satisfies the scalar section square,
with its original Hom coefficient and every original chart section. -/
def reconstructionRawTopPointwise (d : NormalizedCell A n)
    (h : (M).obj ⟨n,d⟩) (s₀ : (Qσ).obj ⟨n,d⟩) :=
  reconstructionRawPointwise_square fan nonempty regular basis rays σ τ
    ((Q).obj ⟨n,d⟩) ((R).obj ⟨n,d⟩)
    (reconstructionAffineCoefficientUnit fan nonempty regular basis rays τ ⟨n,d⟩ h)
    (reconstructionUnderlyingTopCell fan nonempty regular basis rays d)
    (reconstructionDiagonalExternalTop fan nonempty regular basis rays d)
    (reconstructionUnderlyingTopCell_retraction fan nonempty regular basis rays d)
    s₀ ((reconstructionAffineCoefficientIso fan nonempty regular basis rays τ).hom.app ⟨n,d⟩ h)
    ((ΓP).map ((diagonalExteriorChartDiagramIso fan nonempty regular basis rays σ τ).inv.app ⟨n,d⟩)
      ((diagonalAffineExteriorSectionDiagramIso fan nonempty regular basis rays σ τ).hom.app ⟨n,d⟩
        (Cellular.vectorCopowerInclusion ℂ ((Qσ).obj ⟨n,d⟩) ((Rτ).obj ⟨n,d⟩)
          ((reconstructionAffineCoefficientIso fan nonempty regular basis rays τ).hom.app ⟨n,d⟩ h) s₀)))
    (reconstructionAffineCoefficientIso_unit fan nonempty regular basis rays τ ⟨n,d⟩ h)
    (reconstructionRawExterior_unit fan nonempty regular basis rays σ τ ⟨n,d⟩ s₀
      ((reconstructionAffineCoefficientIso fan nonempty regular basis rays τ).hom.app ⟨n,d⟩ h))

end ToricPower

end
