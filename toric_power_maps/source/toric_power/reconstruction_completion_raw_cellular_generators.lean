module

public import ToricPower.ReconstructionCompletionRawComplex

/-! # Original generators in the raw affine source comparison

Every Hom coefficient and every affine section remains visible. The
exterior coefficient is the original product of unit-source maps.
-/

@[expose] public noncomputable section

set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory TauCeti.Toric Opposite
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)
  (σ τ : fan.cones)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "C" => IncidenceObject A
local notation "X" => fan.algebraicRealization
local notation "Y" => toricDiagonalProduct fan
local notation "Q" => arrangementDualLeftCartierDiagram fan nonempty regular basis rays
local notation "Qq" => arrangementDualLeftQuasicoherentDiagram fan nonempty regular basis rays
local notation "R" => arrangementDualRightCartierDiagram fan nonempty regular basis rays
local notation "P₀" => arrangementRightQuasicoherentDiagram fan nonempty regular basis rays
local notation "Φ" => arrangementQuasicoherentCellularRealization fan nonempty regular basis rays
local notation "jσ" => fan.affineToricChartι σ
local notation "jτ" => fan.affineToricChartι τ
local notation "Ringσ" => CommRingCat.of (affineCoordinateRing fan.lattice σ.val)
local notation "Ringτ" => CommRingCat.of (affineCoordinateRing fan.lattice τ.val)
local notation "Qσ" => (Q ⋙ Scheme.Modules.pullback jσ) ⋙
  FiniteCover.schemeBaseSections ℂ (Spec Ringσ) ⊤
local notation "Rτ" => (R ⋙ Scheme.Modules.pullback jτ) ⋙
  FiniteCover.schemeBaseSections ℂ (Spec Ringτ) ⊤
local notation "Ring" => CommRingCat.of (DiagonalChartRing ℂ A
  (fanConeRaySet fan rays σ) (fanConeRaySet fan rays τ))
local notation "ΓP" => FiniteCover.schemeBaseSections ℂ (Spec Ring) ⊤
local notation "chart" => diagonalProductChartι fan basis rays σ τ
local notation "Pull" => Scheme.Modules.pullback chart
local notation "K" => diagonalGlobalInternalDualComplex fan nonempty regular basis rays
local notation "F" => reconstructionRawSectionFunctor fan σ
local notation "Ext" => exteriorLabelDiagram fan Q R
local notation "S" => Cellular.covariantCopowerDiagram ℂ Qσ Rτ
local notation "E" => quasicoherentAffineUnitImage jτ
local notation "M" => (Cellular.homDiagram ℂ P₀).obj E
local notation "leftMap" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (diagonalProductFirstCoordinate fan basis rays σ τ)))
local notation "rightMap" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (diagonalProductSecondCoordinate fan basis rays σ τ)))

local instance reconstructionRawCellularGeneratorsQCohBiproducts : HasFiniteBiproducts (QCoh X) :=
  HasFiniteBiproducts.of_hasFiniteProducts
local instance reconstructionRawCellularGeneratorsSheafBiproducts : HasFiniteBiproducts (Y).Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts
local instance reconstructionRawCellularGeneratorsChartAffine (κ : fan.cones) : IsAffineHom (fan.affineToricChartι κ) :=
  toricChartInclusion_isAffineHom fan κ
local instance reconstructionRawCellularGeneratorsCells (q : ℕ) : Fintype (NormalizedCell A q) :=
  Fintype.ofFinite _

/-- The raw affine coefficient comparison retains each original vector/cell map. -/
@[reassoc]
theorem reconstructionRawCellularCoefficient_generator
    (D : C ⥤ ModuleCat ℂ) (q : ℕ) (d : NormalizedCell A q) (h : D.obj ⟨q,d⟩) :
    (F).map (Cellular.vectorCopowerInclusion ℂ ((Qq).obj ⟨q,d⟩) (D.obj ⟨q,d⟩) h ≫
        arrangementCellularCochainInclusion A ℂ (Cellular.covariantCopowerDiagram ℂ Qq D) q d) ≫
      (reconstructionRawCellularCoefficientComponents fan nonempty regular basis rays σ D).hom.f q =
      Cellular.vectorCopowerInclusion ℂ ((Qσ).obj ⟨q,d⟩) (D.obj ⟨q,d⟩) h ≫
        arrangementCellularCochainInclusion A ℂ (Cellular.covariantCopowerDiagram ℂ Qσ D) q d := by
  rw [reconstructionRawCellularCoefficientComponents_eq]
  simpa only [Iso.refl_hom, NatTrans.id_app, Category.id_comp] using
    cellularRealizationCoefficientObjectIso_generator A ℂ F Qq Qσ (Iso.refl _) D q d h


end ToricPower

end
