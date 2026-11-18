module

public import ToricPower.ReconstructionCompletionRawCellularGenerators
public import ToricPower.ReconstructionCompletionRawHomGenerators
public import ToricPower.ReconstructionCompletionRawKernelComponents
public import ToricPower.ReconstructionCompletionGeneratorChain

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

local instance reconstructionRawKernelGeneratorsQCohBiproducts : HasFiniteBiproducts (QCoh X) :=
  HasFiniteBiproducts.of_hasFiniteProducts
local instance reconstructionRawKernelGeneratorsSheafBiproducts : HasFiniteBiproducts (Y).Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts
local instance reconstructionRawKernelGeneratorsChartAffine (κ : fan.cones) : IsAffineHom (fan.affineToricChartι κ) :=
  toricChartInclusion_isAffineHom fan κ
local instance reconstructionRawKernelGeneratorsCells (q : ℕ) : Fintype (NormalizedCell A q) :=
  Fintype.ofFinite _

/-- The full comparison retains the actual affine coefficient of the original Hom vector. -/
def reconstructionRawKernelIso_generator (q : ℕ) (d : NormalizedCell A q)
    (h : (M).obj ⟨q,d⟩) :=
  reconstruction_generator_chain_of_components
    (reconstructionRawKernelIso_components fan nonempty regular basis rays σ τ q)
    (reconstructionRawCellularCoefficient_generator fan nonempty regular basis rays σ M q d h)
    (reconstructionRawHomCochainIso_generator fan nonempty regular basis rays σ τ q d h)

/-- Postcomposition retains the same explicit source presentation. -/
def reconstructionRawKernelIso_generator_assoc (q : ℕ) (d : NormalizedCell A q)
    (h : (M).obj ⟨q,d⟩) {Z : ModuleCat ℂ}
    (post : (((ΓP).mapHomologicalComplex (.up ℕ)).obj
      (((Pull).mapHomologicalComplex (.up ℕ)).obj K)).X q ⟶ Z) :=
  reconstruction_generator_postcompose _ _ _ _
    (reconstructionRawKernelIso_generator fan nonempty regular basis rays σ τ q d h) post


end ToricPower

end
