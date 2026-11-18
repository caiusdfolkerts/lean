module

public import ToricPower.ArrangementCellularAffineSections
public import ToricPower.CellularRealizationCoefficientIso

/-!
# Naturality of actual affine cellular realization

These are isomorphisms of the complete realization functors, not merely
comparisons of their values. All maps of arbitrary scalar diagrams are
retained, including the source maps between genuine representables.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "X" => fan.algebraicRealization
local notation "Q" => arrangementDualLeftQuasicoherentDiagram fan nonempty regular basis rays

local instance : HasFiniteBiproducts (QCoh X) := HasFiniteBiproducts.of_hasFiniteProducts
local instance : HasFiniteBiproducts (X).Modules := HasFiniteBiproducts.of_hasFiniteProducts

/-- The genuine affine comparison is natural in the entire input
diagram, without finite-dimensionality or finite support assumptions. -/
def arrangementCellularAffineFunctorIso (σ : fan.cones) :
    arrangementQuasicoherentCellularRealization fan nonempty regular basis rays ⋙
        (arrangementAffineSectionFunctor fan σ).mapHomologicalComplex (.up ℕ) ≅
      arrangementCellularRealization A ℂ
        (reflectedLaurentDiagram A (fanConeRaySet fan rays σ) ℂ) :=
  cellularRealizationCoefficientIso A ℂ (arrangementAffineSectionFunctor fan σ)
    Q (reflectedLaurentDiagram A (fanConeRaySet fan rays σ) ℂ)
    (reflectedToricSectionsDiagramIso fan nonempty regular basis rays σ).symm

/-- The full actual quasicoherent construction forgets to the original
module-sheaf construction naturally in every input map. -/
def arrangementCellularUnderlyingFunctorIso :
    arrangementQuasicoherentCellularRealization fan nonempty regular basis rays ⋙
        (quasicoherentInclusion X).mapHomologicalComplex (.up ℕ) ≅
      arrangementCellularSheafRealization fan nonempty regular basis rays :=
  cellularRealizationCoefficientIso A ℂ (quasicoherentInclusion X)
    Q (arrangementDualLeftCartierDiagram fan nonempty regular basis rays) (Iso.refl _)

end ToricPower

end
