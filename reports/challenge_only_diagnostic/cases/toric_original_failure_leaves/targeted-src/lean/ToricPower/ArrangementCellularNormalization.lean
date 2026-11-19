module

public import ToricPower.ArrangementCellularDerivedModel
public import ToricPower.ArrangementTopLineNormalization
public import ToricPower.ArrangementCellularTopLineDerived
public import ToricPower.CellularDerivedCoefficientIso

/-! # The original cellular total equals the normalized derived coend -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i) [nonempty : Nonempty fan.cones]
  (regular : fan.IsRegular) {n s : ℕ}
  (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "Cells" => IncidenceObject A
local notation "X" => fan.algebraicRealization
local notation "J" => dualDiagonalLineQuasicoherent fan nonempty regular basis rays
local notation "P₀" => arrangementRightQuasicoherentDiagram fan nonempty regular basis rays
local notation "P" => arrangementRightTopLineDiagram fan nonempty regular basis rays
local notation "H₀" => Cellular.realization ℂ P₀
local notation "H" => Cellular.realization ℂ P
local notation "Φ" => arrangementQuasicoherentCellularRealization fan nonempty regular basis rays
local notation "D" => arrangementBoundaryDivisor fan regular
local notation "T" => CategoryTheory.Equivalence.functor
  (quasicoherentCartierTensorEquivalence (arrangementBoundaryDivisor fan regular))

local instance cellularNormalizationIntegral : IsIntegral X := toricSchemeIntegral fan nonempty
local instance cellularNormalizationBiproducts : HasFiniteBiproducts (QCoh X) :=
  HasFiniteBiproducts.of_hasFiniteProducts
local instance cellularNormalizationTargetDerived : HasDerivedCategory.{1} (QCoh X) :=
  HasDerivedCategory.standard _
local instance cellularNormalizationSourceDerived :
    HasDerivedCategory.{1} (Cells ⥤ ModuleCat.{0} ℂ) := HasDerivedCategory.standard _
/-- The original cellular total is naturally the literal normalized
coend functor. This is an all-unbounded comparison of actual functors. -/
def arrangementCellularDerivedNormalizedIso :
    arrangementCellularDerivedFunctor fan regular basis rays ≅
      arrangementNormalizedDerivedRealization fan regular basis rays :=
  arrangementCellularDerivedTopLineIso fan regular basis rays ≪≫
    Functor.isoWhiskerRight
      (Cellular.finiteConeRealizationCoefficientIso ℂ H (H₀ ⋙ T)
        (arrangementTopLineRealizationNormalizationIso fan regular basis rays) (n+1) ≪≫
      Cellular.finiteConeRealizationPostcomposeIso ℂ H₀ T (n+1))
      (shiftFunctor (DerivedQCoh X) (-(n : ℤ)))

end ToricPower

end

