module

public import ToricPower.ArrangementRepresentedTopExact
public import ToricPower.ArrangementCellularAugmentation
public import ToricPower.ArrangementCellularDerivedModel
public import ToricPower.ArrangementDerivedRealization
public import ToricPower.FiniteCellularSealedDerivedComparison

/-! # The actual top-quotient comparison on every unbounded input -/

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

local instance cellularTopLineDerivedIntegral : IsIntegral X := toricSchemeIntegral fan nonempty
local instance cellularTopLineDerivedBiproducts : HasFiniteBiproducts (QCoh X) :=
  HasFiniteBiproducts.of_hasFiniteProducts
local instance cellularTopLineDerivedTargetDerived : HasDerivedCategory.{1} (QCoh X) :=
  HasDerivedCategory.standard _
local instance cellularTopLineDerivedSourceDerived :
    HasDerivedCategory.{1} (Cells ⥤ ModuleCat.{0} ℂ) := HasDerivedCategory.standard _
local instance cellularTopLineDerivedDetectorLimits (σ : fan.cones) :
    PreservesFiniteLimits (arrangementAffineSectionFunctor fan σ) :=
  (FiniteCover.schemeBaseSections_exact ℂ X (fan.affineToricChartι σ).opensRange
    (isAffineOpen_opensRange (fan.affineToricChartι σ))).1
local instance cellularTopLineDerivedDetectorColimits (σ : fan.cones) :
    PreservesFiniteColimits (arrangementAffineSectionFunctor fan σ) :=
  (FiniteCover.schemeBaseSections_exact ℂ X (fan.affineToricChartι σ).opensRange
    (isAffineOpen_opensRange (fan.affineToricChartι σ))).2

/-- The genuine finite-resolution comparison, with every geometric
hypothesis discharged by the original represented augmentation. -/
def arrangementCellularDerivedTopLineIso :
    arrangementCellularDerivedFunctor fan regular basis rays ≅
      arrangementDerivedRealization A ℂ P ⋙
        shiftFunctor (DerivedQCoh X) (-(n : ℤ)) := by
  unfold arrangementCellularDerivedFunctor arrangementDerivedRealization
  apply FunctorTotal.sealedDerivedTotalLeftDerivedIso ℂ Φ H n (n+1) (Nat.lt_succ_self n)
    (arrangementCellularAugmentation fan nonempty regular basis rays)
    (arrangementAffineSectionFunctor fan)
  · intro M zero
    exact quasicoherent_isZero_of_affineSections ℂ X
      (fun σ : fan.cones => (fan.affineToricChartι σ).opensRange)
      fan.affineToricOpenCover.isOpenCover_opensRange
      (fun σ => isAffineOpen_opensRange (fan.affineToricChartι σ)) M zero
  · exact arrangementCellularAugmentation_epi fan nonempty regular basis rays
      (arrangementRepresentedTopAugmentation_quasiIso fan nonempty regular basis rays)
  · intro M projective σ
    letI := projective
    letI := arrangementCellularAugmentation_projective_quasiIso fan nonempty regular basis rays
      (arrangementRepresentedTopAugmentation_quasiIso fan nonempty regular basis rays) M
    infer_instance
  · intro M
    exact arrangementQuasicoherentCellularRealization_isZero_X_above
      fan nonempty regular basis rays M (n+1) (Nat.lt_succ_self n)
  · exact Iso.refl _
  · exact arrangementFiniteConeResolution_quasiIso A ℂ

end ToricPower

end
