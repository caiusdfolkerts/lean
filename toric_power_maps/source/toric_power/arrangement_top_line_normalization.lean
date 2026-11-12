module

public import ToricPower.ArrangementRepresentedQuasicoherentAugmentation
public import ToricPower.DiagonalBoundaryNormalization
public import ToricPower.MappedCellularRealizationIso
public import ToricPower.QuasicoherentTensorColimits
public import ToricPower.QuasicoherentTensorLinear
public import ToricPower.ArrangementNormalizedAdjunction

/-! # The actual top-line tensor and the paper's boundary normalization -/

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

local instance topLineNormalizationIntegral : IsIntegral X := toricSchemeIntegral fan nonempty
local instance topLineNormalizationBiproducts : HasFiniteBiproducts (QCoh X) :=
  HasFiniteBiproducts.of_hasFiniteProducts
local instance topLineNormalizationTargetDerived : HasDerivedCategory.{1} (QCoh X) :=
  HasDerivedCategory.standard _
local instance topLineNormalizationSourceDerived :
    HasDerivedCategory.{1} (Cells ⥤ ModuleCat.{0} ℂ) := HasDerivedCategory.standard _
/-- The original proved boundary-line map, lifted in the ordinary
full quasicoherent subcategory. -/
def arrangementBoundaryTopLineQuasicoherentIso :
    (⟨(D).sheaf, inferInstance⟩ : QCoh X) ≅ J :=
  ObjectProperty.isoMk (SheafOfModules.isQuasicoherent (X).ringCatSheaf)
    (dualDiagonalBoundaryLineIso fan nonempty regular basis rays)

/-- The actual right tensor by the top line is the actual boundary
Cartier tensor equivalence, through the genuine symmetry. -/
def arrangementTopLineTensorNormalizationIso : tensorRight J ≅ T := by
  let B : QCoh X := ⟨(D).sheaf, inferInstance⟩
  let e := arrangementBoundaryTopLineQuasicoherentIso fan regular basis rays
  exact (tensoringRight (QCoh X)).mapIso e.symm ≪≫
    (BraidedCategory.tensorLeftIsoTensorRight B).symm ≪≫
      Functor.fullyFaithfulCancelRight (quasicoherentInclusion X) (Iso.refl _)

/-- The coefficient comparison is the actual mapped-coend isomorphism,
followed by the proved geometric normalization. -/
def arrangementTopLineRealizationNormalizationIso : H ≅ H₀ ⋙ T :=
  (Cellular.mappedRealizationIso ℂ (tensorRight J) P₀).symm ≪≫
    Functor.isoWhiskerLeft H₀ (arrangementTopLineTensorNormalizationIso fan regular basis rays)

end ToricPower

end
