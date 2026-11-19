module

public import ToricPower.ArrangementCellularNormalization
public import ToricPower.ReconstructionCompletionCoresolutionFactors
public import ToricPower.ReconstructionCompletionFactorComposition

/-! # The exact toric reconstruction factors

The original affine Hom model, the original cellular total, and the
proved boundary-line identification give the two ordinary factorizations
used to localize the geometric reconstruction comparison.
-/

@[expose] public noncomputable section

set_option maxHeartbeats 800000
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
local notation "C" => affineConeCoresolution (toricDerivedChartOpen fan) (toricDerivedChartList fan)
local notation "L" => arrangementNormalizedDerivedRealization fan regular basis rays
local notation "R" => arrangementToricDerivedHom fan nonempty regular basis rays
local notation "E" => arrangementNormalizationEquivalence fan regular (n := n)
local notation "T" => CategoryTheory.Equivalence.functor
  (quasicoherentCartierTensorEquivalence (arrangementBoundaryDivisor fan regular))

local instance reconstructionFactorsIntegral : IsIntegral X := toricSchemeIntegral fan nonempty
local instance reconstructionFactorsBiproducts : HasFiniteBiproducts (QCoh X) :=
  HasFiniteBiproducts.of_hasFiniteProducts
local instance reconstructionFactorsTargetDerived : HasDerivedCategory.{1} (QCoh X) :=
  HasDerivedCategory.standard _
local instance reconstructionFactorsSourceDerived :
    HasDerivedCategory.{1} (Cells ⥤ ModuleCat.{0} ℂ) := HasDerivedCategory.standard _

local instance reconstructionFactorsHomLimits (cone : fan.cones) :
    PreservesFiniteLimits
      (quasicoherentOpenLocalization (toricDerivedChartOpen fan cone).ι ⋙ H) :=
  (toricDerivedLabelLocalExact fan P₀ (fun _ => inferInstance) cone).1
local instance reconstructionFactorsHomColimits (cone : fan.cones) :
    PreservesFiniteColimits
      (quasicoherentOpenLocalization (toricDerivedChartOpen fan cone).ι ⋙ H) :=
  (toricDerivedLabelLocalExact fan P₀ (fun _ => inferInstance) cone).2

/-- The normalized derived realization is represented by the original
finite signed cellular total. -/
def reconstructionCellularDerivedFactors :
    DerivedCategory.Q ⋙ L ≅ FunctorTotal.functor Φ (n + 1) ⋙ DerivedCategory.Q := by
  refine Functor.isoWhiskerLeft DerivedCategory.Q
    (arrangementCellularDerivedNormalizedIso fan regular basis rays).symm ≪≫ ?_
  unfold arrangementCellularDerivedFunctor
  exact complexFunctorDerivedFactors
    (arrangementCellularTotalFunctor fan nonempty regular basis rays) _

/-- The original right adjoint is the actual Hom diagram of the
actual finite affine coresolution. -/
def reconstructionOriginalHomFactors :
    DerivedCategory.Q ⋙ R ≅ C ⋙ (H).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  affineConeDerivedStageFactors (toricDerivedChartOpen fan) H (toricDerivedChartList fan)

/-- The top line in the geometric augmentation is the boundary tensor,
through the genuine braiding and the original diagonal-line map. -/
def reconstructionTopTensorNormalizationIso : tensorLeft J ≅ T :=
  BraidedCategory.tensorLeftIsoTensorRight J ≪≫
    arrangementTopLineTensorNormalizationIso fan regular basis rays

/-- This factor keeps the geometric top line on the left, as in the
original augmentation, and the actual dimension shift. -/
def reconstructionNormalizationFactors :
    DerivedCategory.Q ⋙ (E).functor ≅
      (tensorLeft J).mapHomologicalComplex (.up ℤ) ⋙
        shiftFunctor (CochainComplex (QCoh X) ℤ) (-(n : ℤ)) ⋙ DerivedCategory.Q := by
  change DerivedCategory.Q ⋙
    ((T).mapDerivedCategory ⋙ shiftFunctor (DerivedQCoh X) (-(n : ℤ))) ≅ _
  exact Functor.isoWhiskerRight (T).mapDerivedCategoryFactors
      (shiftFunctor (DerivedQCoh X) (-(n : ℤ))) ≪≫
    Functor.isoWhiskerRight
      (NatIso.mapHomologicalComplex
        (reconstructionTopTensorNormalizationIso fan regular basis rays).symm (.up ℤ))
      (DerivedCategory.Q ⋙ shiftFunctor (DerivedQCoh X) (-(n : ℤ))) ≪≫
    Functor.isoWhiskerLeft ((tensorLeft J).mapHomologicalComplex (.up ℤ))
      (DerivedCategory.Q.commShiftIso (-(n : ℤ))).symm

/-- The exact source factor used by the final derived reconstruction. -/
def reconstructionDerivedSourceFactors :
    DerivedCategory.Q ⋙ (R ⋙ L) ≅
      C ⋙ (H).mapHomologicalComplex (.up ℤ) ⋙
        FunctorTotal.functor Φ (n + 1) ⋙ DerivedCategory.Q :=
  composeReconstructionSourceFactors DerivedCategory.Q DerivedCategory.Q R L C
    ((H).mapHomologicalComplex (.up ℤ))
    (FunctorTotal.functor Φ (n + 1) ⋙ DerivedCategory.Q)
    (reconstructionOriginalHomFactors fan regular basis rays)
    (reconstructionCellularDerivedFactors fan regular basis rays)

/-- The exact target factor is induced by the genuine coaugmentation,
followed by the proved boundary-line normalization. -/
def reconstructionDerivedTargetFactors :
    DerivedCategory.Q ⋙ (E).functor ≅
      C ⋙ (tensorLeft J).mapHomologicalComplex (.up ℤ) ⋙
        shiftFunctor (CochainComplex (QCoh X) ℤ) (-(n : ℤ)) ⋙ DerivedCategory.Q :=
  composeReconstructionTargetFactors DerivedCategory.Q (E).functor C
    ((tensorLeft J).mapHomologicalComplex (.up ℤ) ⋙
      shiftFunctor (CochainComplex (QCoh X) ℤ) (-(n : ℤ)) ⋙ DerivedCategory.Q)
    (affineConeLocalizationIso (toricDerivedChartOpen fan) (toricDerivedChartList fan)
      (mem_toricDerivedChartList fan) (toricDerivedChartOpen_covers fan))
    (reconstructionNormalizationFactors fan regular basis rays)

end ToricPower

end
