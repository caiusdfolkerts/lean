module

public import ToricPower.ArrangementNormalizedMorseDefinitions
public import ToricPower.ShiftedModelFactorization

/-! # A literal unbounded representative of the normalized right adjoint

The complex is obtained from the actual input shift, the finite affine
coresolution, and the actual normalized Cartier Hom diagram. Its
localization is identified with the paper's normalized right adjoint.
Thus the subsequent Morse calculation applies to that precise image.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open TauCeti.Toric ToricPower.IntegralArrangement

attribute [local instance 2000] Abelian.toPreadditive
attribute [local instance 2000] Preadditive.preadditiveHasZeroMorphisms

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "Cells" => IncidenceObject A
local notation "UniversalCells" => UniversalIncidenceObject A
local notation "X" => fan.algebraicRealization
local notation "PN" => normalizedCartierQuasicoherentSources fan nonempty regular basis rays
local notation "H" => Cellular.homDiagram ℂ PN

local instance normalizedMorseFactorDerivedQCoh : HasDerivedCategory.{1} (QCoh X) :=
  HasDerivedCategory.standard _
local instance normalizedMorseFactorDerivedCells : HasDerivedCategory.{1} (Cells ⥤ ModuleCat.{0} ℂ) :=
  HasDerivedCategory.standard _

local instance normalizedMorseFactorLocalLimits (cone : fan.cones) :
    PreservesFiniteLimits (quasicoherentOpenLocalization (toricDerivedChartOpen fan cone).ι ⋙ H) :=
  (toricDerivedLabelLocalExact fan PN
    (normalizedCartierSources_invertible fan nonempty regular basis rays) cone).1
local instance normalizedMorseFactorLocalColimits (cone : fan.cones) :
    PreservesFiniteColimits (quasicoherentOpenLocalization (toricDerivedChartOpen fan cone).ι ⋙ H) :=
  (toricDerivedLabelLocalExact fan PN
    (normalizedCartierSources_invertible fan nonempty regular basis rays) cone).2

/-- The existing normalization is assembled before evaluating any complex. -/
def normalizedMorseAffineNormalizationIso :
    letI := nonempty
    arrangementNormalizedDerivedHom fan regular basis rays ≅
      shiftFunctor (DerivedCategory (QCoh X)) (n : ℤ) ⋙
        normalizedCartierAffineRHom fan nonempty regular basis rays := by
  letI := nonempty
  exact arrangementNormalizedHomFiniteModelIso fan nonempty regular basis rays ≪≫
    Functor.isoWhiskerLeft (shiftFunctor (DerivedCategory (QCoh X)) (n : ℤ))
      (normalizedCartierFiniteRHomIso fan nonempty regular basis rays)

/-- The original affine localization comparison, with only equal inherited
preadditive structures transported, as a whole natural isomorphism. -/
def normalizedMorseAffineStageFactors :
    DerivedCategory.Q ⋙ normalizedCartierAffineRHom fan nonempty regular basis rays ≅
      normalizedUnshiftedAffineMorseModel fan nonempty regular basis rays ⋙ DerivedCategory.Q := by
  simpa only [normalizedCartierAffineRHom, normalizedUnshiftedAffineMorseModel, homDiagramComplexModel, canonicalAffineCoresolution,
    morseQuasicoherentPreadditivePresentation, morseDiagramPreadditivePresentation] using
    ((affineConeDerivedStageFactors (toricDerivedChartOpen fan) H
      (toricDerivedChartList fan)) ≪≫
      (Functor.associator (affineConeCoresolution (toricDerivedChartOpen fan)
        (toricDerivedChartList fan)) ((H).mapHomologicalComplex (.up ℤ)) DerivedCategory.Q).symm)

/-- The entire genuine normalized right-adjoint model, with its original shift. -/
def normalizedAffineMorseModelNatIso :
    letI := nonempty
    DerivedCategory.Q ⋙ arrangementNormalizedDerivedHom fan regular basis rays ≅
      normalizedAffineMorseModel fan nonempty regular basis rays ⋙ DerivedCategory.Q := by
  letI := nonempty
  exact shiftedModelFactorization DerivedCategory.Q DerivedCategory.Q
    (shiftFunctor (CochainComplex (QCoh X) ℤ) (n : ℤ))
    (shiftFunctor (DerivedCategory (QCoh X)) (n : ℤ))
    (arrangementNormalizedDerivedHom fan regular basis rays)
    (normalizedCartierAffineRHom fan nonempty regular basis rays)
    (normalizedUnshiftedAffineMorseModel fan nonempty regular basis rays)
    (normalizedMorseAffineNormalizationIso fan nonempty regular basis rays)
    (DerivedCategory.Q.commShiftIso (n : ℤ)).symm
    (normalizedMorseAffineStageFactors fan nonempty regular basis rays)

end ToricPower
end
