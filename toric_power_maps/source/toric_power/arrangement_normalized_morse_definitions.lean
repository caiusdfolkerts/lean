module

public import ToricPower.ArrangementNormalizedRHom
public import ToricPower.ArrangementUniversalCover
public import ToricPower.MorseCategoryPresentations
public import ToricPower.ArrangementMorseModelConstruction
public import ToricPower.CanonicalAffineCoresolutionPresentation

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

/-- The genuine affine replacement followed by the original normalized
Cartier Hom diagram, before the dimension shift. -/
def normalizedUnshiftedAffineMorseModel :
    CochainComplex (QCoh X) ℤ ⥤ CochainComplex (Cells ⥤ ModuleCat.{0} ℂ) ℤ :=
  homDiagramComplexModel PN
    (canonicalAffineCoresolution (toricDerivedChartOpen fan) (toricDerivedChartList fan))

/-- The actual integer-indexed normalized Hom complex on every unbounded input. -/
def normalizedAffineMorseModel :
    CochainComplex (QCoh X) ℤ ⥤ CochainComplex (Cells ⥤ ModuleCat.{0} ℂ) ℤ :=
  shiftedHomDiagramComplexModel PN
    (shiftFunctor (CochainComplex (QCoh X) ℤ) (n : ℤ))
    (canonicalAffineCoresolution (toricDerivedChartOpen fan) (toricDerivedChartList fan))

/-- The model is literally the original shift, affine replacement and Hom diagram. -/
theorem normalizedAffineMorseModel_def :
    normalizedAffineMorseModel fan nonempty regular basis rays =
      shiftFunctor (CochainComplex (QCoh X) ℤ) (n : ℤ) ⋙
        affineConeCoresolution (toricDerivedChartOpen fan) (toricDerivedChartList fan) ⋙
          (H).mapHomologicalComplex (.up ℤ) := rfl

/-- Literal pullback to universal cells, retaining every incidence and deck map. -/
def normalizedUniversalMorseModel :
    CochainComplex (QCoh X) ℤ ⥤ CochainComplex (UniversalCells ⥤ ModuleCat.{0} ℂ) ℤ :=
  pulledShiftedHomDiagramComplexModel PN (universalCoverProjection A)
    (shiftFunctor (CochainComplex (QCoh X) ℤ) (n : ℤ))
    (canonicalAffineCoresolution (toricDerivedChartOpen fan) (toricDerivedChartList fan))

/-- The model is the exact specialization of the abstract construction.
The equality is exposed before any coefficient object is evaluated. -/
theorem normalizedUniversalMorseModel_eq_construction :
    normalizedUniversalMorseModel fan nonempty regular basis rays =
      pulledShiftedHomDiagramComplexModel PN (universalCoverProjection A)
        (shiftFunctor (CochainComplex (QCoh X) ℤ) (n : ℤ))
        (canonicalAffineCoresolution (toricDerivedChartOpen fan) (toricDerivedChartList fan)) := rfl

/-- The complete universal model, with all coefficient maps visible.
This statement exposes the literal functor before its value is evaluated. -/
theorem normalizedUniversalMorseModel_def :
    normalizedUniversalMorseModel fan nonempty regular basis rays =
      (shiftFunctor (CochainComplex (QCoh X) ℤ) (n : ℤ) ⋙
        affineConeCoresolution (toricDerivedChartOpen fan) (toricDerivedChartList fan) ⋙
          (H).mapHomologicalComplex (.up ℤ)) ⋙
        ((Functor.whiskeringLeft UniversalCells Cells (ModuleCat ℂ)).obj
          (universalCoverProjection A)).mapHomologicalComplex (.up ℤ) := rfl

end ToricPower
end
