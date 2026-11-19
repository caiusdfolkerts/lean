module

public import ToricPower.ArrangementNormalizedSources
public import ToricPower.ArrangementPowerPostcompose
public import ToricPower.ToricPowerChartSections
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory

/-!
# The power comparison on the complete chart-section diagram

The proof combines the genuine residue splitting, the projection formula,
and the actual fixed-chart section comparison. It is natural in the
coefficient sheaf, every incidence arrow, and every chart restriction.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "C" => IncidenceObject A
local notation "X" => fan.algebraicRealization
local notation "Q" => QCoh X
set_option quotPrecheck false in
local notation "J" => (ToricMeetChartIndex fan)ᵒᵖ ⥤ ModuleCat.{0} ℂ
local notation "S" => FiniteCech.quasicoherentMeetSections ℂ X (toricMeetChartOpenFunctor fan)

/-- All actual normalized inverse twists on all actual affine charts. -/
def normalizedCartierChartDiagram : Q ⥤ C ⥤ J := by
  letI := toricSchemeIntegral fan nonempty
  exact cartierMeetSectionsDiagram ℂ X (normalizedCartierSources fan nonempty regular basis rays)
    (toricMeetChartOpenFunctor fan)

instance normalizedCartierChartDiagram_additive :
    (normalizedCartierChartDiagram fan nonempty regular basis rays).Additive := by
  unfold normalizedCartierChartDiagram
  infer_instance

/-- The coefficient diagram is exact before any derived construction. -/
theorem normalizedCartierChartDiagram_exact :
    PreservesFiniteLimits (normalizedCartierChartDiagram fan nonempty regular basis rays) ∧
      PreservesFiniteColimits (normalizedCartierChartDiagram fan nonempty regular basis rays) := by
  letI := toricSchemeIntegral fan nonempty
  exact cartierMeetSectionsDiagram_exact ℂ X
    (normalizedCartierSources fan nonempty regular basis rays) (toricMeetChartOpenFunctor fan)
    (fun a => isAffineOpen_opensRange (fan.affineToricChartι (toricMeetChartEquiv fan a)))

/-- The normalized source-adjunction mates are the actual normalized
dual tensors, followed by the same full chart-section functor. -/
def normalizedCartierChartTensorIso :
    normalizedCartierChartDiagram fan nonempty regular basis rays ≅
      normalizedDualQuasicoherentTensorDiagram fan nonempty regular basis rays ⋙
        (whiskeringRight C Q J).obj S := by
  letI := toricSchemeIntegral fan nonempty
  exact Functor.isoWhiskerRight (normalizedCartierInverseTensorIso fan nonempty regular basis rays)
    ((whiskeringRight C Q J).obj S)

/-- The whole power comparison, retaining all three kinds of naturality. -/
def normalizedCartierPowerChartIso (ell : ℕ) (positive : 0 < ell) :
    normalizedCartierChartDiagram fan nonempty regular basis rays ⋙
        powerDiagramPushdown A ell positive J ≅
      quasicoherentPullback (toricPowerMap fan ell) ⋙
        normalizedCartierChartDiagram fan nonempty regular basis rays := by
  letI := toricPowerMap_finite fan regular ell positive
  exact Functor.isoWhiskerRight
      (normalizedCartierChartTensorIso fan nonempty regular basis rays)
      (powerDiagramPushdown A ell positive J) ≪≫
    Functor.isoWhiskerLeft
      (normalizedDualQuasicoherentTensorDiagram fan nonempty regular basis rays)
      (powerDiagramPostcomposeIso A ell positive S).symm ≪≫
    Functor.isoWhiskerRight
      (normalizedDualPowerTensorDiagramIso fan nonempty regular basis rays ell positive)
      ((whiskeringRight C Q J).obj S) ≪≫
    Functor.isoWhiskerLeft
      (quasicoherentPullback (toricPowerMap fan ell) ⋙
        normalizedDualQuasicoherentTensorDiagram fan nonempty regular basis rays)
      ((whiskeringRight C Q J).mapIso
        (toricPowerChartSectionsIso fan regular ell positive)) ≪≫
    Functor.isoWhiskerLeft (quasicoherentPullback (toricPowerMap fan ell))
      (normalizedCartierChartTensorIso fan nonempty regular basis rays).symm

end ToricPower

end
