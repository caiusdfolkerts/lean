module

public import ToricPower.ToricClosedScalarSectionMaps
public import ToricPower.ToricLinearPushforwardCohomology
public import ToricPower.ArrangementClosedDualUnderlying
public import ToricPower.CartierFiniteMeetLinear

/-! # The actual whole chart diagrams in the closed-slice calculation

The finite meet index retains every cone. On the target, inverse images
are the literal restricted-cone charts of the genuine linear inclusion.
The comparisons below are whole functor isomorphisms, hence preserve all
chart restrictions and all coefficient maps.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)

def toricMeetConeFunctor : ToricMeetChartIndex fan ⥤ fan.cones where
  obj := toricMeetChartEquiv fan
  map f := homOfLE f.le

theorem toricMeetChartSectionOpens_eq :
    toricChartSectionOpens fan (toricMeetConeFunctor fan) = toricMeetChartOpenFunctor fan :=
  CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ => Subsingleton.elim _ _)

variable (W : LinearSubspace fan)

local instance closedScalarChartClosed : IsClosedImmersion (linearToricInclusion fan W) :=
  linearToricInclusion_isClosedImmersion fan W
local instance closedScalarChartOver :
    (linearToricInclusion fan W).IsOver (Spec (.of ℂ)) := by
  unfold linearToricInclusion
  infer_instance

local notation "X" => fan.algebraicRealization
local notation "Yfan" => restrictedFan fan W.space W.rational
local notation "Y" => Fan.algebraicRealization (restrictedFan fan W.space W.rational)
local notation "B" => ToricMeetChartIndex fan
local notation "opensX" => toricMeetChartOpenFunctor fan
local notation "chartsY" => linearSubspaceChartFunctor fan W (toricMeetConeFunctor fan)
local notation "opensY" => toricChartSectionOpens (Yfan) chartsY

def toricLinearChartPreimageIso :
    (opensX).op ⋙ (Opens.map (linearToricInclusion fan W).base).op ≅ (opensY).op :=
  NatIso.ofComponents (fun c => eqToIso (congrArg op (show
      linearToricInclusion fan W ⁻¹ᵁ (opensX).obj c.unop = (opensY).obj c.unop from
        Opens.ext (linearToricInclusion_preimage_chart fan W (toricMeetChartEquiv fan c.unop)))))
    (fun _ => Subsingleton.elim _ _)

def quasicoherentLinearChartSectionsIso :
    quasicoherentAffinePushforward (linearToricInclusion fan W) ⋙
      FiniteCech.quasicoherentMeetSections ℂ X opensX ≅
      FiniteCech.quasicoherentMeetSections ℂ Y opensY :=
  Functor.isoWhiskerLeft (quasicoherentInclusion Y)
    (pushforwardChartBaseSectionsIso ℂ (linearToricInclusion fan W) (opensX).op ≪≫
      Functor.isoWhiskerLeft (FiniteCover.schemeBasePresheaf ℂ Y)
        ((Functor.whiskeringLeft Bᵒᵖ (Y).Opensᵒᵖ (ModuleCat.{0} ℂ)).mapIso
          (toricLinearChartPreimageIso fan W)))

variable [nonempty : Nonempty fan.cones] (regular : fan.IsRegular)

local instance closedScalarChartSourceIntegral : IsIntegral fan.algebraicRealization :=
  toricSchemeIntegral fan nonempty
local instance closedScalarChartTargetNonempty : Nonempty (restrictedFan fan W.space W.rational).cones :=
  restrictedFanConesNonempty fan nonempty W.space W.rational
local instance closedScalarChartTargetIntegral :
    IsIntegral (restrictedFan fan W.space W.rational).algebraicRealization :=
  toricSchemeIntegral _ (restrictedFanConesNonempty fan nonempty W.space W.rational)

def closedDualRestrictedCartierQuasicoherent (b : fan.Ray → ℤ) : QCoh Y :=
  quasicoherentCartierObject Y
    (invariantCartierDivisor (Yfan)
      (restrictedFanConesNonempty fan nonempty W.space W.rational)
      (restrictedFan_isRegular fan regular W.space W.rational)
      (restrictedFanRayCoefficients fan W.space W.rational b))

def closedDualTargetQuasicoherent (b : fan.Ray → ℤ) : QCoh X :=
  (quasicoherentAffinePushforward (linearToricInclusion fan W)).obj
    (closedDualRestrictedCartierQuasicoherent fan W regular b)

def closedDualTargetSectionDiagramIso (b : fan.Ray → ℤ) :
    (FiniteCech.quasicoherentMeetSections ℂ X opensX).obj
        (closedDualTargetQuasicoherent fan W regular b) ≅
      toricCartierSectionDiagram (Yfan) chartsY
        (restrictedFan_isRegular fan regular W.space W.rational)
        (restrictedFanRayCoefficients fan W.space W.rational b) :=
  (quasicoherentLinearChartSectionsIso fan W).app
    (closedDualRestrictedCartierQuasicoherent fan W regular b)

variable {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

omit W in
def closedDualSourceSectionDiagramIso (b : fan.Ray → ℤ) :
    ((arrangementDualInverseTensorFunctor fan regular basis rays).flip.obj
      (quasicoherentCartierObject X (invariantCartierDivisor fan nonempty regular b))) ⋙
        FiniteCech.quasicoherentMeetSections ℂ X opensX ≅
      toricDualDifferenceSectionLabels fan regular basis rays b (toricMeetConeFunctor fan) := by
  unfold FiniteCech.quasicoherentMeetSections
  rw [← toricMeetChartSectionOpens_eq fan]
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (arrangementDualInverseTensorUnderlyingIso fan regular basis rays b)
      (FiniteCech.meetChartSectionsFunctor ℂ X
        (toricChartSectionOpens fan (toricMeetConeFunctor fan)))

end ToricPower

end
