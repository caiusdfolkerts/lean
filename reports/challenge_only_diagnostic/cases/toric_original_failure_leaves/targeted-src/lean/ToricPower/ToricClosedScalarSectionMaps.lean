module

public import ToricPower.ToricClosedScalarWeights
public import ToricPower.ToricSubspaceLineSheaf
public import ToricPower.ArrangementDualLeftCartierSources

/-! # Full section-diagram maps from the closed inverse Cartier labels

These are morphisms of the actual scalar section diagrams. Their
naturality includes every face restriction and every original Cartier
incidence; no assertion about dimensions or chosen homology bases is
used in their construction.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

universe v w

variable {N : Type} {V : Type v} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i) [nonempty : Nonempty fan.cones]
  (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)
  (σ : fan.cones) (W : LinearSubspace fan)
  (spans : Submodule.span ℝ (σ.val : Set V) = W.space) (b : fan.Ray → ℤ)
  {B : Type w} [Preorder B] (charts : B ⥤ fan.cones)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "selected" => fanConeSliceRows fan rays σ
local notation "Yfan" => restrictedFan fan W.space W.rational
local notation "regY" => restrictedFan_isRegular fan regular W.space W.rational
local notation "restricted" => restrictedFanRayCoefficients fan W.space W.rational

local instance closedScalarMapSourceIntegral : IsIntegral fan.algebraicRealization :=
  toricSchemeIntegral fan nonempty
local instance closedScalarMapTargetNonempty : Nonempty (restrictedFan fan W.space W.rational).cones :=
  restrictedFanConesNonempty fan nonempty W.space W.rational
local instance closedScalarMapTargetIntegral :
    IsIntegral (restrictedFan fan W.space W.rational).algebraicRealization :=
  toricSchemeIntegral _ (restrictedFanConesNonempty fan nonempty W.space W.rational)

def toricClosedScalarSectionMap (c : IncidenceObject A)
    (supported : closedIntegralRowsSupport A selected c) :
    toricCartierSectionDiagram fan charts regular
        (b-arrangementDualLeftCoefficients fan basis rays c) ⟶
      toricCartierSectionDiagram (Yfan) (linearSubspaceChartFunctor fan W charts)
        regY (restricted b) :=
  (toricCartierSectionDiagramIso fan charts regular
      (b-arrangementDualLeftCoefficients fan basis rays c)).inv ≫
    toricClosedScalarWeightDiagramMap fan regular basis rays σ W spans b charts c supported ≫
    (toricCartierSectionDiagramIso (Yfan) (linearSubspaceChartFunctor fan W charts)
      regY (restricted b)).hom

theorem toricClosedScalarSectionMap_coefficients (c : IncidenceObject A)
    (supported : closedIntegralRowsSupport A selected c) (τ : B)
    (p : ToricChartDivisorWeight fan (b-arrangementDualLeftCoefficients fan basis rays c)
      (charts.obj τ) →₀ ℂ) :
    (toricClosedScalarSectionMap fan regular basis rays σ W spans b charts c supported).app (op τ)
      (toricDivisorSectionCoefficientsEquiv fan nonempty regular
        (b-arrangementDualLeftCoefficients fan basis rays c) (charts.obj τ) p) =
      toricDivisorSectionCoefficientsEquiv (Yfan)
        (restrictedFanConesNonempty fan nonempty W.space W.rational) regY (restricted b)
        (linearSubspaceChart fan W (charts.obj τ))
        (Finsupp.mapDomain
          (toricClosedScalarWeightMap fan regular basis rays σ W spans b c supported (charts.obj τ)) p) := by
  change toricDivisorSectionCoefficientsEquiv (Yfan)
      (restrictedFanConesNonempty fan nonempty W.space W.rational) regY (restricted b)
      (linearSubspaceChart fan W (charts.obj τ))
      (Finsupp.mapDomain (toricClosedScalarWeightMap fan regular basis rays σ W spans b
        c supported (charts.obj τ))
        ((toricDivisorSectionCoefficientsEquiv fan nonempty regular
          (b-arrangementDualLeftCoefficients fan basis rays c) (charts.obj τ)).symm
          (toricDivisorSectionCoefficientsEquiv fan nonempty regular
            (b-arrangementDualLeftCoefficients fan basis rays c) (charts.obj τ) p))) = _
  rw [AddEquiv.symm_apply_apply]

def toricDualDifferenceSectionLabels :
    (IncidenceObject A)ᵒᵖ ⥤ (Bᵒᵖ ⥤ ModuleCat.{0} ℂ) :=
  arrangementDualDifferenceCoefficientDiagram fan regular basis rays b ⋙
    FiniteCover.schemeBasePresheaf ℂ fan.algebraicRealization ⋙
      (Functor.whiskeringLeft Bᵒᵖ fan.algebraicRealization.Opensᵒᵖ
        (ModuleCat.{0} ℂ)).obj (toricChartSectionOpens fan charts).op

theorem toricClosedScalarSectionMap_incidence
    {c d : IncidenceObject A} (f : c ⟶ d)
    (supportedD : closedIntegralRowsSupport A selected d) :
    (toricDualDifferenceSectionLabels fan regular basis rays b charts).map f.op ≫
        toricClosedScalarSectionMap fan regular basis rays σ W spans b charts c
          (closedIntegralRowsSupport_incidence A selected f supportedD) =
      toricClosedScalarSectionMap fan regular basis rays σ W spans b charts d supportedD := by
  apply NatTrans.ext
  funext τ
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨p,rfl⟩ := (toricDivisorSectionCoefficientsEquiv fan nonempty regular
    (b-arrangementDualLeftCoefficients fan basis rays d) (charts.obj τ.unop)).surjective x
  let positive := toricMonomialNonnegative_inverseTwist fan
    (arrangementDualLeftCoefficients fan basis rays c)
    (arrangementDualLeftCoefficients fan basis rays d) b (basis.equivFun.symm f.val)
    (arrangementDualLeftCharacter_regular fan basis rays f)
  change (toricClosedScalarSectionMap fan regular basis rays σ W spans b charts c
      (closedIntegralRowsSupport_incidence A selected f supportedD)).app τ
      (Scheme.Modules.Hom.app
        (toricCartierMonomialMap fan nonempty regular
          (b-arrangementDualLeftCoefficients fan basis rays d)
          (b-arrangementDualLeftCoefficients fan basis rays c)
          (basis.equivFun.symm f.val) positive)
        (fan.affineToricChartι (charts.obj τ.unop)).opensRange
        (toricDivisorSectionCoefficientsEquiv fan nonempty regular
          (b-arrangementDualLeftCoefficients fan basis rays d) (charts.obj τ.unop) p)) = _
  have weights : Finsupp.mapDomain
      (toricClosedScalarWeightMap fan regular basis rays σ W spans b c
        (closedIntegralRowsSupport_incidence A selected f supportedD) (charts.obj τ.unop))
      (Finsupp.mapDomain (toricDivisorWeightMonomialMap fan
        (b-arrangementDualLeftCoefficients fan basis rays d)
        (b-arrangementDualLeftCoefficients fan basis rays c)
        (basis.equivFun.symm f.val) positive (charts.obj τ.unop)) p) =
    Finsupp.mapDomain (toricClosedScalarWeightMap fan regular basis rays σ W spans b d
      supportedD (charts.obj τ.unop)) p := by
    rw [← Finsupp.mapDomain_comp]
    apply congrArg (fun index => Finsupp.mapDomain index p)
    funext m
    exact toricClosedScalarWeightMap_incidence fan regular basis rays σ W spans b f
      supportedD (closedIntegralRowsSupport_incidence A selected f supportedD) (charts.obj τ.unop) m
  exact (congrArg
    (fun y => (toricClosedScalarSectionMap fan regular basis rays σ W spans b charts c
      (closedIntegralRowsSupport_incidence A selected f supportedD)).app τ y)
    (toricDivisorSectionCoefficientsEquiv_monomial fan nonempty regular
      (b-arrangementDualLeftCoefficients fan basis rays d)
      (b-arrangementDualLeftCoefficients fan basis rays c)
      (basis.equivFun.symm f.val) positive (charts.obj τ.unop) p)).trans
    ((toricClosedScalarSectionMap_coefficients fan regular basis rays σ W spans b charts c
      (closedIntegralRowsSupport_incidence A selected f supportedD) τ.unop _).trans
      ((congrArg _ weights).trans
        (toricClosedScalarSectionMap_coefficients fan regular basis rays σ W spans b charts d
          supportedD τ.unop p).symm))

end ToricPower

end
