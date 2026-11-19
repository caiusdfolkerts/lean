module

public import ToricPower.ToricClosedRowCharacters
public import ToricPower.ToricCartierSectionDiagram
public import ToricPower.LinearSubspaceChartPreimage
public import ToricPower.CechToricMonomialSections
public import ToricPower.ArrangementDualLeftCartierSources

/-! # Original character maps to the restricted Cartier section diagram

At a supported cell the inverse reflected label contributes its integral
trace character. Adding it and restricting to the saturated sublattice
defines the literal map on every Laurent weight. These maps commute with
all cone restrictions and all translated cell incidences.
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
  [Module ℝ V] {i : N →+ V} (fan : Fan i) [Nonempty fan.cones] (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)
  (σ : fan.cones) (W : LinearSubspace fan)
  (spans : Submodule.span ℝ (σ.val : Set V) = W.space) (b : fan.Ray → ℤ)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "selected" => fanConeSliceRows fan rays σ
local notation "Yfan" => restrictedFan fan W.space W.rational
local notation "restricted" => restrictedFanRayCoefficients fan W.space W.rational

theorem restrictedFanRay_le_originalChart (τ : fan.cones) (ρ : (Yfan).Ray)
    (contained : ρ.toCone ≤ linearSubspaceChart fan W τ) :
    (restrictedFanRayEquiv fan W.space W.rational ρ).val.toCone ≤ τ := by
  change ρ.toCone.val.map W.space.subtype ≤ τ.val
  rintro x ⟨y,hy,rfl⟩
  exact contained hy

def toricClosedScalarWeightMap (c : IncidenceObject A)
    (supported : closedIntegralRowsSupport A selected c) (τ : fan.cones) :
    ToricChartDivisorWeight fan (b-arrangementDualLeftCoefficients fan basis rays c) τ →
      ToricChartDivisorWeight (Yfan) (restricted b) (linearSubspaceChart fan W τ) :=
  fun m => ⟨(m.val+toricClosedRowCharacter fan regular basis rays σ W.space spans c supported).comp
      (latticeTrace i W.space).subtype.toAddMonoidHom,by
    intro ρ
    let targetRay := Fan.Ray.ofToricRay (Yfan) (linearSubspaceChart fan W τ) ρ
    let ambientRay := (restrictedFanRayEquiv fan W.space W.rational targetRay).val
    have contained : ambientRay.toCone ≤ τ :=
      restrictedFanRay_le_originalChart fan W τ targetRay
        (Fan.Ray.toCone_ofToricRay_le (Yfan) (linearSubspaceChart fan W τ) ρ)
    have original := ((toricChartWeightGlobalEquiv fan
      (b-arrangementDualLeftCoefficients fan basis rays c) τ) m).property ambientRay contained
    have coefficient := toricClosedRowCharacter_restrictedCoefficient fan regular basis rays σ
      W.space spans W.rational c supported targetRay
    change 0 ≤ b ambientRay-arrangementDualLeftCoefficients fan basis rays c ambientRay +
      m.val (fanRayPrimitiveGenerator fan ambientRay) at original
    change arrangementDualLeftCoefficients fan basis rays c ambientRay =
      -toricClosedRowCharacter fan regular basis rays σ W.space spans c supported
        (fanRayPrimitiveGenerator (Yfan) targetRay).val at coefficient
    rw [restrictedFan_primitive_value] at coefficient
    rw [← fanRayPrimitiveGenerator_ofToricRay (Yfan) (linearSubspaceChart fan W τ) ρ]
    change 0 ≤ b ambientRay +
      (m.val (fanRayPrimitiveGenerator (Yfan) targetRay).val +
        toricClosedRowCharacter fan regular basis rays σ W.space spans c supported
          (fanRayPrimitiveGenerator (Yfan) targetRay).val)
    rw [restrictedFan_primitive_value]
    dsimp only [ambientRay] at original coefficient ⊢
    omega⟩

def linearSubspaceChartFunctor {B : Type w} [Preorder B] (charts : B ⥤ fan.cones) :
    B ⥤ (Yfan).cones where
  obj c := linearSubspaceChart fan W (charts.obj c)
  map f := homOfLE (fun x hx => (charts.map f).le hx)

def toricClosedScalarWeightDiagramMap {B : Type w} [Preorder B]
    (charts : B ⥤ fan.cones) (c : IncidenceObject A)
    (supported : closedIntegralRowsSupport A selected c) :
    toricCartierWeightDiagram fan charts (b-arrangementDualLeftCoefficients fan basis rays c) ⟶
      toricCartierWeightDiagram (Yfan) (linearSubspaceChartFunctor fan W charts) (restricted b) where
  app τ := ModuleCat.ofHom (Finsupp.lmapDomain ℂ ℂ
    (toricClosedScalarWeightMap fan regular basis rays σ W spans b c supported (charts.obj τ.unop)))
  naturality {τ υ} f := by
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext
    intro m r
    change Finsupp.mapDomain (toricClosedScalarWeightMap fan regular basis rays σ W spans b
      c supported (charts.obj υ.unop))
      (Finsupp.mapDomain (toricDivisorWeightFaceMap fan
        (b-arrangementDualLeftCoefficients fan basis rays c) (charts.map f.unop).le)
        (Finsupp.single m r)) =
      Finsupp.mapDomain (toricDivisorWeightFaceMap (Yfan) (restricted b)
        ((linearSubspaceChartFunctor fan W charts).map f.unop).le)
        (Finsupp.mapDomain (toricClosedScalarWeightMap fan regular basis rays σ W spans b
          c supported (charts.obj τ.unop)) (Finsupp.single m r))
    simp only [Finsupp.mapDomain_single]
    congr 1

theorem toricClosedScalarWeightMap_incidence
    {c d : IncidenceObject A} (f : c ⟶ d)
    (supportedD : closedIntegralRowsSupport A selected d)
    (supportedC : closedIntegralRowsSupport A selected c)
    (τ : fan.cones)
    (m : ToricChartDivisorWeight fan (b-arrangementDualLeftCoefficients fan basis rays d) τ) :
    toricClosedScalarWeightMap fan regular basis rays σ W spans b c supportedC τ
      (toricDivisorWeightMonomialMap fan
        (b-arrangementDualLeftCoefficients fan basis rays d)
        (b-arrangementDualLeftCoefficients fan basis rays c)
        (basis.equivFun.symm f.val)
        (toricMonomialNonnegative_inverseTwist fan
          (arrangementDualLeftCoefficients fan basis rays c)
          (arrangementDualLeftCoefficients fan basis rays d) b
          (basis.equivFun.symm f.val) (arrangementDualLeftCharacter_regular fan basis rays f)) τ m) =
      toricClosedScalarWeightMap fan regular basis rays σ W spans b d supportedD τ m := by
  apply Subtype.ext
  ext z
  have equal := DFunLike.congr_fun (toricClosedRowCharacter_incidence fan regular basis rays σ
    W.space spans f supportedD supportedC) z
  change toricClosedRowCharacter fan regular basis rays σ W.space spans d supportedD z.val =
    toricClosedRowCharacter fan regular basis rays σ W.space spans c supportedC z.val +
      basis.equivFun.symm f.val z.val at equal
  change basis.equivFun.symm f.val z.val + m.val z.val +
    toricClosedRowCharacter fan regular basis rays σ W.space spans c supportedC z.val =
      m.val z.val+toricClosedRowCharacter fan regular basis rays σ W.space spans d supportedD z.val
  omega

end ToricPower

end
