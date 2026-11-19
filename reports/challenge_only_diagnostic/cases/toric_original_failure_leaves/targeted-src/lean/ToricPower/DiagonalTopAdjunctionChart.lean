module

public import ToricPower.DualDiagonalSupportedSheaf
public import ToricPower.DiagonalTopQuotient
public import ToricPower.DiagonalInverseCellFrames
public import ToricPower.SchemeAdjunctSquareSections

/-!
# The original diagonal top quotient under its actual adjunction

The target comparison is the original unit on top homology followed by
ordinary open base change. Each actual inverse-cell column is therefore
the adjunct of its original pulled-back quotient. This is a map-level
identity, independent of any exactness assertion about diagonal pullback.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open TauCeti.Toric ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)
  (σ τ : fan.cones)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "chart" => diagonalProductChartι fan basis rays σ τ
local notation "overlap" => fan.affineToricChartι (σ ⊓ τ)
local notation "δ" => toricDiagonal fan
local notation "g" => Spec.map (CommRingCat.ofHom
  (diagonalChartToIntersection fan basis rays σ τ))
local notation "H" => dualDiagonalTopSheaf fan nonempty regular basis rays
local notation "J" => dualDiagonalLineSheaf fan nonempty regular basis rays

/-- The actual top homology, on a product chart, as the direct image
of its actual diagonal line on the actual overlap. -/
def dualDiagonalTopOpenBaseChangeIso :
    (Scheme.Modules.pullback chart).obj H ≅
      (Scheme.Modules.pushforward g).obj ((J).restrict overlap) :=
  (Scheme.Modules.pullback chart).mapIso
      (dualDiagonalTopPushforwardIso fan nonempty regular basis rays) ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback chart).app
      ((Scheme.Modules.pushforward δ).obj J)).symm ≪≫
    pushforwardRestrictionIso δ g overlap chart
      (diagonalProductChart_isPullback fan basis rays σ τ).w
      (diagonalChart_preimage_opensRange fan basis rays σ τ).le J

/-- The original global quotient column is the original local
adjunct after the actual supported-target comparison. -/
@[reassoc]
theorem diagonalInverseCellTopChart_adjunct (c : NormalizedCell A n) :
    (Scheme.Modules.pullback chart).map
        (diagonalInverseCellTopQuotient fan nonempty regular basis rays c) ≫
      (dualDiagonalTopOpenBaseChangeIso fan nonempty regular basis rays σ τ).hom =
    (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
      ((pullbackSquareIso δ g overlap chart
          (diagonalProductChart_isPullback fan basis rays σ τ).w).hom.app
          (diagonalInverseProductSheaf fan nonempty regular basis rays c) ≫
        (Scheme.Modules.restrictFunctorIsoPullback overlap).inv.app
          ((Scheme.Modules.pullback δ).obj
            (diagonalInverseProductSheaf fan nonempty regular basis rays c)) ≫
        (Scheme.Modules.restrictFunctor overlap).map
          ((Scheme.Modules.pullback δ).map
            (diagonalInverseCellTopQuotient fan nonempty regular basis rays c))) := by
  let a := diagonalInverseCellTopQuotient fan nonempty regular basis rays c
  have original := (Scheme.Modules.pullbackPushforwardAdjunction δ).unit.naturality a
  change a ≫ (Scheme.Modules.pullbackPushforwardAdjunction δ).unit.app H =
    (Scheme.Modules.pullbackPushforwardAdjunction δ).unit.app _ ≫
      (Scheme.Modules.pushforward δ).map ((Scheme.Modules.pullback δ).map a) at original
  change (Scheme.Modules.pullback chart).map a ≫
    (Scheme.Modules.pullback chart).map
      ((Scheme.Modules.pullbackPushforwardAdjunction δ).unit.app H) ≫
    (Scheme.Modules.restrictFunctorIsoPullback chart).inv.app
      ((Scheme.Modules.pushforward δ).obj J) ≫
    pushforwardRestrictionMap δ g overlap chart
      (diagonalProductChart_isPullback fan basis rays σ τ).w J = _
  rw [← Functor.map_comp_assoc, original]
  exact pullback_pushforwardRestrictionMap_homEquiv δ g overlap chart
    (diagonalProductChart_isPullback fan basis rays σ τ).w
    ((Scheme.Modules.pullback δ).map a)

/-- In the actual inverse-cell frame, the same equality retains the
specified unit-source map used for affine Laurent coordinates. -/
@[reassoc]
theorem diagonalInverseCellTopFrame_adjunct (c : NormalizedCell A n) :
    (diagonalInverseCellPullbackFrame fan nonempty regular basis rays σ τ n c).hom ≫
      (Scheme.Modules.pullback chart).map
        (diagonalInverseCellTopQuotient fan nonempty regular basis rays c) ≫
      (dualDiagonalTopOpenBaseChangeIso fan nonempty regular basis rays σ τ).hom =
    (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
      ((Scheme.Modules.pullback g).map
          (diagonalInverseCellPullbackFrame fan nonempty regular basis rays σ τ n c).hom ≫
        (pullbackSquareIso δ g overlap chart
          (diagonalProductChart_isPullback fan basis rays σ τ).w).hom.app
          (diagonalInverseProductSheaf fan nonempty regular basis rays c) ≫
        (Scheme.Modules.restrictFunctorIsoPullback overlap).inv.app
          ((Scheme.Modules.pullback δ).obj
            (diagonalInverseProductSheaf fan nonempty regular basis rays c)) ≫
        (Scheme.Modules.restrictFunctor overlap).map
          ((Scheme.Modules.pullback δ).map
            (diagonalInverseCellTopQuotient fan nonempty regular basis rays c))) := by
  rw [diagonalInverseCellTopChart_adjunct]
  exact ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv_naturality_left
    (diagonalInverseCellPullbackFrame fan nonempty regular basis rays σ τ n c).hom _).symm

end ToricPower

end
