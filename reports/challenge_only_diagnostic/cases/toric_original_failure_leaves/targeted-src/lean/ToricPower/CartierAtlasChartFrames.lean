module

public import ToricPower.SheafChartFrameTransitions
public import ToricPower.SheafRestrictionPullbackCoherence

/-!
# Cartier frames on actual scheme charts

Every atlas frame is read on arbitrary smaller open charts. Its values,
restriction behavior, and transition functions are statements about the
ordinary module sheaf attached to the Cartier divisor.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

namespace ToricPower.CartierEquationAtlas

universe u v

variable {X A B : Scheme.{u}} [IsIntegral X] (atlas : CartierEquationAtlas.{u,v} X)

/-- The Cartier frame on any actual open chart contained in its atlas open. -/
def affineFrame (index : atlas.Index) (chart : A ⟶ X) [IsOpenImmersion chart]
    (included : chart.opensRange ≤ atlas.chart index) :
    𝟙_ A.Modules ≅ atlas.cartierDivisor.sheaf.restrict chart :=
  cartierOverToAffineFrame chart atlas.cartierDivisor.sheaf
    (atlas.frameOn index chart.opensRange included)

/-- The actual section formula on every open of an arbitrary chart. -/
theorem affineFrame_sections (index : atlas.Index) (chart : A ⟶ X) [IsOpenImmersion chart]
    (included : chart.opensRange ≤ atlas.chart index) (U : A.Opens) (coefficient : Γ(A, U)) :
    Hom.app (atlas.affineFrame index chart included).hom U coefficient =
      (atlas.chartTrivialization index).hom.val.app
        (op (Over.mk (homOfLE ((chart.image_le_opensRange U).trans included))))
        ((chart.appIso U).inv coefficient) := by
  exact cartierOverToAffineFrame_image_sections chart atlas.cartierDivisor.sheaf
    (atlas.frameOn index chart.opensRange included) U coefficient

/-- Ordinary restriction of an atlas frame agrees with reading the same
atlas frame on the smaller composite chart. -/
theorem affineFrame_restrict (index : atlas.Index) (chart : A ⟶ X)
    (smaller : B ⟶ A) [IsOpenImmersion chart] [IsOpenImmersion smaller]
    (included : chart.opensRange ≤ atlas.chart index)
    (included' : (smaller ≫ chart).opensRange ≤ atlas.chart index) :
    restrictModuleFrame smaller (atlas.affineFrame index chart included) ≪≫
      ((restrictFunctorComp smaller chart).app atlas.cartierDivisor.sheaf).symm =
        atlas.affineFrame index (smaller ≫ chart) included' := by
  apply Iso.ext
  apply unitSheafHom_ext_top
  simp only [restrictModuleFrame, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.app_inv, Hom.comp_app, ConcreteCategory.comp_apply, restrictFunctor_map_app,
    restrictUnitIso_inv_sections, map_one,
    restrictFunctorComp_inv_app_app]
  let source : Over (atlas.chart index) :=
    Over.mk (homOfLE ((chart.image_le_opensRange (smaller ''ᵁ ⊤)).trans included))
  let target : Over (atlas.chart index) :=
    Over.mk (homOfLE (((smaller ≫ chart).image_le_opensRange ⊤).trans included'))
  let reindex : target ⟶ source := Over.homMk
    (eqToHom (show (smaller ≫ chart) ''ᵁ (⊤ : B.Opens) = chart ''ᵁ smaller ''ᵁ ⊤ by simp))
  have naturality := ConcreteCategory.congr_hom
    ((atlas.chartTrivialization index).hom.val.naturality reindex.op)
      (1 : Γ(X, chart ''ᵁ smaller ''ᵁ (⊤ : B.Opens)))
  change (atlas.chartTrivialization index).hom.val.app (op target)
      (X.presheaf.map reindex.left.op (1 : Γ(X, chart ''ᵁ smaller ''ᵁ (⊤ : B.Opens)))) =
    atlas.cartierDivisor.sheaf.presheaf.map reindex.left.op
      ((atlas.chartTrivialization index).hom.val.app (op source)
        (1 : Γ(X, chart ''ᵁ smaller ''ᵁ (⊤ : B.Opens)))) at naturality
  simp only [map_one] at naturality
  have firstValue := atlas.affineFrame_sections index chart included
    (smaller ''ᵁ (⊤ : B.Opens)) (1 : Γ(A, smaller ''ᵁ (⊤ : B.Opens)))
  have secondValue := atlas.affineFrame_sections index (smaller ≫ chart) included'
    ⊤ (1 : Γ(B, ⊤))
  simp only [map_one] at firstValue secondValue
  exact (congrArg (atlas.cartierDivisor.sheaf.presheaf.map reindex.left.op) firstValue).trans
    (naturality.symm.trans secondValue.symm)

/-- The transition between two actual chart frames is multiplication by
the actual regular unit relating their local equations. -/
theorem affineFrame_transition (first second : atlas.Index) (chart : A ⟶ X)
    [IsOpenImmersion chart] [Nonempty chart.opensRange]
    (firstIncluded : chart.opensRange ≤ atlas.chart first)
    (secondIncluded : chart.opensRange ≤ atlas.chart second)
    (unit : Γ(X, chart.opensRange)ˣ)
    (ratio : TauCeti.AlgebraicGeometry.Scheme.regularUnitToFunctionField X chart.opensRange unit *
      atlas.equation first = atlas.equation second) :
    (atlas.affineFrame first chart firstIncluded).hom =
      globalSectionsSmul (𝟙_ A.Modules)
        ((chart.appIso ⊤).hom
          (X.presheaf.map (eqToHom chart.image_top_eq_opensRange).op (unit : Γ(X, chart.opensRange)))) ≫
        (atlas.affineFrame second chart secondIncluded).hom :=
  cartierOverToAffineFrame_transition chart atlas.cartierDivisor.sheaf
    (atlas.frameOn first chart.opensRange firstIncluded)
    (atlas.frameOn second chart.opensRange secondIncluded) (unit : Γ(X, chart.opensRange))
      (atlas.frameOn_transition first second chart.opensRange firstIncluded secondIncluded unit ratio)

end ToricPower.CartierEquationAtlas
