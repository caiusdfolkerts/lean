module

public import ToricPower.SheafModuleHomGluing
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Basic

/-!
# Pulling local frames through a commuting chart square

These comparisons use the genuine pullback of module sheaves and its
composition isomorphisms. They apply to every morphism of schemes, including
the nondominant inclusions of toric subgroups occurring in linear tests.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory

namespace ToricPower

universe u

variable {A B X Y : Scheme.{u}}

/-- Restricting to the image of an open immersion is the same as first
restricting to its source and then using its inverse image isomorphism. -/
def moduleImageRestrictionIso (inclusion : A ⟶ X) [IsOpenImmersion inclusion]
    (M : X.Modules) :
    M.restrict inclusion.opensRange.ι ≅
      (M.restrict inclusion).restrict inclusion.isoOpensRange.inv :=
  ((Scheme.Modules.restrictFunctorCongr inclusion.isoOpensRange_inv_comp).app M).symm ≪≫
    (Scheme.Modules.restrictFunctorComp inclusion.isoOpensRange.inv inclusion).app M

/-- An isomorphism on an actual chart gives an isomorphism on the slice site
of its open image. This allows local affine constructions to be glued. -/
def moduleOverIsoOfChartIso (inclusion : A ⟶ X) [IsOpenImmersion inclusion]
    {M N : X.Modules} (equivalence : M.restrict inclusion ≅ N.restrict inclusion) :
    M.over inclusion.opensRange ≅ N.over inclusion.opensRange :=
  (Scheme.Modules.overEquiv inclusion.opensRange).fullyFaithfulFunctor.preimageIso
    ((Scheme.Modules.overFunctorEquiv inclusion.opensRange).app M ≪≫
      moduleImageRestrictionIso inclusion M ≪≫
      (Scheme.Modules.restrictFunctor inclusion.isoOpensRange.inv).mapIso equivalence ≪≫
      (moduleImageRestrictionIso inclusion N).symm ≪≫
      ((Scheme.Modules.overFunctorEquiv inclusion.opensRange).app N).symm)

/-- Transport a local frame through a commuting square of an arbitrary
scheme morphism and two open charts. No map of function fields is used. -/
def pullbackChartFrame (morphism : X ⟶ Y)
    (sourceChart : A ⟶ X) [IsOpenImmersion sourceChart]
    (targetChart : B ⟶ Y) [IsOpenImmersion targetChart]
    (chartMap : A ⟶ B) (square : sourceChart ≫ morphism = chartMap ≫ targetChart)
    (M : Y.Modules)
    (frame : SheafOfModules.unit B.ringCatSheaf ≅ M.restrict targetChart) :
    SheafOfModules.unit A.ringCatSheaf ≅
      ((Scheme.Modules.pullback morphism).obj M).restrict sourceChart :=
  (Scheme.Modules.pullbackObjUnitIso chartMap).symm ≪≫
    (Scheme.Modules.pullback chartMap).mapIso frame ≪≫
    (Scheme.Modules.pullback chartMap).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback targetChart).app M) ≪≫
    (Scheme.Modules.pullbackComp chartMap targetChart).app M ≪≫
    (Scheme.Modules.pullbackCongr square.symm).app M ≪≫
    ((Scheme.Modules.pullbackComp sourceChart morphism).app M).symm ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback sourceChart).app
      ((Scheme.Modules.pullback morphism).obj M)).symm

end ToricPower
