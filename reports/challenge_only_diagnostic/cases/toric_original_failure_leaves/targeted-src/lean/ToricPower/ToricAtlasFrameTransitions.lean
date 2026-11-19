module

public import ToricPower.CartierAtlasChartFrames
public import ToricPower.ToricCharacterAtlasPullback

/-!
# Actual toric Cartier transition functions

On every common face chart, the ratio of two local equation characters is
an actual regular monomial unit. Its coefficient in the actual sheaf
frame is the ordinary affine section of that monomial. Fan morphisms pull
these coefficients back by the genuine lattice homomorphism.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory MonoidalCategory Multiplicative
open AlgebraicGeometry.Scheme.Modules TauCeti.Toric

namespace ToricPower

universe u v

variable {N N' : Type u} {V V' : Type v}
  [AddCommGroup N] [AddCommGroup N'] [AddCommGroup V] [AddCommGroup V']
  [Module ℝ V] [Module ℝ V'] {i : N →+ V} {i' : N' →+ V'}

/-- Inclusion of cones gives inclusion of their actual open charts. -/
theorem toricChart_opensRange_mono (fan : Fan i) {small large : fan.cones}
    (included : small ≤ large) :
    (fan.affineToricChartι small).opensRange ≤ (fan.affineToricChartι large).opensRange := by
  have face := fan.isFaceOf_of_le large.property small.property included
  rintro point ⟨localPoint, same⟩
  refine ⟨faceAffineToricSchemeMap fan.lattice face localPoint, ?_⟩
  have square := congrArg (fun morphism => morphism localPoint)
    (Fan.faceAffineToricSchemeMap_comp_affineToricChartι face)
  exact (show fan.affineToricChartι large
    (faceAffineToricSchemeMap fan.lattice face localPoint) =
      fan.affineToricChartι small localPoint from square).trans same

/-- Actual affine sections respect the actual affine toric morphism. -/
theorem affineGlobalSectionsEquiv_toricMap (source : Fan i) (target : Fan i')
    (mapping : FanHom source target) {σ : PointedCone ℝ V} {τ : PointedCone ℝ V'}
    (mapsTo : Set.MapsTo mapping.realMap σ τ) (coordinate : affineCoordinateRing target.lattice τ) :
    (affineToricSchemeMap source.lattice target.lattice mapping.latticeMap mapping.realMap
      mapping.map_lattice mapsTo).appTop
        (affineGlobalSectionsEquiv (affineCoordinateRing target.lattice τ) coordinate) =
    affineGlobalSectionsEquiv (affineCoordinateRing source.lattice σ)
      (affineCoordinateRingMap source.lattice target.lattice mapping.latticeMap mapping.realMap
        mapping.map_lattice mapsTo coordinate) := by
  rw [affineToricSchemeMap_def]
  exact (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (affineCoordinateRingMap source.lattice target.lattice
      mapping.latticeMap mapping.realMap mapping.map_lattice mapsTo).toRingHom)) coordinate).symm

/-- The actual coordinate homomorphism pulls a monomial unit back to the
unit for the composed lattice character. -/
theorem toricMonomialUnit_fanMap (source : Fan i) (target : Fan i')
    (mapping : FanHom source target) {σ : PointedCone ℝ V} {τ : PointedCone ℝ V'}
    (mapsTo : Set.MapsTo mapping.realMap σ τ) (character : N' →+ ℤ)
    (positive : character ∈ dualSemigroup target.lattice τ)
    (negative : -character ∈ dualSemigroup target.lattice τ) :
    Units.map (affineCoordinateRingMap source.lattice target.lattice mapping.latticeMap
      mapping.realMap mapping.map_lattice mapsTo).toMonoidHom
      (toricMonomialUnit target.lattice τ character positive negative) =
    toricMonomialUnit source.lattice σ (character.comp mapping.latticeMap)
      (character_pullback_mem mapping mapsTo positive)
      (by simpa only [AddMonoidHom.neg_comp] using character_pullback_mem mapping mapsTo negative) := by
  apply Units.ext
  change affineCoordinateRingMap source.lattice target.lattice mapping.latticeMap
    mapping.realMap mapping.map_lattice mapsTo
      (MonoidAlgebra.single (ofAdd (⟨character, positive⟩ : dualSemigroup target.lattice τ)) 1) = _
  rw [affineCoordinateRingMap_single, toricMonomialUnit_val]
  apply congrArg (fun m : dualSemigroup source.lattice σ =>
    MonoidAlgebra.single (ofAdd m) (1 : ℂ))
  apply Subtype.ext
  ext n
  exact dualSemigroupMap_apply source.lattice target.lattice mapping.latticeMap mapping.realMap
    mapping.map_lattice mapsTo ⟨character, positive⟩ n

namespace ToricCharacterAtlas

variable {fan : Fan i}

/-- The actual regular monomial converting the first frame into the second. -/
def frameTransitionUnit (atlas : ToricCharacterAtlas fan) (first second cone : fan.cones)
    (inFirst : cone ≤ first) (inSecond : cone ≤ second) :
    (affineCoordinateRing fan.lattice cone.val)ˣ :=
  toricMonomialUnit fan.lattice cone.val (atlas.equation second - atlas.equation first)
    (dualSemigroup_anti fan.lattice (le_inf inSecond inFirst) (atlas.positive second first))
    (dualSemigroup_anti fan.lattice (le_inf inSecond inFirst) (atlas.negative second first))

/-- Read a toric Cartier atlas frame on any of its face charts. -/
def faceFrame (atlas : ToricCharacterAtlas fan) (nonempty : Nonempty fan.cones)
    (index cone : fan.cones) (included : cone ≤ index) :
    letI := toricSchemeIntegral fan nonempty
    𝟙_ (fan.affineToricChart cone).Modules ≅
      (atlas.cartierDivisor nonempty).sheaf.restrict (fan.affineToricChartι cone) := by
  letI := toricSchemeIntegral fan nonempty
  exact (atlas.cartierEquationAtlas nonempty).affineFrame index (fan.affineToricChartι cone)
    (toricChart_opensRange_mono fan included)

/-- The actual transition between Cartier frames is its literal monomial
section, with the sign fixed by reciprocal local equations. -/
theorem faceFrame_transition (atlas : ToricCharacterAtlas fan) (nonempty : Nonempty fan.cones)
    (first second cone : fan.cones) (inFirst : cone ≤ first) (inSecond : cone ≤ second) :
    letI := toricSchemeIntegral fan nonempty
    (atlas.faceFrame nonempty first cone inFirst).hom =
      globalSectionsSmul (𝟙_ (fan.affineToricChart cone).Modules)
        (affineGlobalSectionsEquiv (affineCoordinateRing fan.lattice cone.val)
          (atlas.frameTransitionUnit first second cone inFirst inSecond :
            affineCoordinateRing fan.lattice cone.val)) ≫
        (atlas.faceFrame nonempty second cone inSecond).hom := by
  letI := toricSchemeIntegral fan nonempty
  letI := chartOpen_nonempty fan cone
  let unit := atlas.frameTransitionUnit first second cone inFirst inSecond
  let actualUnit := Units.map (chartCoordinateSectionsEquiv fan cone).toMonoidHom unit
  have ratio :
      TauCeti.AlgebraicGeometry.Scheme.regularUnitToFunctionField fan.algebraicRealization
        (fan.affineToricChartι cone).opensRange actualUnit *
        (atlas.cartierEquationAtlas nonempty).equation first =
          (atlas.cartierEquationAtlas nonempty).equation second := by
    change TauCeti.AlgebraicGeometry.Scheme.regularUnitToFunctionField fan.algebraicRealization
      (fan.affineToricChartι cone).opensRange actualUnit *
      rationalCharacterUnit fan nonempty (atlas.equation first) =
        rationalCharacterUnit fan nonempty (atlas.equation second)
    rw [chartCoordinateGerm_regularUnit]
    change Units.map (chartCoordinateGerm fan nonempty cone).toMonoidHom
      (toricMonomialUnit fan.lattice cone.val (atlas.equation second - atlas.equation first)
        _ _) * _ = _
    rw [chartCoordinateGerm_monomialUnit]
    exact rationalCharacterUnit_sub_mul fan nonempty _ _
  have transition := (atlas.cartierEquationAtlas nonempty).affineFrame_transition
    first second (fan.affineToricChartι cone)
    (toricChart_opensRange_mono fan inFirst) (toricChart_opensRange_mono fan inSecond)
    actualUnit ratio
  have sectionFormula :
      ((fan.affineToricChartι cone).appIso ⊤).hom
        (fan.algebraicRealization.presheaf.map
          (eqToHom (fan.affineToricChartι cone).image_top_eq_opensRange).op
            (actualUnit : Γ(fan.algebraicRealization, (fan.affineToricChartι cone).opensRange))) =
      affineGlobalSectionsEquiv (affineCoordinateRing fan.lattice cone.val)
        (unit : affineCoordinateRing fan.lattice cone.val) := by
    change ((fan.affineToricChartι cone).appIso ⊤).hom
      (fan.algebraicRealization.presheaf.map
        (eqToHom (fan.affineToricChartι cone).image_top_eq_opensRange).op
          ((IsOpenImmersion.ΓIsoTop (fan.affineToricChartι cone)).hom
            (affineGlobalSectionsEquiv (affineCoordinateRing fan.lattice cone.val)
              (unit : affineCoordinateRing fan.lattice cone.val)))) = _
    exact openImmersion_appIso_top_sections _ _
  exact transition.trans (congrArg (fun scalar =>
    globalSectionsSmul (𝟙_ (fan.affineToricChart cone).Modules) scalar ≫
      (atlas.faceFrame nonempty second cone inSecond).hom) sectionFormula)

end ToricCharacterAtlas

end ToricPower
