module

public import ToricPower.ToricPulledCartierNaturality
public import ToricPower.SheafFrameComparison
public import ToricPower.SheafChartSectionTransport

/-!
# Actual chart compatibility of toric Cartier pullback

The local isomorphisms between the character-pullback Cartier line and
the literal module-sheaf pullback commute with every actual face restriction.
The equation-independence theorem removes the choice of containing chart.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 400000

open AlgebraicGeometry CategoryTheory MonoidalCategory TauCeti.Toric
open AlgebraicGeometry.Scheme.Modules
namespace ToricPower
universe u v
variable {N N' : Type u} {V V' : Type v}
  [AddCommGroup N] [AddCommGroup N'] [AddCommGroup V] [AddCommGroup V']
  [Module ℝ V] [Module ℝ V'] {i : N →+ V} {i' : N' →+ V'}
  {source : Fan i} {target : Fan i'}

namespace ToricCharacterAtlas

/-- The local sheaf comparison commutes with genuine restriction along
every face map; both sides use their own chart equations. -/
theorem pullbackFaceIso_restrict (atlas : ToricCharacterAtlas target)
    (sourceNonempty : Nonempty source.cones) (targetNonempty : Nonempty target.cones)
    (mapping : FanHom source target) (large small : source.cones) (included : small ≤ large) :
    letI := toricSchemeIntegral source sourceNonempty
    letI := toricSchemeIntegral target targetNonempty
    let face := source.isFaceOf_of_le large.property small.property included
    let localMap := faceAffineToricSchemeMap source.lattice face
    letI := (source.isToricCone large.property).rational.isOpenImmersion_faceAffineToricSchemeMap
      source.lattice face
    let square := Fan.faceAffineToricSchemeMap_comp_affineToricChartι face
    let original := ((atlas.pullback mapping).cartierDivisor sourceNonempty).sheaf
    let pulled := (Scheme.Modules.pullback mapping.algebraicMap).obj (atlas.cartierDivisor targetNonempty).sheaf
    (chartRestrictionIso localMap (source.affineToricChartι large)
        (source.affineToricChartι small) square original).symm ≪≫
      (restrictFunctor localMap).mapIso
        (atlas.pullbackFaceIso sourceNonempty targetNonempty mapping large large le_rfl) ≪≫
      chartRestrictionIso localMap (source.affineToricChartι large)
        (source.affineToricChartι small) square pulled =
    atlas.pullbackFaceIso sourceNonempty targetNonempty mapping small small le_rfl := by
  letI := toricSchemeIntegral source sourceNonempty
  letI := toricSchemeIntegral target targetNonempty
  let face := source.isFaceOf_of_le large.property small.property included
  let localMap := faceAffineToricSchemeMap source.lattice face
  letI : IsOpenImmersion localMap :=
    (source.isToricCone large.property).rational.isOpenImmersion_faceAffineToricSchemeMap
      source.lattice face
  have comparison := frameComparison_restrict localMap
    ((atlas.pullback mapping).faceFrame sourceNonempty large large le_rfl)
    (atlas.pullbackFaceFrame targetNonempty mapping large large le_rfl)
    ((atlas.pullback mapping).faceFrame sourceNonempty large small included)
    (atlas.pullbackFaceFrame targetNonempty mapping large small included)
    (chartRestrictionIso localMap (source.affineToricChartι large)
      (source.affineToricChartι small)
      (Fan.faceAffineToricSchemeMap_comp_affineToricChartι face)
      ((atlas.pullback mapping).cartierDivisor sourceNonempty).sheaf)
    (chartRestrictionIso localMap (source.affineToricChartι large)
      (source.affineToricChartι small)
      (Fan.faceAffineToricSchemeMap_comp_affineToricChartι face)
      ((Scheme.Modules.pullback mapping.algebraicMap).obj (atlas.cartierDivisor targetNonempty).sheaf))
    ((atlas.pullback mapping).faceFrame_restrict sourceNonempty large large small le_rfl included)
    (atlas.pullbackFaceFrame_restrict targetNonempty mapping large large small le_rfl included)
  exact comparison.trans
    (atlas.pullbackFaceIso_independent sourceNonempty targetNonempty mapping large small small
      included le_rfl)

end ToricCharacterAtlas
end ToricPower
