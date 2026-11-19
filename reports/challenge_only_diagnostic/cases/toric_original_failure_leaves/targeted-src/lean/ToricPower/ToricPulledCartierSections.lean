module

public import ToricPower.ToricPulledCartierCompatibility
public import ToricPower.SheafChartSectionComparison

/-!
# Actual section comparison for toric Cartier pullback

The equation-character pullback and the literal pullback of module sheaves
have isomorphic section groups on every toric chart. These isomorphisms
commute with the original sheaf restriction maps for all face inclusions.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 400000

open AlgebraicGeometry CategoryTheory MonoidalCategory TauCeti.Toric Opposite
open AlgebraicGeometry.Scheme.Modules
namespace ToricPower
universe u v
variable {N N' : Type u} {V V' : Type v}
  [AddCommGroup N] [AddCommGroup N'] [AddCommGroup V] [AddCommGroup V']
  [Module ℝ V] [Module ℝ V'] {i : N →+ V} {i' : N' →+ V'}
  {source : Fan i} {target : Fan i'}

namespace ToricCharacterAtlas

/-- Comparison on the actual original sheaf's sections over a toric chart. -/
def pullbackChartSectionsIso (atlas : ToricCharacterAtlas target)
    (sourceNonempty : Nonempty source.cones) (targetNonempty : Nonempty target.cones)
    (mapping : FanHom source target) (cone : source.cones) :
    letI := toricSchemeIntegral source sourceNonempty
    letI := toricSchemeIntegral target targetNonempty
    Γ(((atlas.pullback mapping).cartierDivisor sourceNonempty).sheaf,
      (source.affineToricChartι cone).opensRange) ≅
    Γ((Scheme.Modules.pullback mapping.algebraicMap).obj
      (atlas.cartierDivisor targetNonempty).sheaf,
      (source.affineToricChartι cone).opensRange) := by
  letI := toricSchemeIntegral source sourceNonempty
  letI := toricSchemeIntegral target targetNonempty
  exact moduleChartComparisonIso (source.affineToricChartι cone)
    (atlas.pullbackFaceIso sourceNonempty targetNonempty mapping cone cone le_rfl)

set_option maxRecDepth 4096 in
/-- The comparison commutes with every actual face restriction on
sections of the original sheaves. -/
theorem pullbackChartSectionsIso_restrict (atlas : ToricCharacterAtlas target)
    (sourceNonempty : Nonempty source.cones) (targetNonempty : Nonempty target.cones)
    (mapping : FanHom source target) (large small : source.cones) (included : small ≤ large) :
    letI := toricSchemeIntegral source sourceNonempty
    letI := toricSchemeIntegral target targetNonempty
    let original := ((atlas.pullback mapping).cartierDivisor sourceNonempty).sheaf
    let pulled := (Scheme.Modules.pullback mapping.algebraicMap).obj
      (atlas.cartierDivisor targetNonempty).sheaf
    (atlas.pullbackChartSectionsIso sourceNonempty targetNonempty mapping large).hom ≫
      pulled.presheaf.map (homOfLE (toricChart_opensRange_mono source included)).op =
    original.presheaf.map (homOfLE (toricChart_opensRange_mono source included)).op ≫
      (atlas.pullbackChartSectionsIso sourceNonempty targetNonempty mapping small).hom := by
  letI := toricSchemeIntegral source sourceNonempty
  letI := toricSchemeIntegral target targetNonempty
  let face := source.isFaceOf_of_le large.property small.property included
  let localMap := faceAffineToricSchemeMap source.lattice face
  letI : IsOpenImmersion localMap :=
    (source.isToricCone large.property).rational.isOpenImmersion_faceAffineToricSchemeMap
      source.lattice face
  exact moduleChartSectionsIso_restrict_of_iso localMap (source.affineToricChartι large)
    (source.affineToricChartι small)
    (Fan.faceAffineToricSchemeMap_comp_affineToricChartι face)
    (M := ((atlas.pullback mapping).cartierDivisor sourceNonempty).sheaf)
    (N := (Scheme.Modules.pullback mapping.algebraicMap).obj
      (atlas.cartierDivisor targetNonempty).sheaf)
    (atlas.pullbackFaceIso sourceNonempty targetNonempty mapping large large le_rfl)
    (atlas.pullbackFaceIso sourceNonempty targetNonempty mapping small small le_rfl)
    (atlas.pullbackFaceIso_restrict sourceNonempty targetNonempty mapping large small included)

end ToricCharacterAtlas
end ToricPower
