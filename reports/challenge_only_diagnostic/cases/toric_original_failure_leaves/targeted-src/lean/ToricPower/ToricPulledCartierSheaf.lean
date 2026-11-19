module

public import ToricPower.ToricPulledCartierCompatibility
public import ToricPower.ChartIsomorphismGluing

/-!
# The global sheaf of the pulled-back toric Cartier atlas

The equation-character pullback is identified with the literal pullback
of the actual Cartier line sheaf. This is a global sheaf isomorphism,
obtained by gluing the already established local frame comparisons.
It applies to arbitrary fan morphisms, including nondominant ones.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory TopologicalSpace TauCeti.Toric
open Scheme.Modules

namespace ToricPower.ToricCharacterAtlas

universe u v

variable {N N' : Type u} {V V' : Type v}
  [AddCommGroup N] [AddCommGroup N'] [AddCommGroup V] [AddCommGroup V']
  [Module ℝ V] [Module ℝ V'] {i : N →+ V} {i' : N' →+ V'}
  {source : Fan i} {target : Fan i'}

/-- Literal pullback of the Cartier line agrees with pullback of its
character equations, globally and without any dominance assumption. -/
def pullbackSheafIso (atlas : ToricCharacterAtlas target)
    (sourceNonempty : Nonempty source.cones) (targetNonempty : Nonempty target.cones)
    (mapping : FanHom source target) :
    letI := toricSchemeIntegral source sourceNonempty
    letI := toricSchemeIntegral target targetNonempty
    ((atlas.pullback mapping).cartierDivisor sourceNonempty).sheaf ≅
      (Scheme.Modules.pullback mapping.algebraicMap).obj
        (atlas.cartierDivisor targetNonempty).sheaf := by
  letI := toricSchemeIntegral source sourceNonempty
  letI := toricSchemeIntegral target targetNonempty
  let face (small large : source.cones) (h : small ≤ large) :=
    faceAffineToricSchemeMap source.lattice
      (source.isFaceOf_of_le large.property small.property h)
  letI : ∀ (small large : source.cones) (h : small ≤ large),
      IsOpenImmersion (face small large h) := fun small large h =>
    (source.isToricCone large.property).rational.isOpenImmersion_faceAffineToricSchemeMap
      source.lattice (source.isFaceOf_of_le large.property small.property h)
  have square (small large : source.cones) (h : small ≤ large) :
      face small large h ≫ source.affineToricChartι large = source.affineToricChartι small :=
    Fan.faceAffineToricSchemeMap_comp_affineToricChartι
      (source.isFaceOf_of_le large.property small.property h)
  have covers : IsOpenCover (fun σ => (source.affineToricChartι σ).opensRange) := by
    apply IsOpenCover.mk
    apply top_unique
    intro x _
    obtain ⟨σ,y,rfl⟩ := source.exists_affineToricChartι_apply_eq x
    exact Opens.mem_iSup.mpr ⟨σ,⟨y,rfl⟩⟩
  exact chartGluedIso (faceOpen := fun small large h =>
      (source.isToricCone large.property).rational.isOpenImmersion_faceAffineToricSchemeMap
        source.lattice (source.isFaceOf_of_le large.property small.property h))
    source.affineToricChart source.affineToricChartι face square
    (chart_opensRange_intersection source) covers
    (fun σ => atlas.pullbackFaceIso sourceNonempty targetNonempty mapping σ σ le_rfl)
    (fun small large h => atlas.pullbackFaceIso_restrict
      sourceNonempty targetNonempty mapping large small h)

end ToricPower.ToricCharacterAtlas

end
