module

public import ToricPower.ToricAtlasFrameTransitions
public import ToricPower.SheafChartPullbackTransitions

/-!
# Frames of the actual pullback of a toric Cartier line sheaf

Every source face chart is mapped into its least target chart. Reading
each target equation on this common chart gives frames of the literal
module-sheaf pullback. Their transition functions are exactly those of
the Cartier atlas obtained by composing equation characters with the
lattice homomorphism. No function-field map is used.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 750000

open AlgebraicGeometry CategoryTheory MonoidalCategory TauCeti.Toric
open AlgebraicGeometry.Scheme.Modules

namespace ToricPower
universe u v

private theorem frameComparison_eq_of_common_transition
    {C : Type*} [Category C] {U M N : C}
    (sourceFirst sourceSecond : U ≅ M) (targetFirst targetSecond : U ≅ N)
    (scalar : U ⟶ U)
    (sourceTransition : sourceFirst.hom = scalar ≫ sourceSecond.hom)
    (targetTransition : targetFirst.hom = scalar ≫ targetSecond.hom) :
    sourceFirst.symm ≪≫ targetFirst = sourceSecond.symm ≪≫ targetSecond := by
  apply Iso.ext
  apply (cancel_epi sourceFirst.hom).mp
  simp only [Iso.trans_hom, Iso.symm_hom, ← Category.assoc, Iso.hom_inv_id,
    Category.id_comp]
  rw [sourceTransition]
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using targetTransition

variable {N N' : Type u} {V V' : Type v}
  [AddCommGroup N] [AddCommGroup N'] [AddCommGroup V] [AddCommGroup V']
  [Module ℝ V] [Module ℝ V'] {i : N →+ V} {i' : N' →+ V'}
  {source : Fan i} {target : Fan i'}

namespace ToricCharacterAtlas

/-- The frame of the actual pulled-back line sheaf obtained from a target
equation, read on an arbitrary source face chart. -/
def pullbackFaceFrame (atlas : ToricCharacterAtlas target)
    (nonempty : Nonempty target.cones) (mapping : FanHom source target)
    (index cone : source.cones) (included : cone ≤ index) :
    letI := toricSchemeIntegral target nonempty
    𝟙_ (source.affineToricChart cone).Modules ≅
      ((Scheme.Modules.pullback mapping.algebraicMap).obj
        (atlas.cartierDivisor nonempty).sheaf).restrict (source.affineToricChartι cone) := by
  letI := toricSchemeIntegral target nonempty
  exact chartPullbackFrame mapping.algebraicMap (source.affineToricChartι cone)
    (target.affineToricChartι (fanMapTargetCone mapping cone))
    (mapping.affineToricChartMap cone) (mapping.affineToricChartι_comp_algebraicMap cone)
    (atlas.cartierDivisor nonempty).sheaf
    (atlas.faceFrame nonempty (fanMapTargetCone mapping index) (fanMapTargetCone mapping cone)
      (mapping.leastCone_mono cone.property index.property included))

/-- The literal coordinate homomorphism sends each target transition
unit to the transition unit of the composed character atlas. -/
theorem pullback_frameTransitionUnit (atlas : ToricCharacterAtlas target)
    (mapping : FanHom source target) (first second cone : source.cones)
    (inFirst : cone ≤ first) (inSecond : cone ≤ second) :
    Units.map (affineCoordinateRingMap source.lattice target.lattice mapping.latticeMap
      mapping.realMap mapping.map_lattice (mapping.mapsTo_leastCone cone.property)).toMonoidHom
      (atlas.frameTransitionUnit (fanMapTargetCone mapping first) (fanMapTargetCone mapping second)
        (fanMapTargetCone mapping cone)
        (mapping.leastCone_mono cone.property first.property inFirst)
        (mapping.leastCone_mono cone.property second.property inSecond)) =
    (atlas.pullback mapping).frameTransitionUnit first second cone inFirst inSecond := by
  simpa only [frameTransitionUnit, pullback_equation, ← AddMonoidHom.sub_comp,
    fanMapTargetCone] using
    toricMonomialUnit_fanMap source target mapping (mapping.mapsTo_leastCone cone.property)
      (atlas.equation (fanMapTargetCone mapping second) -
        atlas.equation (fanMapTargetCone mapping first))
      (dualSemigroup_anti target.lattice
        (le_inf (mapping.leastCone_mono cone.property second.property inSecond)
          (mapping.leastCone_mono cone.property first.property inFirst))
        (atlas.positive (fanMapTargetCone mapping second) (fanMapTargetCone mapping first)))
      (dualSemigroup_anti target.lattice
        (le_inf (mapping.leastCone_mono cone.property second.property inSecond)
          (mapping.leastCone_mono cone.property first.property inFirst))
        (atlas.negative (fanMapTargetCone mapping second) (fanMapTargetCone mapping first)))

/-- On actual global chart sections, transition functions pull back by
the actual map of affine toric schemes. -/
theorem pullback_frameTransitionSection (atlas : ToricCharacterAtlas target)
    (mapping : FanHom source target) (first second cone : source.cones)
    (inFirst : cone ≤ first) (inSecond : cone ≤ second) :
    (mapping.affineToricChartMap cone).appTop
      (affineGlobalSectionsEquiv (affineCoordinateRing target.lattice
        (fanMapTargetCone mapping cone).val)
        (atlas.frameTransitionUnit (fanMapTargetCone mapping first) (fanMapTargetCone mapping second)
          (fanMapTargetCone mapping cone)
          (mapping.leastCone_mono cone.property first.property inFirst)
          (mapping.leastCone_mono cone.property second.property inSecond) :
            affineCoordinateRing target.lattice (fanMapTargetCone mapping cone).val)) =
    affineGlobalSectionsEquiv (affineCoordinateRing source.lattice cone.val)
      ((atlas.pullback mapping).frameTransitionUnit first second cone inFirst inSecond :
        affineCoordinateRing source.lattice cone.val) := by
  let unit := atlas.frameTransitionUnit (fanMapTargetCone mapping first)
    (fanMapTargetCone mapping second) (fanMapTargetCone mapping cone)
    (mapping.leastCone_mono cone.property first.property inFirst)
    (mapping.leastCone_mono cone.property second.property inSecond)
  have affine : (mapping.affineToricChartMap cone).appTop
      (affineGlobalSectionsEquiv (affineCoordinateRing target.lattice
        (fanMapTargetCone mapping cone).val) unit.val) =
    affineGlobalSectionsEquiv (affineCoordinateRing source.lattice cone.val)
      (affineCoordinateRingMap source.lattice target.lattice mapping.latticeMap mapping.realMap
        mapping.map_lattice (mapping.mapsTo_leastCone cone.property) unit.val) := by
    rw [mapping.affineToricChartMap_def]
    exact affineGlobalSectionsEquiv_toricMap source target mapping
      (mapping.mapsTo_leastCone cone.property) unit.val
  exact affine.trans (congrArg
    (affineGlobalSectionsEquiv (affineCoordinateRing source.lattice cone.val))
    (congrArg Units.val
      (atlas.pullback_frameTransitionUnit mapping first second cone inFirst inSecond)))

/-- The actual pulled-back sheaf has exactly the scalar transitions of
the character-pullback Cartier atlas. -/
theorem pullbackFaceFrame_transition (atlas : ToricCharacterAtlas target)
    (nonempty : Nonempty target.cones) (mapping : FanHom source target)
    (first second cone : source.cones) (inFirst : cone ≤ first) (inSecond : cone ≤ second) :
    letI := toricSchemeIntegral target nonempty
    (atlas.pullbackFaceFrame nonempty mapping first cone inFirst).hom =
      globalSectionsSmul (𝟙_ (source.affineToricChart cone).Modules)
        (affineGlobalSectionsEquiv (affineCoordinateRing source.lattice cone.val)
          ((atlas.pullback mapping).frameTransitionUnit first second cone inFirst inSecond :
            affineCoordinateRing source.lattice cone.val)) ≫
        (atlas.pullbackFaceFrame nonempty mapping second cone inSecond).hom := by
  letI := toricSchemeIntegral target nonempty
  have transition := chartPullbackFrame_scalar mapping.algebraicMap (source.affineToricChartι cone)
    (target.affineToricChartι (fanMapTargetCone mapping cone))
    (mapping.affineToricChartMap cone) (mapping.affineToricChartι_comp_algebraicMap cone)
    (atlas.cartierDivisor nonempty).sheaf
    (atlas.faceFrame nonempty (fanMapTargetCone mapping first) (fanMapTargetCone mapping cone)
      (mapping.leastCone_mono cone.property first.property inFirst))
    (atlas.faceFrame nonempty (fanMapTargetCone mapping second) (fanMapTargetCone mapping cone)
      (mapping.leastCone_mono cone.property second.property inSecond))
    _ (atlas.faceFrame_transition nonempty (fanMapTargetCone mapping first)
      (fanMapTargetCone mapping second) (fanMapTargetCone mapping cone)
      (mapping.leastCone_mono cone.property first.property inFirst)
      (mapping.leastCone_mono cone.property second.property inSecond))
  exact transition.trans (congrArg (fun scalar : Γ(source.affineToricChart cone, ⊤) =>
    globalSectionsSmul (𝟙_ (source.affineToricChart cone).Modules) scalar ≫
      (atlas.pullbackFaceFrame nonempty mapping second cone inSecond).hom)
    (atlas.pullback_frameTransitionSection mapping first second cone inFirst inSecond))

/-- Compare the actual character-pullback Cartier line with the actual
module-sheaf pullback on any common face chart. -/
def pullbackFaceIso (atlas : ToricCharacterAtlas target)
    (sourceNonempty : Nonempty source.cones) (targetNonempty : Nonempty target.cones)
    (mapping : FanHom source target) (index cone : source.cones) (included : cone ≤ index) :
    letI := toricSchemeIntegral source sourceNonempty
    letI := toricSchemeIntegral target targetNonempty
    ((atlas.pullback mapping).cartierDivisor sourceNonempty).sheaf.restrict
        (source.affineToricChartι cone) ≅
      ((Scheme.Modules.pullback mapping.algebraicMap).obj
        (atlas.cartierDivisor targetNonempty).sheaf).restrict (source.affineToricChartι cone) := by
  letI := toricSchemeIntegral source sourceNonempty
  letI := toricSchemeIntegral target targetNonempty
  exact ((atlas.pullback mapping).faceFrame sourceNonempty index cone included).symm ≪≫
    atlas.pullbackFaceFrame targetNonempty mapping index cone included

/-- The local comparison is independent of which containing cone supplied
its equation. This is an equality of actual module-sheaf isomorphisms. -/
theorem pullbackFaceIso_independent (atlas : ToricCharacterAtlas target)
    (sourceNonempty : Nonempty source.cones) (targetNonempty : Nonempty target.cones)
    (mapping : FanHom source target) (first second cone : source.cones)
    (inFirst : cone ≤ first) (inSecond : cone ≤ second) :
    atlas.pullbackFaceIso sourceNonempty targetNonempty mapping first cone inFirst =
      atlas.pullbackFaceIso sourceNonempty targetNonempty mapping second cone inSecond := by
  letI := toricSchemeIntegral source sourceNonempty
  letI := toricSchemeIntegral target targetNonempty
  exact frameComparison_eq_of_common_transition _ _ _ _ _
    ((atlas.pullback mapping).faceFrame_transition sourceNonempty first second cone inFirst inSecond)
    (atlas.pullbackFaceFrame_transition targetNonempty mapping first second cone inFirst inSecond)

end ToricCharacterAtlas
end ToricPower
