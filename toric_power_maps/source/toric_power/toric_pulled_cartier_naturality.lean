module

public import ToricPower.ToricPulledCartierFrames
public import ToricPower.SheafChartPullbackRefinement

/-!
# Face compatibility of actual toric pullback frames

The frames of the character-pullback divisor and of the genuine sheaf
pullback both restrict along the actual toric face maps. Together with
the equality of transition functions, this supplies the local natural
comparison used in descent and in the actual Čech complex.
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

private theorem identityIso_app {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (x : C) : (Iso.refl F).app x = Iso.refl (F.obj x) := rfl

namespace CartierEquationAtlas

theorem affineFrame_congr {X A : Scheme.{u}} [IsIntegral X]
    (atlas : CartierEquationAtlas.{u,v} X) (index : atlas.Index)
    {chart chart' : A ⟶ X} [IsOpenImmersion chart] [IsOpenImmersion chart']
    (equal : chart = chart') (included : chart.opensRange ≤ atlas.chart index)
    (included' : chart'.opensRange ≤ atlas.chart index) :
    atlas.affineFrame index chart included ≪≫
      (restrictFunctorCongr equal).app atlas.cartierDivisor.sheaf =
    atlas.affineFrame index chart' included' := by
  subst chart'
  rw [restrictFunctorCongr_refl, identityIso_app, Iso.trans_refl]

end CartierEquationAtlas

variable {N N' : Type u} {V V' : Type v}
  [AddCommGroup N] [AddCommGroup N'] [AddCommGroup V] [AddCommGroup V']
  [Module ℝ V] [Module ℝ V'] {i : N →+ V} {i' : N' →+ V'}
  {source : Fan i} {target : Fan i'}

namespace ToricCharacterAtlas

/-- Actual Cartier frames restrict to the frame for the same equation
on every smaller face chart, with the canonical chart comparisons. -/
theorem faceFrame_restrict {fan : Fan i} (atlas : ToricCharacterAtlas fan)
    (nonempty : Nonempty fan.cones) (index large small : fan.cones)
    (inIndex : large ≤ index) (included : small ≤ large) :
    letI := toricSchemeIntegral fan nonempty
    let face := fan.isFaceOf_of_le large.property small.property included
    letI := (fan.isToricCone large.property).rational.isOpenImmersion_faceAffineToricSchemeMap
      fan.lattice face
    restrictModuleFrame (faceAffineToricSchemeMap fan.lattice face)
        (atlas.faceFrame nonempty index large inIndex) ≪≫
      ((restrictFunctorComp (faceAffineToricSchemeMap fan.lattice face)
        (fan.affineToricChartι large)).app (atlas.cartierDivisor nonempty).sheaf).symm ≪≫
      (restrictFunctorCongr
        (Fan.faceAffineToricSchemeMap_comp_affineToricChartι face)).app
          (atlas.cartierDivisor nonempty).sheaf =
    atlas.faceFrame nonempty index small (included.trans inIndex) := by
  letI := toricSchemeIntegral fan nonempty
  let face := fan.isFaceOf_of_le large.property small.property included
  let localMap := faceAffineToricSchemeMap fan.lattice face
  letI : IsOpenImmersion localMap :=
    (fan.isToricCone large.property).rational.isOpenImmersion_faceAffineToricSchemeMap
      fan.lattice face
  let actualAtlas := atlas.cartierEquationAtlas nonempty
  have square : localMap ≫ fan.affineToricChartι large = fan.affineToricChartι small :=
    Fan.faceAffineToricSchemeMap_comp_affineToricChartι face
  have smallerIncluded : (localMap ≫ fan.affineToricChartι large).opensRange ≤
      actualAtlas.chart index := by
    change (localMap ≫ fan.affineToricChartι large).opensRange ≤
      (fan.affineToricChartι index).opensRange
    rintro point ⟨localPoint, rfl⟩
    exact toricChart_opensRange_mono fan (included.trans inIndex)
      ⟨localPoint, (congrArg (fun mapping => mapping localPoint) square).symm⟩
  exact (congrArg (fun frame => frame ≪≫
      (restrictFunctorCongr square).app (atlas.cartierDivisor nonempty).sheaf)
    (actualAtlas.affineFrame_restrict index (fan.affineToricChartι large) localMap
      (toricChart_opensRange_mono fan inIndex) smallerIncluded)).trans
    (actualAtlas.affineFrame_congr index square smallerIncluded
      (toricChart_opensRange_mono fan (included.trans inIndex)))

/-- The genuine pulled-back frames restrict through the simultaneous
source/target face square. This is compatibility of actual sheaf maps. -/
theorem pullbackFaceFrame_restrict (atlas : ToricCharacterAtlas target)
    (nonempty : Nonempty target.cones) (mapping : FanHom source target)
    (index large small : source.cones) (inIndex : large ≤ index) (included : small ≤ large) :
    letI := toricSchemeIntegral target nonempty
    let face := source.isFaceOf_of_le large.property small.property included
    letI := (source.isToricCone large.property).rational.isOpenImmersion_faceAffineToricSchemeMap
      source.lattice face
    let pulled := (Scheme.Modules.pullback mapping.algebraicMap).obj
      (atlas.cartierDivisor nonempty).sheaf
    restrictModuleFrame (faceAffineToricSchemeMap source.lattice face)
        (atlas.pullbackFaceFrame nonempty mapping index large inIndex) ≪≫
      ((restrictFunctorComp (faceAffineToricSchemeMap source.lattice face)
        (source.affineToricChartι large)).app pulled).symm ≪≫
      (restrictFunctorCongr
        (Fan.faceAffineToricSchemeMap_comp_affineToricChartι face)).app pulled =
    atlas.pullbackFaceFrame nonempty mapping index small (included.trans inIndex) := by
  letI := toricSchemeIntegral target nonempty
  let face := source.isFaceOf_of_le large.property small.property included
  let targetFace := mapping.leastCone_isFaceOf large.property face
  letI := (source.isToricCone large.property).rational.isOpenImmersion_faceAffineToricSchemeMap
    source.lattice face
  letI := (target.isToricCone (mapping.leastCone_mem large.property)).rational.isOpenImmersion_faceAffineToricSchemeMap
    target.lattice targetFace
  exact chartPullbackFrame_refine mapping.algebraicMap
    (source.affineToricChartι large) (source.affineToricChartι small)
    (target.affineToricChartι (fanMapTargetCone mapping large))
    (target.affineToricChartι (fanMapTargetCone mapping small))
    (faceAffineToricSchemeMap source.lattice face)
    (faceAffineToricSchemeMap target.lattice targetFace)
    (mapping.affineToricChartMap large) (mapping.affineToricChartMap small)
    (Fan.faceAffineToricSchemeMap_comp_affineToricChartι face)
    (Fan.faceAffineToricSchemeMap_comp_affineToricChartι targetFace)
    (mapping.faceAffineToricSchemeMap_comp_affineToricChartMap face)
    (mapping.affineToricChartι_comp_algebraicMap large)
    (mapping.affineToricChartι_comp_algebraicMap small)
    (atlas.cartierDivisor nonempty).sheaf
    (atlas.faceFrame nonempty (fanMapTargetCone mapping index) (fanMapTargetCone mapping large)
      (mapping.leastCone_mono large.property index.property inIndex))
    (atlas.faceFrame nonempty (fanMapTargetCone mapping index) (fanMapTargetCone mapping small)
      (mapping.leastCone_mono small.property index.property (included.trans inIndex)))
    (atlas.faceFrame_restrict nonempty (fanMapTargetCone mapping index)
      (fanMapTargetCone mapping large) (fanMapTargetCone mapping small)
      (mapping.leastCone_mono large.property index.property inIndex)
      (mapping.leastCone_mono small.property large.property included))

end ToricCharacterAtlas
end ToricPower
