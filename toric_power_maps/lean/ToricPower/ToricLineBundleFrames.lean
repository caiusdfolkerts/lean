module

public import ToricPower.AffinePicard
public import ToricPower.ToricLaurentUnits
public import ToricPower.CartierRepresentation

/-! # Actual toric line-bundle frames without completeness

The restriction comparison is retained from BondalThomsen's
Toric/Divisor/PicardSurjective.lean at commit
9a2bdcdcf6b25710459f7f476c9c62de3039b7bb, under its original license.
The toric constructions use factoriality for each regular cone separately.
They do not choose complete fans or full-dimensional cones. This source is
uncompiled development work.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace ToricPower.InvertibleRestriction

universe u

theorem invertible_restrict {source target : Scheme.{u}}
    (inclusion : source ⟶ target) [IsOpenImmersion inclusion]
    (sheaf : target.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible target sheaf] :
    TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible source (sheaf.restrict inclusion) := by
  let atlas := TauCeti.SheafOfModules.LocalTrivializations.ofIsInvertible sheaf
  apply TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible_iff_exists_isOpenCover.mpr
  refine ⟨atlas.I, fun index => inclusion ⁻¹ᵁ atlas.X index, ?_, ?_⟩
  · apply IsOpenCover.mk
    apply top_unique
    intro point member
    have covered := (Opens.coversTop_iff target.carrier atlas.X).mp atlas.coversTop
    obtain ⟨index, contains⟩ := Opens.mem_iSup.mp
      (covered.symm ▸ (show inclusion point ∈ (⊤ : target.Opens) from trivial))
    exact Opens.mem_iSup.mpr ⟨index, contains⟩
  · intro index
    let localMap := inclusion.resLE (atlas.X index) (inclusion ⁻¹ᵁ atlas.X index) le_rfl
    have factorization : localMap ≫ Scheme.Opens.ι (atlas.X index) =
        Scheme.Opens.ι (inclusion ⁻¹ᵁ atlas.X index) ≫ inclusion :=
      inclusion.resLE_comp_ι le_rfl
    letI : IsOpenImmersion (localMap ≫ Scheme.Opens.ι (atlas.X index)) := by
      rw [factorization]
      infer_instance
    letI : IsOpenImmersion localMap := IsOpenImmersion.of_comp
      localMap (Scheme.Opens.ι (atlas.X index))
    let comparison := (Scheme.Modules.restrictFunctorComp
      (inclusion ⁻¹ᵁ atlas.X index).ι inclusion).symm.app sheaf ≪≫
      (Scheme.Modules.restrictFunctorCongr
        factorization.symm).app sheaf ≪≫
      (Scheme.Modules.restrictFunctorComp localMap (Scheme.Opens.ι (atlas.X index))).app sheaf
    exact ⟨(comparison ≪≫ (Scheme.Modules.restrictFunctor localMap).mapIso
      (TauCeti.SheafOfModules.LocalTrivializations.unitIsoRestrict (atlas.iso index)).symm ≪≫
        Scheme.Modules.restrictUnitIso localMap).symm⟩

noncomputable def openImageTrivialization {source target : Scheme.{u}}
    (inclusion : source ⟶ target) [IsOpenImmersion inclusion]
    (sheaf : target.Modules)
    (trivialization : sheaf.restrict inclusion ≅ SheafOfModules.unit source.ringCatSheaf) :
    SheafOfModules.free (R := target.ringCatSheaf.over inclusion.opensRange) PUnit ≅
      sheaf.over inclusion.opensRange := by
  let imageIso := inclusion.isoOpensRange
  let imageTrivialization :=
    (Scheme.Modules.restrictFunctorCongr inclusion.isoOpensRange_inv_comp.symm).app sheaf ≪≫
      (Scheme.Modules.restrictFunctorComp imageIso.inv inclusion).app sheaf ≪≫
      (Scheme.Modules.restrictFunctor imageIso.inv).mapIso trivialization ≪≫
      Scheme.Modules.restrictUnitIso imageIso.inv
  exact (Scheme.Modules.overEquiv inclusion.opensRange).fullyFaithfulFunctor.preimageIso
    ((Scheme.Modules.overEquiv inclusion.opensRange).functor.mapIso
        (TauCeti.SheafOfModules.freePUnitIsoUnit _) ≪≫
      Opens.sheafOfModulesEquivOverUnit inclusion.opensRange target.ringCatSheaf ≪≫
      imageTrivialization.symm ≪≫
      ((Scheme.Modules.overFunctorEquiv inclusion.opensRange).app sheaf).symm)

end ToricPower.InvertibleRestriction

namespace ToricPower

open TauCeti.Toric

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

def toricInvertibleChartUnitIso (fan : Fan i) (regular : fan.IsRegular)
    (cone : fan.cones) (F : fan.algebraicRealization.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible fan.algebraicRealization F] :
    F.restrict (fan.affineToricChartι cone) ≅
      SheafOfModules.unit (fan.affineToricChart cone).ringCatSheaf := by
  letI := InvertibleRestriction.invertible_restrict (fan.affineToricChartι cone) F
  exact regularAffineInvertibleSheafUnitIso fan.lattice
    ((Fan.isRegular_iff (Φ := fan)).mp regular cone.val cone.property) _

def toricInvertibleTorusUnitIso (fan : Fan i) (nonempty : Nonempty fan.cones)
    (F : fan.algebraicRealization.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible fan.algebraicRealization F] :
    F.restrict (fan.denseTorusι nonempty) ≅
      SheafOfModules.unit fan.denseTorus.ringCatSheaf := by
  letI := InvertibleRestriction.invertible_restrict (fan.denseTorusι nonempty) F
  exact regularAffineInvertibleSheafUnitIso fan.lattice (isRegularCone_bot fan.lattice) _

def toricLineBundleChartFrame (fan : Fan i) (regular : fan.IsRegular)
    (cone : fan.cones) (F : fan.algebraicRealization.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible fan.algebraicRealization F] :
    SheafOfModules.free
      (R := fan.algebraicRealization.ringCatSheaf.over (fan.affineToricChartι cone).opensRange)
      PUnit ≅ F.over (fan.affineToricChartι cone).opensRange :=
  InvertibleRestriction.openImageTrivialization _ F
    (toricInvertibleChartUnitIso fan regular cone F)

def toricLineBundleTorusFrame (fan : Fan i) (nonempty : Nonempty fan.cones)
    (F : fan.algebraicRealization.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible fan.algebraicRealization F] :
    SheafOfModules.free
      (R := fan.algebraicRealization.ringCatSheaf.over (fan.denseTorusι nonempty).opensRange)
      PUnit ≅ F.over (fan.denseTorusι nonempty).opensRange :=
  InvertibleRestriction.openImageTrivialization _ F
    (toricInvertibleTorusUnitIso fan nonempty F)

theorem toricTorusOpen_dense (fan : Fan i) (nonempty : Nonempty fan.cones) :
    Dense ((fan.denseTorusι nonempty).opensRange : Set fan.algebraicRealization) := by
  letI := toricSchemeIntegral fan nonempty
  letI : IsIntegral fan.denseTorus := inferInstance
  change DenseRange (fan.denseTorusι nonempty)
  exact IsOpenMap.denseRange_of_isPreirreducibleSpace _
    (fan.denseTorusι nonempty).isOpenEmbedding.isOpenMap

/-- Every actual line bundle has a Cartier representative vanishing on
the actual dense torus. The sheaf isomorphism is constructed, not assumed. -/
theorem toricLineBundle_exists_cartier_zero_on_torus (fan : Fan i)
    (nonempty : Nonempty fan.cones) (F : fan.algebraicRealization.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible fan.algebraicRealization F] :
    letI := toricSchemeIntegral fan nonempty
    ∃ D : TauCeti.AlgebraicGeometry.Scheme.CartierDivisor fan.algebraicRealization,
      D |_ (fan.denseTorusι nonempty).opensRange = 0 ∧ Nonempty (F ≅ D.sheaf) := by
  letI := toricSchemeIntegral fan nonempty
  exact exists_cartierDivisor_zero_on_trivializing_open F
    (toricLineBundleTorusFrame fan nonempty F) (toricTorusOpen_dense fan nonempty)

end ToricPower
