module

public import ToricPower.CoherentRestriction
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.LocalIsomorphism

/-!
# Actual open restrictions and local isomorphism detection

These comparisons use the literal restriction functors and the actual
isomorphism from an open immersion to its image. They also retain the
ordinary restriction--pushforward counit on every selected chart.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Scheme.Modules

namespace ToricPower

universe u v

variable {A U X : Scheme.{u}}

def moduleRestrictionToImageIso (j : U ⟶ X) [IsOpenImmersion j] :
    restrictFunctor j ⋙ restrictFunctor j.isoOpensRange.inv ≅
      restrictFunctor j.opensRange.ι :=
  (restrictFunctorComp j.isoOpensRange.inv j).symm ≪≫
    restrictFunctorCongr (Scheme.Hom.isoOpensRange_inv_comp j)

def moduleImageToRestrictionIso (j : U ⟶ X) [IsOpenImmersion j] :
    restrictFunctor j.opensRange.ι ⋙ restrictFunctor j.isoOpensRange.hom ≅
      restrictFunctor j :=
  (restrictFunctorComp j.isoOpensRange.hom j.opensRange.ι).symm ≪≫
    restrictFunctorCongr (Scheme.Hom.isoOpensRange_hom_ι j)

/-- Restriction is an isomorphism exactly when the same map is an
isomorphism on its actual image-open slice. -/
theorem moduleRestriction_isIso_iff_over (j : U ⟶ X) [IsOpenImmersion j]
    {M N : X.Modules} (f : M ⟶ N) :
    IsIso ((restrictFunctor j).map f) ↔ IsIso (f.over j.opensRange) := by
  constructor
  · intro h
    letI := h
    have imageIso := (NatIso.isIso_map_iff (moduleRestrictionToImageIso j) f).mp
      (show IsIso ((restrictFunctor j ⋙ restrictFunctor j.isoOpensRange.inv).map f) from by
        change IsIso ((restrictFunctor j.isoOpensRange.inv).map ((restrictFunctor j).map f))
        infer_instance)
    have sliceIso := (NatIso.isIso_map_iff (overFunctorEquiv j.opensRange) f).mpr imageIso
    exact (isIso_iff_of_reflects_iso (f.over j.opensRange)
      (overEquiv j.opensRange).functor).mp sliceIso
  · intro h
    letI := h
    have imageIso := (NatIso.isIso_map_iff (overFunctorEquiv j.opensRange) f).mp
      (show IsIso
        ((SheafOfModules.overFunctor X.ringCatSheaf j.opensRange ⋙
          (overEquiv j.opensRange).functor).map f) from by
        change IsIso ((overEquiv j.opensRange).functor.map (f.over j.opensRange))
        infer_instance)
    letI := imageIso
    exact (NatIso.isIso_map_iff (moduleImageToRestrictionIso j) f).mp
      (show IsIso
        ((restrictFunctor j.opensRange.ι ⋙ restrictFunctor j.isoOpensRange.hom).map f) from by
        change IsIso ((restrictFunctor j.isoOpensRange.hom).map
          ((restrictFunctor j.opensRange.ι).map f))
        infer_instance)

/-- A jointly surjective family of actual open immersions detects
isomorphisms of module sheaves. -/
theorem moduleSheaf_isIso_of_openImmersionCover {I : Type v}
    (Y : I → Scheme.{u}) (j : ∀ a, Y a ⟶ X) [∀ a, IsOpenImmersion (j a)]
    (covers : ∀ x : X, ∃ a, ∃ y : Y a, j a y = x)
    {M N : X.Modules} (f : M ⟶ N)
    (localIso : ∀ a, IsIso ((restrictFunctor (j a)).map f)) : IsIso f := by
  have cover : (Opens.grothendieckTopology X).CoversTop (fun a => (j a).opensRange) := by
    apply (Opens.coversTop_iff X _).mpr
    apply IsOpenCover.mk
    apply top_unique
    intro x _
    obtain ⟨a,y,rfl⟩ := covers x
    exact Opens.mem_iSup.mpr ⟨a,⟨y,rfl⟩⟩
  exact SheafOfModules.isIso_of_coversTop cover f
    (fun a => (moduleRestriction_isIso_iff_over (j a) f).mp (localIso a))

/-- Restricting the actual open direct image to a chart already inside
the source recovers the original sheaf on that same chart. -/
def openPushforwardChartRestrictionIso (j : U ⟶ X) [IsOpenImmersion j]
    (a : A ⟶ U) [IsOpenImmersion a] (b : A ⟶ X) [IsOpenImmersion b]
    (square : a ≫ j = b) (M : U.Modules) :
    ((pushforward j).obj M).restrict b ≅ M.restrict a :=
  (restrictFunctorCongr square.symm).app ((pushforward j).obj M) ≪≫
    (restrictFunctorComp a j).app ((pushforward j).obj M) ≪≫
      (restrictFunctor a).mapIso ((restrictFunctorAdjCounitIso j).app M)

end ToricPower

end
