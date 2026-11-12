module

public import ToricPower.CartierCore
public import ToricPower.SheafPullbackFrames

/-!
# Invertibility from actual open-immersion chart frames

The chart indices may live in a larger universe than the scheme. Choosing
one chart through each point produces an ordinary small rank-one atlas.
Every local comparison is transported through the chart's actual open image.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace ToricPower

universe u v

variable {X : Scheme.{u}}

/-- A frame on an open immersion gives a frame on its literal open image. -/
def unitFrameOnOpenImage {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : X.Modules) (frame : SheafOfModules.unit U.ringCatSheaf ≅ M.restrict j) :
    SheafOfModules.unit j.opensRange.toScheme.ringCatSheaf ≅
      M.restrict j.opensRange.ι :=
  (Scheme.Modules.restrictUnitIso j.isoOpensRange.inv).symm ≪≫
    (Scheme.Modules.restrictFunctor j.isoOpensRange.inv).mapIso frame ≪≫
      (moduleImageRestrictionIso j M).symm

/-- Actual rank-one frames on an arbitrary open cover prove invertibility. -/
theorem isInvertible_of_openCover_frames (cover : Scheme.OpenCover.{v} X)
    (M : X.Modules)
    (frames : ∀ i, SheafOfModules.unit (cover.X i).ringCatSheaf ≅
      M.restrict (cover.f i)) :
    TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X M := by
  let index (x : X) := (cover.isOpenCover_opensRange.exists_mem x).choose
  let W (x : X) := (cover.f (index x)).opensRange
  have contains (x : X) : x ∈ W x :=
    (cover.isOpenCover_opensRange.exists_mem x).choose_spec
  apply TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible_iff_exists_isOpenCover.mpr
  refine ⟨X, W, ?_, fun x => ⟨unitFrameOnOpenImage (cover.f (index x)) M (frames _)⟩⟩
  apply IsOpenCover.mk
  apply top_unique
  intro x _
  exact Opens.mem_iSup.mpr ⟨x, contains x⟩

end ToricPower
