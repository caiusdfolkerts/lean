module

public import ToricPower.SheafPullbackSquareFrames

/-!
# Ordinary restrictions of genuine pulled-back frames

The canonical pullback square comparison is compatible with ordinary
restriction to a smaller source chart. This is the coherence needed to
glue actual Cartier line-sheaf comparisons over a toric affine cover.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory MonoidalCategory
open AlgebraicGeometry.Scheme.Modules

namespace ToricPower
universe u
variable {A B C X Y : Scheme.{u}}

/-- The restriction/pullback comparison with its two intermediate factors
in the order used by normalized pullback of frames. -/
theorem restrictionComparison_comp (c : C ⟶ A) (a : A ⟶ X)
    [IsOpenImmersion c] [IsOpenImmersion a] (M : X.Modules) :
    (restrictFunctorComp c a).app M ≪≫
      (restrictFunctorIsoPullback c).app (M.restrict a) ≪≫
      (pullback c).mapIso ((restrictFunctorIsoPullback a).app M) ≪≫
      (pullbackComp c a).app M = (restrictFunctorIsoPullback (c ≫ a)).app M := by
  apply Iso.ext
  simp only [Iso.trans_hom, CategoryTheory.Functor.mapIso_hom, Iso.app_hom,
    Category.assoc (obj := C.Modules)]
  rw [← (restrictFunctorIsoPullback c).hom.naturality_assoc
    ((restrictFunctorIsoPullback a).hom.app M)]
  exact restrictFunctorComp_toPullback_app c a M

/-- The inverse comparison, in the order in which it occurs after pulling
back an ordinary chart frame. -/
theorem restrictionComparison_inverse (c : C ⟶ A) (a : A ⟶ X)
    [IsOpenImmersion c] [IsOpenImmersion a] (M : X.Modules) :
    (pullback c).mapIso ((restrictFunctorIsoPullback a).app M).symm ≪≫
      ((restrictFunctorIsoPullback c).app (M.restrict a)).symm ≪≫
      ((restrictFunctorComp c a).app M).symm =
        (pullbackComp c a).app M ≪≫ ((restrictFunctorIsoPullback (c ≫ a)).app M).symm := by
  have comparison := congrArg Iso.inv (restrictionComparison_comp c a M)
  have normalized := congrArg
    (fun mapping => (pullbackComp c a).hom.app M ≫ mapping) comparison
  apply Iso.ext
  simpa only [Iso.trans_inv, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    CategoryTheory.Functor.mapIso_inv, CategoryTheory.Functor.mapIso_hom,
    Category.assoc (obj := C.Modules), Iso.hom_inv_id_app_assoc] using normalized

/-- An ordinary restricted frame is its genuine normalized pullback,
followed by the canonical inverse comparison. -/
theorem restrictModuleFrame_asPullback (c : C ⟶ A) [IsOpenImmersion c]
    {M : A.Modules} (frame : 𝟙_ A.Modules ≅ M) :
    restrictModuleFrame c frame =
      pullbackModuleFrame c frame ≪≫ ((restrictFunctorIsoPullback c).app M).symm := by
  rw [← restrictModuleFrame_pullback c frame, Iso.trans_assoc, Iso.self_symm_id,
    Iso.trans_refl]

/-- Transport a chart frame through an arbitrary commuting scheme square.
The construction uses actual module-sheaf pullback, with no dominance
assumption on the scheme morphism. -/
def chartPullbackFrame (f : X ⟶ Y) (a : A ⟶ X) [IsOpenImmersion a]
    (b : B ⟶ Y) [IsOpenImmersion b] (g : A ⟶ B) (square : a ≫ f = g ≫ b)
    (M : Y.Modules) (frame : 𝟙_ B.Modules ≅ M.restrict b) :
    𝟙_ A.Modules ≅ ((pullback f).obj M).restrict a :=
  squarePullbackFrame f a b g square (frame ≪≫ (restrictFunctorIsoPullback b).app M) ≪≫
    ((restrictFunctorIsoPullback a).app ((pullback f).obj M)).symm

/-- Restricting a pulled-back chart frame to a smaller source chart is
exactly the frame obtained from the pasted commuting square. -/
theorem chartPullbackFrame_precompose (f : X ⟶ Y) (a : A ⟶ X)
    [IsOpenImmersion a] (b : B ⟶ Y) [IsOpenImmersion b] (g : A ⟶ B)
    (square : a ≫ f = g ≫ b) (c : C ⟶ A) [IsOpenImmersion c]
    (M : Y.Modules) (frame : 𝟙_ B.Modules ≅ M.restrict b)
    (pasted : (c ≫ a) ≫ f = (c ≫ g) ≫ b) :
    restrictModuleFrame c (chartPullbackFrame f a b g square M frame) ≪≫
      ((restrictFunctorComp c a).app ((pullback f).obj M)).symm =
    chartPullbackFrame f (c ≫ a) b (c ≫ g) pasted M frame := by
  rw [restrictModuleFrame_asPullback]
  simp only [chartPullbackFrame, pullbackModuleFrame_trans, Iso.trans_assoc]
  rw [restrictionComparison_inverse]
  rw [← Iso.trans_assoc, squarePullbackFrame_precompose]

end ToricPower
