module

public import ToricPower.SheafPullbackSquares

/-!
# Local frame coherence for actual pullback squares

Pasting a source chart restriction onto a commuting scheme square gives
the same canonical pullback comparison. The statements retain all
composition and equality isomorphisms of the ordinary pullback functor.
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

/-- Normalized pullback respects postcomposition of a local frame. -/
theorem pullbackModuleFrame_trans (f : A ⟶ B) {M N : B.Modules}
    (frame : 𝟙_ B.Modules ≅ M) (comparison : M ≅ N) :
    pullbackModuleFrame f (frame ≪≫ comparison) =
      pullbackModuleFrame f frame ≪≫ (pullback f).mapIso comparison := by
  apply Iso.ext
  simp only [pullbackModuleFrame, Iso.trans_hom, Iso.symm_hom,
    CategoryTheory.Functor.mapIso_hom, CategoryTheory.Functor.map_comp, Category.assoc]

/-- A frame pulled through an actual commuting square, before converting
open pullback back to ordinary restriction. -/
def squarePullbackFrame (f : X ⟶ Y) (a : A ⟶ X) (b : B ⟶ Y) (g : A ⟶ B)
    (square : a ≫ f = g ≫ b) {M : Y.Modules}
    (frame : 𝟙_ B.Modules ≅ (pullback b).obj M) :
    𝟙_ A.Modules ≅ (pullback a).obj ((pullback f).obj M) :=
  pullbackModuleFrame g frame ≪≫ (chartPullbackSquare f a b g square).app M

/-- Pulling the local frame further along the source gives exactly the
frame of the pasted square. -/
theorem squarePullbackFrame_precompose (f : X ⟶ Y) (a : A ⟶ X)
    (b : B ⟶ Y) (g : A ⟶ B) (square : a ≫ f = g ≫ b)
    (c : C ⟶ A) {M : Y.Modules}
    (frame : 𝟙_ B.Modules ≅ (pullback b).obj M)
    (pasted : (c ≫ a) ≫ f = (c ≫ g) ≫ b) :
    pullbackModuleFrame c (squarePullbackFrame f a b g square frame) ≪≫
      (pullbackComp c a).app ((pullback f).obj M) =
        squarePullbackFrame f (c ≫ a) b (c ≫ g) pasted frame := by
  simp only [squarePullbackFrame, pullbackModuleFrame_trans, Iso.trans_assoc]
  apply Iso.ext
  simp only [Iso.trans_hom, CategoryTheory.Functor.mapIso_hom, Iso.app_hom]
  change (pullbackModuleFrame c (pullbackModuleFrame g frame)).hom ≫
    (pullback c).map ((chartPullbackSquare f a b g square).hom.app M) ≫
      (pullbackComp c a).hom.app ((pullback f).obj M) =
    (pullbackModuleFrame (c ≫ g) frame).hom ≫
      (chartPullbackSquare f (c ≫ a) b (c ≫ g) pasted).hom.app M
  rw [chartPullbackSquare_precompose f a b g square c M pasted]
  have composition := congrArg (fun e => e.hom) (pullbackModuleFrame_comp c g frame)
  simpa only [Iso.trans_hom, Iso.app_hom, Category.assoc] using
    congrArg (fun mapping => mapping ≫
      (chartPullbackSquare f (c ≫ a) b (c ≫ g) pasted).hom.app M) composition

end ToricPower
