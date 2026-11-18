module

public import ToricPower.SheafChartPullbackCongruence

/-! Simultaneous refinement of the source and target open charts in a
genuine module-sheaf pullback. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 500000

open AlgebraicGeometry CategoryTheory MonoidalCategory
open AlgebraicGeometry.Scheme.Modules
namespace ToricPower
universe u
variable {A A' B B' X Y : Scheme.{u}}

private theorem identityIso_app {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (x : C) : (Iso.refl F).app x = Iso.refl (F.obj x) := rfl

theorem chartPullbackFrame_congr_map (f : X ⟶ Y) (a : A ⟶ X) [IsOpenImmersion a]
    (b : B ⟶ Y) [IsOpenImmersion b] {g g' : A ⟶ B} (equal : g = g')
    (square : a ≫ f = g ≫ b) (square' : a ≫ f = g' ≫ b)
    (M : Y.Modules) (frame : 𝟙_ B.Modules ≅ M.restrict b) :
    chartPullbackFrame f a b g square M frame =
      chartPullbackFrame f a b g' square' M frame := by
  subst g'
  rfl

/-- Both chart refinements commute with the actual pulled-back frame,
provided the original target frames are related by their actual ordinary
restriction. Every comparison is retained explicitly. -/
theorem chartPullbackFrame_refine (f : X ⟶ Y)
    (a : A ⟶ X) (a' : A' ⟶ X) [IsOpenImmersion a] [IsOpenImmersion a']
    (b : B ⟶ Y) (b' : B' ⟶ Y) [IsOpenImmersion b] [IsOpenImmersion b']
    (c : A' ⟶ A) (d : B' ⟶ B) [IsOpenImmersion c] [IsOpenImmersion d]
    (g : A ⟶ B) (g' : A' ⟶ B')
    (source : c ≫ a = a') (target : d ≫ b = b') (maps : c ≫ g = g' ≫ d)
    (square : a ≫ f = g ≫ b) (square' : a' ≫ f = g' ≫ b')
    (M : Y.Modules) (frame : 𝟙_ B.Modules ≅ M.restrict b)
    (frame' : 𝟙_ B'.Modules ≅ M.restrict b')
    (targetFrame : restrictModuleFrame d frame ≪≫
      ((restrictFunctorComp d b).app M).symm ≪≫
      (restrictFunctorCongr target).app M = frame') :
    restrictModuleFrame c (chartPullbackFrame f a b g square M frame) ≪≫
      ((restrictFunctorComp c a).app ((pullback f).obj M)).symm ≪≫
      (restrictFunctorCongr source).app ((pullback f).obj M) =
    chartPullbackFrame f a' b' g' square' M frame' := by
  subst a'
  subst b'
  rw [restrictFunctorCongr_refl, identityIso_app, Iso.trans_refl] at targetFrame
  rw [restrictFunctorCongr_refl, identityIso_app, Iso.trans_refl, ← targetFrame]
  have pasted : (c ≫ a) ≫ f = (c ≫ g) ≫ b := by
    rw [Category.assoc, square, ← Category.assoc]
  have changed : (c ≫ a) ≫ f = (g' ≫ d) ≫ b :=
    pasted.trans (congrArg (fun mapping => mapping ≫ b) maps)
  rw [chartPullbackFrame_precompose f a b g square c M frame pasted]
  exact (chartPullbackFrame_congr_map f (c ≫ a) b maps pasted changed M frame).trans
    (chartPullbackFrame_target_refine f (c ≫ a) b d g' changed square' M frame).symm

end ToricPower
