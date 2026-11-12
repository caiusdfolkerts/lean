module

public import ToricPower.SheafChartPullbackTransitions

/-! Equality transports for actual pullback chart frames. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 500000

open AlgebraicGeometry CategoryTheory MonoidalCategory
open AlgebraicGeometry.Scheme.Modules
namespace ToricPower
universe u
variable {A B X Y : Scheme.{u}}

private theorem identityIso_app {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (x : C) : (Iso.refl F).app x = Iso.refl (F.obj x) := rfl

/-- Restriction along an equality of open immersions uses the identity
comparison when the equality is reflexive. -/
theorem restrictFunctorCongr_refl (a : A ⟶ X) [IsOpenImmersion a] :
    restrictFunctorCongr (rfl : a = a) = Iso.refl (restrictFunctor a) := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply Scheme.Modules.hom_ext
  intro U
  change Hom.app ((restrictFunctorCongr (rfl : a = a)).hom.app M) U =
    Hom.app (𝟙 (M.restrict a)) U
  rw [Hom.id_app, restrictFunctorCongr_hom_app_app]
  simp only [eqToHom_refl, op_id, CategoryTheory.Functor.map_id]
  have comparison := congrArg (fun mapping => Hom.app mapping U)
    ((restrictFunctor a).map_id M)
  simpa only [restrictFunctor_map_app, Hom.id_app] using comparison

/-- Changing only the equality presentation of the source chart has the
canonical restriction comparison and changes no frame. -/
theorem chartPullbackFrame_congr_source (f : X ⟶ Y) {a a' : A ⟶ X}
    [IsOpenImmersion a] [IsOpenImmersion a'] (equal : a = a')
    (b : B ⟶ Y) [IsOpenImmersion b] (g : A ⟶ B)
    (square : a ≫ f = g ≫ b) (square' : a' ≫ f = g ≫ b)
    (M : Y.Modules) (frame : 𝟙_ B.Modules ≅ M.restrict b) :
    chartPullbackFrame f a b g square M frame ≪≫
      (restrictFunctorCongr equal).app ((pullback f).obj M) =
    chartPullbackFrame f a' b g square' M frame := by
  subst a'
  rw [restrictFunctorCongr_refl, identityIso_app, Iso.trans_refl]

/-- Changing only the target-chart presentation transports its ordinary
restriction frame by the canonical equality comparison. -/
theorem chartPullbackFrame_congr_target (f : X ⟶ Y) (a : A ⟶ X)
    [IsOpenImmersion a] {b b' : B ⟶ Y} [IsOpenImmersion b] [IsOpenImmersion b']
    (equal : b = b') (g : A ⟶ B)
    (square : a ≫ f = g ≫ b) (square' : a ≫ f = g ≫ b')
    (M : Y.Modules) (frame : 𝟙_ B.Modules ≅ M.restrict b) :
    chartPullbackFrame f a b' g square' M
      (frame ≪≫ (restrictFunctorCongr equal).app M) =
    chartPullbackFrame f a b g square M frame := by
  subst b'
  rw [restrictFunctorCongr_refl, identityIso_app, Iso.trans_refl]

end ToricPower
