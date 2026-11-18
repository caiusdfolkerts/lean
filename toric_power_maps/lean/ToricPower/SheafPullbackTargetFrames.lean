module

public import ToricPower.SheafRestrictedPullbackFrames

/-! Refining the target chart in an actual pullback-frame construction. -/

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

/-- Pasting a target chart restriction respects the prescribed pullback
comparison, including its equality transport. -/
theorem chartPullbackSquare_target_refine (f : X ⟶ Y) (a : A ⟶ X)
    (b : B ⟶ Y) (d : C ⟶ B) (g : A ⟶ C)
    (square : a ≫ f = (g ≫ d) ≫ b) (refined : a ≫ f = g ≫ (d ≫ b)) (M : Y.Modules) :
    (pullback g).map ((pullbackComp d b).hom.app M) ≫
      (chartPullbackSquare f a (d ≫ b) g refined).hom.app M =
    (pullbackComp g d).hom.app ((pullback b).obj M) ≫
      (chartPullbackSquare f a b (g ≫ d) square).hom.app M := by
  have associativity := pullback_map_pullbackComp_hom_app_comp_pullbackComp_hom_app g d b M
  have transport :
      eqToHom (congrArg (fun h => (pullback h).obj M) (Category.assoc g d b)) ≫
        (pullbackCongr refined.symm).hom.app M = (pullbackCongr square.symm).hom.app M := by
    simp only [pullbackCongr_hom_app_eqToHom, eqToHom_trans]
  have suffix := congrArg (fun mapping => mapping ≫ (pullbackComp a f).inv.app M) transport
  simp only [Category.assoc (obj := A.Modules)] at suffix
  have comparison := congrArg (fun mapping => mapping ≫
    (pullbackCongr refined.symm).hom.app M ≫ (pullbackComp a f).inv.app M) associativity
  simp only [Category.assoc (obj := A.Modules)] at comparison
  rw [suffix] at comparison
  simpa only [chartPullbackSquare_hom_app, Category.assoc (obj := A.Modules)] using comparison

/-- The target-pasting identity as an equality of actual module isomorphisms. -/
theorem chartPullbackSquare_target_refine_iso (f : X ⟶ Y) (a : A ⟶ X)
    (b : B ⟶ Y) (d : C ⟶ B) (g : A ⟶ C)
    (square : a ≫ f = (g ≫ d) ≫ b) (refined : a ≫ f = g ≫ (d ≫ b)) (M : Y.Modules) :
    (pullback g).mapIso ((pullbackComp d b).app M) ≪≫
      (chartPullbackSquare f a (d ≫ b) g refined).app M =
    (pullbackComp g d).app ((pullback b).obj M) ≪≫
      (chartPullbackSquare f a b (g ≫ d) square).app M := by
  apply Iso.ext
  exact chartPullbackSquare_target_refine f a b d g square refined M

/-- Normalized genuine pullback of a frame is unchanged by refining its
target chart and using the canonical restricted frame there. -/
theorem squarePullbackFrame_target_refine (f : X ⟶ Y) (a : A ⟶ X)
    (b : B ⟶ Y) (d : C ⟶ B) (g : A ⟶ C)
    (square : a ≫ f = (g ≫ d) ≫ b) (refined : a ≫ f = g ≫ (d ≫ b))
    {M : Y.Modules} (frame : 𝟙_ B.Modules ≅ (pullback b).obj M) :
    squarePullbackFrame f a (d ≫ b) g refined
      (pullbackModuleFrame d frame ≪≫ (pullbackComp d b).app M) =
    squarePullbackFrame f a b (g ≫ d) square frame := by
  unfold squarePullbackFrame
  rw [pullbackModuleFrame_trans, Iso.trans_assoc, chartPullbackSquare_target_refine_iso]
  rw [← Iso.trans_assoc, pullbackModuleFrame_comp]

/-- Converting an ordinary restricted chart frame to pullback is the same
as pulling back its converted frame and composing the two pullbacks. -/
theorem restrictedFrame_toPullback (d : C ⟶ B) (b : B ⟶ Y)
    [IsOpenImmersion d] [IsOpenImmersion b] (M : Y.Modules)
    (frame : 𝟙_ B.Modules ≅ M.restrict b) :
    restrictModuleFrame d frame ≪≫ ((restrictFunctorComp d b).app M).symm ≪≫
      (restrictFunctorIsoPullback (d ≫ b)).app M =
    pullbackModuleFrame d (frame ≪≫ (restrictFunctorIsoPullback b).app M) ≪≫
      (pullbackComp d b).app M := by
  rw [← restrictionComparison_comp d b M]
  simp only [Iso.trans_assoc, Iso.symm_self_id_assoc]
  rw [← Iso.trans_assoc, restrictModuleFrame_pullback]
  simp only [pullbackModuleFrame_trans, Iso.trans_assoc]

/-- Refining an actual target open chart does not change the actual
ordinary-restriction frame of the pulled-back module sheaf. -/
theorem chartPullbackFrame_target_refine (f : X ⟶ Y) (a : A ⟶ X)
    [IsOpenImmersion a] (b : B ⟶ Y) [IsOpenImmersion b]
    (d : C ⟶ B) [IsOpenImmersion d] (g : A ⟶ C)
    (square : a ≫ f = (g ≫ d) ≫ b) (refined : a ≫ f = g ≫ (d ≫ b))
    (M : Y.Modules) (frame : 𝟙_ B.Modules ≅ M.restrict b) :
    chartPullbackFrame f a (d ≫ b) g refined M
      (restrictModuleFrame d frame ≪≫ ((restrictFunctorComp d b).app M).symm) =
    chartPullbackFrame f a b (g ≫ d) square M frame := by
  simp only [chartPullbackFrame, Iso.trans_assoc]
  rw [restrictedFrame_toPullback, squarePullbackFrame_target_refine]

end ToricPower
