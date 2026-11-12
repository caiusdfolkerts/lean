module

public import ToricPower.SheafPullbackTargetFrames

/-! Actual transition functions of frames transported through commuting
scheme charts. The scalar is pulled back by the literal map on global
sections of the chart, with no dominance assumption. -/

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

theorem squarePullbackFrame_scalar (f : X ⟶ Y) (a : A ⟶ X)
    (b : B ⟶ Y) (g : A ⟶ B) (square : a ≫ f = g ≫ b)
    {M : Y.Modules} (first second : 𝟙_ B.Modules ≅ (pullback b).obj M)
    (scalar : Γ(B, ⊤))
    (transition : first.hom = globalSectionsSmul (𝟙_ B.Modules) scalar ≫ second.hom) :
    (squarePullbackFrame f a b g square first).hom =
      globalSectionsSmul (𝟙_ A.Modules) (g.appTop scalar) ≫
        (squarePullbackFrame f a b g square second).hom := by
  exact (congrArg (fun mapping => mapping ≫
      (chartPullbackSquare f a b g square).hom.app M)
    (pullbackModuleFrame_scalar g first second scalar transition)).trans
      (Category.assoc _ _ _)

/-- Scalar transitions of ordinary target-chart frames pull back to
scalar transitions of the genuine pulled-back sheaf. -/
theorem chartPullbackFrame_scalar (f : X ⟶ Y) (a : A ⟶ X) [IsOpenImmersion a]
    (b : B ⟶ Y) [IsOpenImmersion b] (g : A ⟶ B) (square : a ≫ f = g ≫ b)
    (M : Y.Modules) (first second : 𝟙_ B.Modules ≅ M.restrict b)
    (scalar : Γ(B, ⊤))
    (transition : first.hom = globalSectionsSmul (𝟙_ B.Modules) scalar ≫ second.hom) :
    (chartPullbackFrame f a b g square M first).hom =
      globalSectionsSmul (𝟙_ A.Modules) (g.appTop scalar) ≫
        (chartPullbackFrame f a b g square M second).hom := by
  have converted : (first ≪≫ (restrictFunctorIsoPullback b).app M).hom =
      globalSectionsSmul (𝟙_ B.Modules) scalar ≫
        (second ≪≫ (restrictFunctorIsoPullback b).app M).hom := by
    simp only [Iso.trans_hom, transition, Category.assoc]
  exact (congrArg (fun mapping => mapping ≫
      (restrictFunctorIsoPullback a).inv.app ((pullback f).obj M))
    (squarePullbackFrame_scalar f a b g square _ _ scalar converted)).trans
      (Category.assoc _ _ _)

end ToricPower
