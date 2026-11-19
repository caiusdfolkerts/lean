module

public import ToricPower.AffineQuasicoherentDuality
public import ToricPower.OpenBaseChangeNaturality
public import ToricPower.SheafQuasiIsoLocal
public import ToricPower.JointExactDetection

/-! # Actual pullback squares and zero detection for quasicoherent sheaves -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace ToricPower

universe u v

/-- The actual scheme pullback square restricted to quasicoherent objects. -/
def quasicoherentPullbackRestrictionSquareIso {X X' Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : X' ⟶ Y') (j : X' ⟶ X) (k : Y' ⟶ Y)
    [IsOpenImmersion j] [IsOpenImmersion k] (hsq : j ≫ f = g ≫ k) :
    quasicoherentRestriction k ⋙ quasicoherentPullback g ≅
      quasicoherentPullback f ⋙ quasicoherentRestriction j :=
  Functor.fullyFaithfulCancelRight (quasicoherentInclusion X')
    (Functor.isoWhiskerLeft (quasicoherentInclusion Y)
      (pullbackRestrictionSquareIso f g j k hsq))

/-- Restriction to an actual open cover detects zero quasicoherent sheaves. -/
theorem quasicoherent_isZero_of_openCover {X : Scheme.{u}}
    (cover : Scheme.OpenCover.{v} X) (M : QCoh X)
    (localZero : ∀ a, IsZero ((quasicoherentRestriction (cover.f a)).obj M)) :
    IsZero M := by
  apply IsZero.of_full_of_faithful_of_isZero (quasicoherentInclusion X) M
  apply (Scheme.Modules.isZero_iff_pullback_openCover cover M.obj).mpr
  intro a
  apply ((Scheme.Modules.restrictFunctorIsoPullback (cover.f a)).app M.obj).isZero_iff.mp
  exact (quasicoherentInclusion (cover.X a)).map_isZero (localZero a)

end ToricPower

end
