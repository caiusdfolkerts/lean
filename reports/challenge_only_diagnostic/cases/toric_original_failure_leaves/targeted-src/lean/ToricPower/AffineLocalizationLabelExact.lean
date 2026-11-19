module

public import ToricPower.AffineOpenIntrinsicLabelHomExact
public import ToricPower.AffineConeCoresolution
public import ToricPower.FiniteExactComposition

/-! # Exact label Hom after actual affine-open localization -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace ToricPower

universe u

variable (R : Type u) [CommRing R] {U X : Scheme.{u}}
  [X.Over (Spec (.of R))] (j : U ⟶ X) [IsOpenImmersion j] [IsAffineHom j]
  [IsAffine U] [IsIntegral U] {C : Type u} [Category.{u} C]
  (P : Cᵒᵖ ⥤ QCoh X)
  (invertible : ∀ c, TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X (P.obj (op c)).obj)

include invertible

/-- Restriction is exact and the intrinsic label Hom is exact on the
actual affine direct image, so their literal composite is exact. -/
theorem quasicoherentOpenLocalizationLabelHom_exact :
    PreservesFiniteLimits (quasicoherentOpenLocalization j ⋙ Cellular.homDiagram R P) ∧
    PreservesFiniteColimits (quasicoherentOpenLocalization j ⋙ Cellular.homDiagram R P) :=
  finiteExact_rightComposite (quasicoherentRestriction j) (quasicoherentAffinePushforward j)
    (Cellular.homDiagram R P) (quasicoherentOpenIntrinsicLabelHom_exact R j P invertible)

end ToricPower

end
