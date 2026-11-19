module

public import ToricPower.AffineProjectionFormula
public import ToricPower.PowerSheafCore

/-!
# Actual finite duality on every toric affine chart

The regular dual-semigroup coordinates include every Laurent direction.
Their complete residue trace proves the second scalar-change adjunction
for the literal chart power-ring homomorphism. Transport through the
actual affine tilde equivalence gives sheaf and unbounded derived
adjunctions, and the canonical affine projection formula for arbitrary
quasicoherent coefficients.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i) (regular : fan.IsRegular)
  (ell : ℕ) (positive : 0 < ell) (cone : fan.cones)

include regular positive

/-- The actual ring homomorphism of the cone chart has the proved trace adjunction. -/
def toricChartPowerRestrictExtendAdjunction :
    ModuleCat.restrictScalars.{0} (chartPowerRingHom fan cone ell).hom ⊣
      ModuleCat.extendScalars (chartPowerRingHom fan cone ell).hom := by
  have hcone := (Fan.isRegular_iff.mp regular) cone.val cone.property
  letI := ToricRay.finite_of_fg hcone.fg
  letI := Fintype.ofFinite (ToricRay cone.val)
  have equality : (chartPowerRingHom fan cone ell).hom =
      MonoidAlgebra.mapDomainRingHom ℂ
        (exponentPower ell (dualSemigroup fan.lattice cone.val)) :=
    power_affineCoordinateRingMap_eq fan ell cone
  rw [equality]
  exact transportedPowerRestrictExtendAdjunction ell ℂ
    (regularDualCoordinateEquiv fan.lattice hcone) positive

/-- Genuine quasicoherent direct image is left adjoint to genuine pullback
on every regular chart, using the local relative-boundary frame. -/
def toricAffinePowerPushforwardPullbackAdjunction :
    quasicoherentAffinePushforward (Spec.map (chartPowerRingHom fan cone ell)) ⊣
      quasicoherentPullback (Spec.map (chartPowerRingHom fan cone ell)) :=
  affineQuasicoherentPushforwardPullbackAdjunction (chartPowerRingHom fan cone ell)
    (toricChartPowerRestrictExtendAdjunction fan regular ell positive cone)

/-- The actual affine projection formula has no finite-generation condition
on the input quasicoherent sheaves. -/
theorem toricAffinePowerProjectionComparison_isIso
    (P Q : QCoh (fan.affineToricChart cone)) :
    IsIso ((quasicoherentProjectionComparison
      (Spec.map (chartPowerRingHom fan cone ell)) P).app Q) :=
  affineQuasicoherentProjectionComparison_isIso (chartPowerRingHom fan cone ell)
    (toricChartPowerRestrictExtendAdjunction fan regular ell positive cone) P Q

end ToricPower

end
