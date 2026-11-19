module

public import ToricPower.ToricAffinePowerDuality
public import ToricPower.ProjectionBaseChange
public import ToricPower.SheafQuasiIsoLocal

/-!
# The global projection formula for a positive toric power

The genuine unit/tensor comparison is invertible on the whole smooth
toric variety.  Its restriction to every cone chart is identified with
the already proved unrestricted affine projection comparison.  No
completeness, properness, or finite-generation assumption is needed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory TauCeti.Toric

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i) (regular : fan.IsRegular)
  (ell : ℕ) (positive : 0 < ell)

include regular positive

/-- The canonical global projection morphism for arbitrary quasicoherent
coefficients is an isomorphism, for every positive power. -/
theorem toricPowerProjectionComparison_isIso
    (P Q : QCoh fan.algebraicRealization) :
    IsIso ((monoidalProjectionComparison
      (Scheme.Modules.pullbackPushforwardAdjunction (toricPowerMap fan ell)) P.obj).app Q.obj) := by
  let comparison := (monoidalProjectionComparison
    (Scheme.Modules.pullbackPushforwardAdjunction (toricPowerMap fan ell)) P.obj).app Q.obj
  apply (Scheme.Modules.isIso_iff_pullback_openCover fan.affineToricOpenCover comparison).mpr
  intro cone
  apply (NatIso.isIso_map_iff
    (Scheme.Modules.restrictFunctorIsoPullback (fan.affineToricChartι cone)) comparison).mp
  apply projectionComparison_restrict_isIso (toricPowerMap fan ell)
    (affinePowerMap fan ell cone) (fan.affineToricChartι cone) (fan.affineToricChartι cone)
    (toricPowerMap_affine_chart fan ell positive cone)
    (by
      change (toricPowerMap fan ell) ⁻¹' Set.range (fan.affineToricChartι cone) ⊆
        Set.range (fan.affineToricChartι cone)
      exact (toricPowerMap_preimage_chart fan ell positive cone).subset)
    Q.obj P.obj
  have affine := toricAffinePowerProjectionComparison_isIso fan regular ell positive cone
    ((quasicoherentRestriction (fan.affineToricChartι cone)).obj P)
    ((quasicoherentRestriction (fan.affineToricChartι cone)).obj Q)
  have equality : affinePowerMap fan ell cone = Spec.map (chartPowerRingHom fan cone ell) := by
    rw [affinePowerMap, affineToricSchemeMap_def]
    rfl
  rw [equality]
  exact affine

/-- The complete natural projection isomorphism on actual quasicoherent
coefficients, retaining the original unit/tensor map as its hom. -/
def toricPowerProjectionIso (P : QCoh fan.algebraicRealization) :
    letI := toricPowerMap_finite fan regular ell positive
    quasicoherentInclusion fan.algebraicRealization ⋙
        tensorRight ((Scheme.Modules.pushforward (toricPowerMap fan ell)).obj P.obj) ≅
      quasicoherentPullback (toricPowerMap fan ell) ⋙ tensorRight P ⋙
        quasicoherentAffinePushforward (toricPowerMap fan ell) ⋙
          quasicoherentInclusion fan.algebraicRealization := by
  letI := toricPowerMap_finite fan regular ell positive
  let α := quasicoherentProjectionComparison (toricPowerMap fan ell) P
  letI : IsIso α := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact toricPowerProjectionComparison_isIso fan regular ell positive P
  exact asIso α

end ToricPower

end
