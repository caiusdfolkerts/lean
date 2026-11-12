module

public import ToricPower.QuasicoherentPullbackLocal
public import ToricPower.ToricAffinePowerDuality

/-!
# Exactness of pullback by every positive power of a smooth toric variety

The genuine chart trace adjunction makes each affine pullback exact.
Canonical pullback-square isomorphisms and detection of zero homology on
the fan's actual cover then give global exactness, without completeness.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i) (regular : fan.IsRegular)
  (ell : ℕ) (positive : 0 < ell)

include regular positive

/-- All local exactness hypotheses are discharged by the chart trace. -/
theorem toricPowerPullback_preservesFiniteLimits :
    PreservesFiniteLimits (quasicoherentPullback (toricPowerMap fan ell)) := by
  let F := quasicoherentPullback (toricPowerMap fan ell)
  let G := fun cone : fan.cones => quasicoherentRestriction (fan.affineToricChartι cone)
  have comparison (cone : fan.cones) :
      G cone ⋙ quasicoherentPullback (Spec.map (chartPowerRingHom fan cone ell)) ≅ F ⋙ G cone := by
    apply quasicoherentPullbackRestrictionSquareIso
    have equality : affinePowerMap fan ell cone = Spec.map (chartPowerRingHom fan cone ell) := by
      rw [affinePowerMap, affineToricSchemeMap_def]
      rfl
    rw [← equality]
    exact toricPowerMap_affine_chart fan ell positive cone
  letI (cone : fan.cones) :
      PreservesFiniteLimits (quasicoherentPullback (Spec.map (chartPowerRingHom fan cone ell))) :=
    affineQuasicoherentPullback_preservesFiniteLimits (chartPowerRingHom fan cone ell)
      (toricChartPowerRestrictExtendAdjunction fan regular ell positive cone)
  letI (cone : fan.cones) : PreservesFiniteLimits (F ⋙ G cone) :=
    preservesFiniteLimits_of_natIso (comparison cone)
  letI (cone : fan.cones) : PreservesFiniteColimits (F ⋙ G cone) :=
    preservesFiniteColimits_of_natIso (comparison cone)
  exact (exactFunctor_of_jointly_detect_zero G
    (quasicoherent_isZero_of_openCover fan.affineToricOpenCover) F).1

local instance toricPowerPullback_derivedQCoh : HasDerivedCategory.{1} (QCoh fan.algebraicRealization) :=
  HasDerivedCategory.standard _

/-- The original pullback--pushforward adjunction on the full unbounded
derived category, obtained from the proved exact ordinary functors. -/
def toricPowerDerivedAdjunction :
    letI := toricPowerMap_finite fan regular ell positive
    letI := toricPowerPullback_preservesFiniteLimits fan regular ell positive
    (quasicoherentPullback (toricPowerMap fan ell)).mapDerivedCategory ⊣
      (quasicoherentAffinePushforward (toricPowerMap fan ell)).mapDerivedCategory := by
  letI := toricPowerMap_finite fan regular ell positive
  letI := toricPowerPullback_preservesFiniteLimits fan regular ell positive
  exact exactDerivedAdjunction
    (quasicoherentPullbackPushforwardAdjunction (toricPowerMap fan ell))

end ToricPower

end
