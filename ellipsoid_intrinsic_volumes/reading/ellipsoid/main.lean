module

public import Ellipsoid.PrincipalReconstruction
public import Ellipsoid.UniformHolderTheorem
public import Ellipsoid.SharpHolderTheorem
public import Ellipsoid.FixedVolumeSharpness
public import Ellipsoid.CoefficientProperness
public import Ellipsoid.MeasuredCoefficientBox
public import Ellipsoid.AffineParameterization

@[expose] public section

/-!
# Complete Ellipsoid theorem entry point

This source entry point includes every principal theorem, the exact geometric
Steiner/GSZ correspondence in their dependency closure, the measured coefficient
bounds, and both directions of the customary affine-ball parameterization.
It is separate from generated compiled stages and does not certify compilation.
-/

namespace EllipsoidVerification

theorem principal_reconstruction_and_stability :
    IntrinsicReconstruction ∧ UniformHolderRecovery ∧ SharpHolderRecovery ∧
      SharpHolderRecoveryAtFixedVolume :=
  ⟨intrinsic_reconstruction, uniform_holder_recovery, sharp_holder_recovery,
    sharp_holder_recovery_at_fixed_volume⟩

end EllipsoidVerification
