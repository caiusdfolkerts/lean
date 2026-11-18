module

public import ellipsoid

@[expose] public section
noncomputable section
open EllipsoidVerification MeasureTheory Set Polynomial Filter Topology Matrix
open scoped BigOperators Pointwise ContDiff Manifold
namespace PalomarEllipsoid

theorem intrinsic_reconstruction : IntrinsicReconstruction := EllipsoidVerification.intrinsic_reconstruction

theorem uniform_holder_recovery : UniformHolderRecovery := EllipsoidVerification.uniform_holder_recovery

theorem sharp_holder_recovery : SharpHolderRecovery := EllipsoidVerification.sharp_holder_recovery

theorem sharp_holder_recovery_at_fixed_volume : SharpHolderRecoveryAtFixedVolume := EllipsoidVerification.sharp_holder_recovery_at_fixed_volume

theorem coefficient_transform_theorem {m : ℕ} {e0 en : ℝ}
    (h0 : 0 < e0) (hn : 0 < en) : CoefficientTransformConclusion m e0 en := EllipsoidVerification.coefficient_transform_theorem

theorem coefficient_transform_manifold_with_corners {m : ℕ} {e0 en : ℝ}
    (h0 : 0 < e0) (hn : 0 < en) :
    Manifold.IsSmoothEmbedding (𝓡c m) 𝓘(ℝ, Fin m → ℝ) ∞
      (quadrantCoefficientMap m e0 en) ∧
    IsProperMap (quadrantCoefficientMap m e0 en) ∧
    IsClosed (Set.range (quadrantCoefficientMap m e0 en)) := EllipsoidVerification.coefficient_transform_manifold_with_corners

theorem measured_coefficient_box {n : ℕ} (hn : 0 < n) (E : FullEllipsoid n)
    (k : Fin (n + 1)) (hk : 0 < k.val) (hkn : k.val < n) :
    (n.choose k.val : ℝ) * (E.volume n / unitBallVolume n) ^ (2 * (k.val : ℝ) / n) ≤
      axisCoefficients E.semiaxis k ∧
    axisCoefficients E.semiaxis k < (E.volume k.val / unitBallVolume k.val) ^ 2 ∧
    axisCoefficients E.semiaxis (Fin.last n) = (E.volume n / unitBallVolume n) ^ 2 := EllipsoidVerification.measured_coefficient_box

end PalomarEllipsoid
