module

public import ellipsoid

@[expose] public section
noncomputable section
open EllipsoidVerification MeasureTheory Set Polynomial Filter Topology Matrix
open scoped BigOperators Pointwise ContDiff Manifold
namespace PalomarEllipsoid

/-- The coefficient transform on Mathlib's standard quadrant, using its literal
Euclidean coordinate entries. No auxiliary coordinate transport is part of
this definition. -/
def coefficientQuadrantMap (m : ℕ) (e0 en : ℝ) :
    EuclideanQuadrant m → (Fin m → ℝ) :=
  fun x => coefficientMap m e0 en (fun i => x.val i)

theorem intrinsic_reconstruction : IntrinsicReconstruction := EllipsoidVerification.intrinsic_reconstruction

theorem uniform_holder_recovery : UniformHolderRecovery := EllipsoidVerification.uniform_holder_recovery

theorem sharp_holder_recovery : SharpHolderRecovery := EllipsoidVerification.sharp_holder_recovery

theorem sharp_holder_recovery_at_fixed_volume : SharpHolderRecoveryAtFixedVolume := EllipsoidVerification.sharp_holder_recovery_at_fixed_volume

theorem coefficient_transform_theorem {m : ℕ} {e0 en : ℝ}
    (h0 : 0 < e0) (hn : 0 < en) : CoefficientTransformConclusion m e0 en := EllipsoidVerification.coefficient_transform_theorem h0 hn
theorem coefficient_transform_manifold_with_corners {m : ℕ} {e0 en : ℝ}
    (h0 : 0 < e0) (hn : 0 < en) :
    Manifold.IsSmoothEmbedding (𝓡c m) 𝓘(ℝ, Fin m → ℝ) ∞
      (coefficientQuadrantMap m e0 en) ∧
    IsProperMap (coefficientQuadrantMap m e0 en) ∧
    IsClosed (Set.range (coefficientQuadrantMap m e0 en))  := by
  have hmap : quadrantCoefficientMap m e0 en = coefficientQuadrantMap m e0 en := by
    funext x
    exact quadrantCoefficientMap_apply m e0 en x
  simpa only [hmap] using
    EllipsoidVerification.coefficient_transform_manifold_with_corners h0 hn
theorem measured_coefficient_box {n : ℕ} (hn : 0 < n) (E : FullEllipsoid n)
    (k : Fin (n + 1)) (hk : 0 < k.val) (hkn : k.val < n) :
    (n.choose k.val : ℝ) * (E.volume n / unitBallVolume n) ^ (2 * (k.val : ℝ) / n) ≤
      axisCoefficients E.semiaxis k ∧
    axisCoefficients E.semiaxis k < (E.volume k.val / unitBallVolume k.val) ^ 2 ∧
    axisCoefficients E.semiaxis (Fin.last n) = (E.volume n / unitBallVolume n) ^ 2 := EllipsoidVerification.measured_coefficient_box hn E k hk hkn
end PalomarEllipsoid
