module

public import verification.internal.ellipsoid_remaining_statements
public import ellipsoid.coefficient_corners
public import ellipsoid.sharpness_neighborhood

/- Separate twenty-root readable theorem/axiom reports for the ellipsoid principal
   family and its independent literal statements. This is an inspection
   source only until the ordinary check and separate actual-body/replay
   gates pass. -/

#print EllipsoidVerification.intrinsic_reconstruction
#print axioms EllipsoidVerification.intrinsic_reconstruction

#print EllipsoidVerification.exists_fullEllipsoid_of_affineBall
#print axioms EllipsoidVerification.exists_fullEllipsoid_of_affineBall

#print EllipsoidVerification.FullEllipsoid.exists_affineBallParameterization
#print axioms EllipsoidVerification.FullEllipsoid.exists_affineBallParameterization

#print EllipsoidVerification.symmetricPart_balancedJacobian_posDef
#print axioms EllipsoidVerification.symmetricPart_balancedJacobian_posDef

#print EllipsoidVerification.uniform_holder_recovery
#print axioms EllipsoidVerification.uniform_holder_recovery

#print EllipsoidVerification.sharp_holder_recovery
#print axioms EllipsoidVerification.sharp_holder_recovery

#print EllipsoidVerification.sharp_holder_recovery_at_fixed_volume
#print axioms EllipsoidVerification.sharp_holder_recovery_at_fixed_volume

#print EllipsoidVerification.coefficient_transform_theorem
#print axioms EllipsoidVerification.coefficient_transform_theorem

#print EllipsoidVerification.measured_coefficient_box
#print axioms EllipsoidVerification.measured_coefficient_box

#print EllipsoidVerification.coefficientTransform_gt_sqrt
#print axioms EllipsoidVerification.coefficientTransform_gt_sqrt

#print EllipsoidAudit.uniformOneOverN_statement
#print axioms EllipsoidAudit.uniformOneOverN_statement

#print EllipsoidAudit.noLargerExponent_statement
#print axioms EllipsoidAudit.noLargerExponent_statement

#print EllipsoidAudit.noLargerExponentEqualVolume_statement
#print axioms EllipsoidAudit.noLargerExponentEqualVolume_statement

#print EllipsoidAudit.coefficientTransformFull_statement
#print axioms EllipsoidAudit.coefficientTransformFull_statement

#print EllipsoidAudit.coefficient_strict_bound_statement
#print axioms EllipsoidAudit.coefficient_strict_bound_statement

#print EllipsoidAudit.measuredCoefficientBox_statement
#print axioms EllipsoidAudit.measuredCoefficientBox_statement

#print EllipsoidVerification.orderedMomentKernel_posDef
#print axioms EllipsoidVerification.orderedMomentKernel_posDef

#print EllipsoidVerification.coefficient_transform_manifold_with_corners
#print axioms EllipsoidVerification.coefficient_transform_manifold_with_corners

#print EllipsoidVerification.sharp_holder_recovery_near_sphere
#print axioms EllipsoidVerification.sharp_holder_recovery_near_sphere

#print EllipsoidVerification.sharp_holder_recovery_at_fixed_volume_near_sphere
#print axioms EllipsoidVerification.sharp_holder_recovery_at_fixed_volume_near_sphere

/- Literal bridge assignments, independent of named statement abbreviations. -/
open scoped ContDiff Manifold

example {m : ℕ} {e0 en : ℝ} (h0 : 0 < e0) (hn : 0 < en) :
    Manifold.IsSmoothEmbedding (modelWithCornersEuclideanQuadrant m)
      𝓘(ℝ, Fin m → ℝ) ∞ (EllipsoidVerification.quadrantCoefficientMap m e0 en) ∧
    IsProperMap (EllipsoidVerification.quadrantCoefficientMap m e0 en) ∧
    IsClosed (Set.range (EllipsoidVerification.quadrantCoefficientMap m e0 en)) :=
  EllipsoidVerification.coefficient_transform_manifold_with_corners h0 hn

example (n : ℕ) (hn : 0 < n) (a b r : ℝ)
    (ha : 0 < a) (har : a < r) (hrb : r < b)
    (γ : ℝ) (hγ : 1 / (n : ℝ) < γ) (δ C : ℝ) (hδ : 0 < δ) (hC : 0 < C) :
    ∃ E F : EllipsoidVerification.FullEllipsoid n,
      E.axesIn a b ∧ F.axesIn a b ∧
      E.axisDistance (EllipsoidVerification.FullEllipsoid.sphere n r (ha.trans har)) < δ ∧
      F.axisDistance (EllipsoidVerification.FullEllipsoid.sphere n r (ha.trans har)) < δ ∧
      C * Real.rpow (E.volumeDistance F) γ < E.axisDistance F :=
  EllipsoidVerification.sharp_holder_recovery_near_sphere
    n hn a b r ha har hrb γ hγ δ C hδ hC

example (n : ℕ) (hn : 2 ≤ n) (a b r : ℝ)
    (ha : 0 < a) (har : a < r) (hrb : r < b)
    (γ : ℝ) (hγ : 1 / (n : ℝ) < γ) (δ C : ℝ) (hδ : 0 < δ) (hC : 0 < C) :
    ∃ E F : EllipsoidVerification.FullEllipsoid n,
      E.axesIn a b ∧ F.axesIn a b ∧
      E.axisDistance (EllipsoidVerification.FullEllipsoid.sphere n r (ha.trans har)) < δ ∧
      F.axisDistance (EllipsoidVerification.FullEllipsoid.sphere n r (ha.trans har)) < δ ∧
      E.volume n = F.volume n ∧
      C * Real.rpow (E.volumeDistance F) γ < E.axisDistance F :=
  EllipsoidVerification.sharp_holder_recovery_at_fixed_volume_near_sphere
    n hn a b r ha har hrb γ hγ δ C hδ hC
