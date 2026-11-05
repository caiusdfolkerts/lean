module

public import Ellipsoid.AxisIntegralTransform

@[expose] public section

noncomputable section

open MeasureTheory Set Polynomial Metric
open scoped BigOperators

namespace EllipsoidVerification

theorem angularMellinConstants_sum {n k : ℕ} (hk : 0 < k) (hkn : k < n) :
    angularMellinConstant n k + angularMellinConstant n ((k : ℝ) + 2) =
      (n : ℝ) * unitBallVolume (n - k) * unitBallVolume k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hknR : (k : ℝ) < n := by exact_mod_cast hkn
  have hnkR : 0 < (n : ℝ) - k := sub_pos.mpr hknR
  have hgk := (Real.Gamma_pos_of_pos (half_pos hkR)).ne'
  have hgnk := (Real.Gamma_pos_of_pos (half_pos hnkR)).ne'
  rw [angularMellinConstant, angularMellinConstant, unitBallVolume_eq, unitBallVolume_eq,
    Nat.cast_sub hkn.le]
  rw [show ((n : ℝ) + 2 - k) / 2 = ((n : ℝ) - k) / 2 + 1 by ring,
    show ((k : ℝ) + 2) / 2 = (k : ℝ) / 2 + 1 by ring,
    show ((n : ℝ) + 2 - ((k : ℝ) + 2)) / 2 = ((n : ℝ) - k) / 2 by ring,
    Real.Gamma_add_one (half_pos hkR).ne', Real.Gamma_add_one (half_pos hnkR).ne']
  field_simp [hgk, hgnk, hkR.ne', hnkR.ne']
  rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hkn.le]
  ring

theorem integrable_sphere_axisA {n k : ℕ} {a : Fin n → ℝ} (ha : ∀ i, 0 < a i) :
    Integrable (fun u : sphere (0 : Space n) 1 => axisA a k u / axisSupport a u ^ k)
      volume.toSphere := by
  have hc : Continuous (fun u : sphere (0 : Space n) 1 => axisA a k u / axisSupport a u ^ k) := by
    apply Continuous.div
    · unfold axisA
      fun_prop
    · exact ((continuous_axisSupport a).comp continuous_subtype_val).pow k
    · intro u
      exact pow_ne_zero _ (axisSupport_pos ha (by
        intro h; simpa [h] using u.property)).ne'
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem integrable_sphere_axisC {n k : ℕ} {a : Fin n → ℝ} (ha : ∀ i, 0 < a i) :
    Integrable (fun u : sphere (0 : Space n) 1 => axisC a k u / axisSupport a u ^ (k + 2))
      volume.toSphere := by
  have hc : Continuous (fun u : sphere (0 : Space n) 1 => axisC a k u / axisSupport a u ^ (k + 2)) := by
    apply Continuous.div
    · unfold axisC
      fun_prop
    · exact ((continuous_axisSupport a).comp continuous_subtype_val).pow (k + 2)
    · intro u
      exact pow_ne_zero _ (axisSupport_pos ha (by
        intro h; simpa [h] using u.property)).ne'
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The GSZ geometric integral formula, derived here from the actual Steiner
polynomial, its normal-map Jacobian, Gaussian integrals, and Mellin integration
by parts. The right side is the literal coefficient integral from the paper. -/
theorem intrinsicVolume_axisBody_eq_coefficientTransform {n k : ℕ}
    {a : Fin n → ℝ} (ha : ∀ i, 0 < a i) (hk : 0 < k) (hkn : k < n) :
    intrinsicVolume (axisBody a) k =
      unitBallVolume k * coefficientTransform (axisCoefficients a) k := by
  rw [intrinsicVolume_axisBody_eq_sphere (by omega) ha hk hkn.le,
    integral_add (integrable_sphere_axisA ha) (integrable_sphere_axisC ha),
    sphere_axisA_eq_headMellin ha hk hkn, sphere_axisC_eq_tailMellin ha hk hkn,
    ← axisHeadTail_integral_eq ha hk hkn, ← add_mul, angularMellinConstants_sum hk hkn,
    coefficientTransform_eq_axisHeadIntegral ha hk hkn.le]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp [hnR, (unitBallVolume_pos (n - k)).ne']

theorem FullEllipsoid.volume_eq_coefficientTransform {n k : ℕ} (E : FullEllipsoid n)
    (hk : 0 < k) (hkn : k < n) :
    E.volume k = unitBallVolume k * coefficientTransform (axisCoefficients E.semiaxis) k := by
  rw [E.volume_eq_axes]
  exact intrinsicVolume_axisBody_eq_coefficientTransform E.semiaxis_pos hk hkn

end EllipsoidVerification
