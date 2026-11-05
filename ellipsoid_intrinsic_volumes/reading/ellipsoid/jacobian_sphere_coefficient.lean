module

public import Ellipsoid.AxisElementary
public import Ellipsoid.HomogeneousIntegration

@[expose] public section

noncomputable section

open MeasureTheory Polynomial Set Metric
open scoped BigOperators

namespace EllipsoidVerification

theorem normalOffsetJacobianPolynomial_coeff_unit {n k : ℕ}
    {a : Fin n → ℝ} (ha : ∀ i, 0 < a i) (hk : 0 < k) (hkn : k ≤ n)
    {x : Space n} (hx : ‖x‖ = 1) :
    (normalOffsetJacobianPolynomial a x).coeff (n - k) =
      axisA a k x / axisSupport a x ^ k + axisC a k x / axisSupport a x ^ (k + 2) := by
  have hx0 : x ≠ 0 := by intro h; simpa [h] using hx
  let h := axisSupport a x
  have hh : 0 < h := axisSupport_pos ha hx0
  have hcoef (s : Finset (Fin n)) (l : ℕ) (hl : l ≤ s.card) :
      (∏ i ∈ s, (X + C (h⁻¹ * a i ^ 2))).coeff (s.card - l) =
        (h⁻¹) ^ l * elementaryOn s (fun i => a i ^ 2) l := by
    rw [coeff_prod_X_add_C s _ hl, elementaryOn_scaling]
  have hfirst : (∏ i : Fin n, (X + C (h⁻¹ * a i ^ 2))).coeff (n - k) =
      elementaryOn Finset.univ (fun i => a i ^ 2) k / h ^ k := by
    simpa [div_eq_mul_inv, inv_pow, mul_comm] using
      hcoef Finset.univ k (by simpa using hkn)
  have hminor (i : Fin n) :
      (∏ j ∈ Finset.univ.erase i, (X + C (h⁻¹ * a j ^ 2))).coeff (n - k) =
        (h⁻¹) ^ (k - 1) * elementaryOn (Finset.univ.erase i) (fun j => a j ^ 2) (k - 1) := by
    have hcard : (Finset.univ.erase i : Finset (Fin n)).card = n - 1 := by simp
    have h := hcoef (Finset.univ.erase i) (k - 1) (by rw [hcard]; omega)
    simpa only [hcard, show n - 1 - (k - 1) = n - k by omega] using h
  have hv (i : Fin n) : supportPoint a x i = a i ^ 2 * x i / h := by
    simp only [supportPoint_eq, PiLp.smul_apply, axisMap, PiLp.toLp_apply, smul_eq_mul]
    dsimp [h]
    ring
  have hterm (i : Fin n) :
      supportPoint a x i * (x i - h⁻¹ * supportPoint a x i) *
        ((h⁻¹) ^ (k - 1) * elementaryOn (Finset.univ.erase i) (fun j => a j ^ 2) (k - 1)) =
      (a i ^ 2 * (x i) ^ 2 * elementaryOn (Finset.univ.erase i) (fun j => a j ^ 2) (k - 1)) / h ^ k -
      ((a i ^ 2) ^ 2 * (x i) ^ 2 * elementaryOn (Finset.univ.erase i) (fun j => a j ^ 2) (k - 1)) /
        h ^ (k + 2) := by
    rw [hv]
    obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    have hsub : l.succ - 1 = l := by omega
    simp only [hsub, inv_pow, pow_succ]
    field_simp [hh.ne']
  have hsum :
      (∑ i : Fin n, supportPoint a x i * (x i - h⁻¹ * supportPoint a x i) *
        (∏ j ∈ Finset.univ.erase i, (X + C (h⁻¹ * a j ^ 2))).coeff (n - k)) =
      axisA a k x / h ^ k -
        (∑ i : Fin n, (a i ^ 2) ^ 2 * (x i) ^ 2 *
          elementaryOn (Finset.univ.erase i) (fun j => a j ^ 2) (k - 1)) / h ^ (k + 2) := by
    calc
      _ = ∑ i : Fin n,
          ((a i ^ 2 * (x i) ^ 2 * elementaryOn (Finset.univ.erase i)
            (fun j => a j ^ 2) (k - 1)) / h ^ k -
          ((a i ^ 2) ^ 2 * (x i) ^ 2 * elementaryOn (Finset.univ.erase i)
            (fun j => a j ^ 2) (k - 1)) / h ^ (k + 2)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hminor i]
        exact hterm i
      _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div]
        rfl
  simp only [normalOffsetJacobianPolynomial, hx, one_div, inv_one, one_mul,
    Polynomial.coeff_add, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
  change (∏ i : Fin n, (X + C (h⁻¹ * a i ^ 2))).coeff (n - k) +
      (∑ i : Fin n, supportPoint a x i * (x i - h⁻¹ * supportPoint a x i) *
        (∏ j ∈ Finset.univ.erase i, (X + C (h⁻¹ * a j ^ 2))).coeff (n - k)) = _
  rw [hfirst, hsum, axisC_identity a hk x]
  change _ = axisA a k x / h ^ k + _ / h ^ (k + 2)
  rw [pow_add]
  dsimp [axisA]
  field_simp [hh.ne']
  ring

theorem intrinsicVolume_axisBody_eq_sphereJacobian {n k : ℕ} (hn : 0 < n)
    {a : Fin n → ℝ} (ha : ∀ i, 0 < a i) (hk : k ≤ n) :
    intrinsicVolume (axisBody a) k =
      ((n : ℝ) * unitBallVolume (n - k))⁻¹ *
        ∫ u : sphere (0 : Space n) 1,
          (normalOffsetJacobianPolynomial a (u : Space n)).coeff (n - k) ∂volume.toSphere := by
  rw [intrinsicVolume_axisBody_eq_jacobianIntegral hn ha hk,
    integral_homogeneous_zero_unitBall hn
      (integrableOn_normalOffsetJacobianPolynomial_coeff ha (n - k))
      (fun r hr x => by simp only [normalOffsetJacobianPolynomial_smul_pos a hr,
        Real.rpow_zero, one_mul])]
  rw [_root_.mul_inv_rev]
  ring

theorem intrinsicVolume_axisBody_eq_sphere {n k : ℕ} (hn : 0 < n)
    {a : Fin n → ℝ} (ha : ∀ i, 0 < a i) (hk : 0 < k) (hkn : k ≤ n) :
    intrinsicVolume (axisBody a) k =
      ((n : ℝ) * unitBallVolume (n - k))⁻¹ *
        ∫ u : sphere (0 : Space n) 1,
          (axisA a k u / axisSupport a u ^ k + axisC a k u / axisSupport a u ^ (k + 2))
            ∂volume.toSphere := by
  rw [intrinsicVolume_axisBody_eq_sphereJacobian hn ha hkn]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun u => normalOffsetJacobianPolynomial_coeff_unit ha hk hkn
    (by simpa using u.property)

end EllipsoidVerification
