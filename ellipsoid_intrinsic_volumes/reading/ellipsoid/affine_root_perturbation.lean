module

public import Ellipsoid.SharpnessSeeds
public import Ellipsoid.AxisElementary
public import Ellipsoid.PrincipalReconstruction

@[expose] public section

noncomputable section

open Polynomial Set
open scoped BigOperators

namespace EllipsoidVerification

theorem realMonicRootPolynomial_affine {n : ℕ} (u : Fin n → ℝ) (x ε : ℝ) (hε : ε ≠ 0) :
    realMonicRootPolynomial (fun i => x + ε * u i) =
      C (ε ^ n) * (realMonicRootPolynomial u).comp (C ε⁻¹ * (X - C x)) := by
  rw [realMonicRootPolynomial, realMonicRootPolynomial, Polynomial.prod_comp,
    show C (ε ^ n) = ∏ _ : Fin n, C ε by simp,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  simp only [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp]
  have hC : C ε * C ε⁻¹ = (1 : ℝ[X]) := by rw [← C_mul, mul_inv_cancel₀ hε, map_one]
  rw [mul_sub, ← mul_assoc, hC, one_mul, ← C_mul]
  simp only [C_add]
  ring

theorem realMonicRootPolynomial_affine_sub {n : ℕ} {u v : Fin n → ℝ} {c : ℝ}
    (h : realMonicRootPolynomial v = realMonicRootPolynomial u - C c)
    (x ε : ℝ) (hε : ε ≠ 0) :
    realMonicRootPolynomial (fun i => x + ε * u i) -
      realMonicRootPolynomial (fun i => x + ε * v i) = C (c * ε ^ n) := by
  rw [realMonicRootPolynomial_affine u x ε hε, realMonicRootPolynomial_affine v x ε hε,
    h, Polynomial.sub_comp, Polynomial.C_comp]
  ring_nf
  simp [← Polynomial.C_mul, mul_comm]

theorem realMonicRootPolynomial_coeff {n : ℕ} (d : Fin n → ℝ) {k : ℕ} (hk : k ≤ n) :
    (realMonicRootPolynomial d).coeff (n - k) = (-1 : ℝ) ^ k * elementaryOn Finset.univ d k := by
  have h := coeff_prod_X_add_C (Finset.univ : Finset (Fin n)) (fun i => -d i)
    (k := k) (by simpa using hk)
  simp only [Finset.card_univ, Fintype.card_fin, Polynomial.C_neg, ← sub_eq_add_neg] at h
  rw [realMonicRootPolynomial, h]
  simpa only [neg_one_mul] using elementaryOn_scaling Finset.univ d (-1) k

theorem axisCoefficient_difference_bound_of_rootPolynomial {n : ℕ} {a b : Fin n → ℝ}
    {c : ℝ} (h : realMonicRootPolynomial (fun i => a i ^ 2) -
      realMonicRootPolynomial (fun i => b i ^ 2) = C c) :
    ‖axisCoefficients a - axisCoefficients b‖ ≤ |c| := by
  apply (pi_norm_le_iff_of_nonneg (abs_nonneg c)).mpr
  intro k
  have hk : k.val ≤ n := by omega
  have hcoeff := congrArg (fun p : ℝ[X] => p.coeff (n - k.val)) h
  rw [Polynomial.coeff_sub, realMonicRootPolynomial_coeff _ hk,
    realMonicRootPolynomial_coeff _ hk, ← mul_sub, Polynomial.coeff_C] at hcoeff
  have habs := congrArg abs hcoeff
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] at habs
  change |elementaryOn Finset.univ (fun i => a i ^ 2) k.val -
    elementaryOn Finset.univ (fun i => b i ^ 2) k.val| ≤ |c|
  rw [habs]
  split_ifs <;> simp

theorem axisCoefficient_difference_bound_affine {n : ℕ} {u v a b : Fin n → ℝ} {c : ℝ}
    (h : realMonicRootPolynomial v = realMonicRootPolynomial u - C c)
    {x ε : ℝ} (hε : 0 < ε) (ha : ∀ i, a i ^ 2 = x + ε * u i)
    (hb : ∀ i, b i ^ 2 = x + ε * v i) :
    ‖axisCoefficients a - axisCoefficients b‖ ≤ |c| * ε ^ n := by
  have heq := realMonicRootPolynomial_affine_sub h x ε hε.ne'
  rw [← funext ha, ← funext hb] at heq
  simpa only [abs_mul, abs_pow, abs_of_pos hε] using
    axisCoefficient_difference_bound_of_rootPolynomial heq

end EllipsoidVerification
