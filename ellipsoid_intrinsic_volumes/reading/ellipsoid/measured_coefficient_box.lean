module

public import Ellipsoid.CoefficientProperness
public import Ellipsoid.PrincipalReconstruction
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.RingTheory.Polynomial.Vieta
public import Mathlib.Data.Finset.Powerset

@[expose] public section

noncomputable section

open Set Filter Polynomial Finset
open scoped BigOperators

namespace EllipsoidVerification

theorem finset_product_rpow {ι : Type*} [DecidableEq ι] (s : Finset ι) (d : ι → ℝ)
    (hd : ∀ i ∈ s, 0 ≤ d i) (r : ℝ) : (∏ i ∈ s, d i) ^ r = ∏ i ∈ s, (d i) ^ r := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi,
        Real.mul_rpow (hd i (Finset.mem_insert_self _ _))
          (Finset.prod_nonneg fun j hj => hd j (Finset.mem_insert_of_mem hj)),
        ih (fun j hj => hd j (Finset.mem_insert_of_mem hj))]

theorem elementaryOn_eq_sum_products {n k : ℕ} (d : Fin n → ℝ) (hk : k ≤ n) :
    elementaryOn Finset.univ d k =
      ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k, ∏ i ∈ s, d i := by
  rw [← coeff_prod_X_add_C Finset.univ d (by simpa using hk), Finset.prod_X_add_C_coeff]
  · simp only [Finset.card_univ, Fintype.card_fin, Nat.sub_sub_self hk]
  · simp

theorem product_powersetCard_products {n k : ℕ} (d : Fin n → ℝ) (hk : 0 < k) :
    (∏ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k, ∏ i ∈ s, d i) =
      (∏ i, d i) ^ ((n - 1).choose (k - 1)) := by
  classical
  let S := (Finset.univ : Finset (Fin n)).powersetCard k
  calc
    _ = ∏ s ∈ S, ∏ i : Fin n, if i ∈ s then d i else 1 := by
      apply Finset.prod_congr rfl
      intro s hs
      exact (Finset.prod_ite_mem_eq s d).symm
    _ = ∏ i : Fin n, ∏ s ∈ S, if i ∈ s then d i else 1 := Finset.prod_comm
    _ = ∏ i : Fin n, d i ^ ((n - 1).choose (k - 1)) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [← Finset.prod_filter, Finset.prod_const]
      congr 1
      have h := Finset.card_filter_powersetCard_subset ({i} : Finset (Fin n))
        Finset.univ k (Finset.subset_univ _)
        (by simpa only [Finset.card_singleton] using (Nat.succ_le_iff.mpr hk))
      simpa only [S, Finset.singleton_subset_iff, Finset.card_univ, Fintype.card_fin,
        Finset.card_singleton] using h
    _ = _ := Finset.prod_pow _ _ _

theorem elementary_ge_geometric_mean {n k : ℕ} (hn : 0 < n)
    (hk : k ≤ n) (d : Fin n → ℝ) (hd : ∀ i, 0 < d i) :
    (n.choose k : ℝ) * (∏ i, d i) ^ ((k : ℝ) / n) ≤ elementaryOn Finset.univ d k := by
  classical
  by_cases hk0 : k = 0
  · subst k
    simp [elementaryOn, Polynomial.coeff_zero_prod]
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
  let S := (Finset.univ : Finset (Fin n)).powersetCard k
  let N : ℝ := n.choose k
  have hN : 0 < N := by
    change (0 : ℝ) < (n.choose k : ℝ)
    exact_mod_cast Nat.choose_pos hk
  have hprod : 0 < ∏ i, d i := Finset.prod_pos fun i _ => hd i
  have hw : (∑ _s ∈ S, N⁻¹) = 1 := by
    simp only [Finset.sum_const, S, Finset.card_powersetCard, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    exact mul_inv_cancel₀ hN.ne'
  have h := Real.geom_mean_le_arith_mean_weighted S (fun _ => N⁻¹)
    (fun s => ∏ i ∈ s, d i) (fun s hs => inv_nonneg.mpr hN.le) hw
    (fun s hs => Finset.prod_nonneg fun i hi => (hd i).le)
  have hcount : (((n - 1).choose (k - 1) : ℕ) : ℝ) * N⁻¹ = (k : ℝ) / n := by
    have hnat := Nat.add_one_mul_choose_eq (n - 1) (k - 1)
    rw [Nat.sub_add_cancel hn, Nat.sub_add_cancel hkpos] at hnat
    have hr : (n : ℝ) * ((n - 1).choose (k - 1) : ℝ) = N * k := by
      change (n : ℝ) * ((n - 1).choose (k - 1) : ℝ) = (n.choose k : ℝ) * (k : ℝ)
      exact_mod_cast hnat
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    field_simp [hN.ne', hnR]
    nlinarith
  rw [← finset_product_rpow S (fun s => ∏ i ∈ s, d i)
      (fun s hs => Finset.prod_nonneg fun i hi => (hd i).le),
    product_powersetCard_products d hkpos, ← Real.rpow_natCast_mul hprod.le,
    hcount, ← Finset.mul_sum, ← elementaryOn_eq_sum_products d hk] at h
  have hmul := mul_le_mul_of_nonneg_left h hN.le
  simpa only [mul_inv_cancel_left₀ hN.ne'] using hmul

/-- The coefficient box determined by measured intrinsic volumes, as stated
in Section 5.1. Both constants and the exponent `2k/n` are retained exactly. -/
theorem measured_coefficient_box {n : ℕ} (hn : 0 < n) (E : FullEllipsoid n)
    (k : Fin (n + 1)) (hk : 0 < k.val) (hkn : k.val < n) :
    (n.choose k.val : ℝ) * (E.volume n / unitBallVolume n) ^ (2 * (k.val : ℝ) / n) ≤
      axisCoefficients E.semiaxis k ∧
    axisCoefficients E.semiaxis k < (E.volume k.val / unitBallVolume k.val) ^ 2 ∧
    axisCoefficients E.semiaxis (Fin.last n) = (E.volume n / unitBallVolume n) ^ 2 := by
  have hp : 0 < ∏ i, E.semiaxis i := Finset.prod_pos fun i _ => E.semiaxis_pos i
  have htop : E.volume n / unitBallVolume n = ∏ i, E.semiaxis i := by
    rw [E.volume_top hn]
    field_simp [(unitBallVolume_pos n).ne']
  have hmid : E.volume k.val / unitBallVolume k.val =
      coefficientTransform (axisCoefficients E.semiaxis) k.val := by
    rw [E.volume_eq_coefficientTransform hk hkn]
    field_simp [(unitBallVolume_pos k.val).ne']
  refine ⟨?_, ?_, ?_⟩
  · have h := elementary_ge_geometric_mean hn hkn.le (fun i => E.semiaxis i ^ 2)
      (fun i => sq_pos_of_pos (E.semiaxis_pos i))
    rw [Finset.prod_pow, ← Real.rpow_natCast_mul hp.le] at h
    simpa only [Nat.cast_ofNat, htop, axisCoefficients, axisCoefficientPolynomial, elementaryOn,
      show (2 : ℝ) * ((k.val : ℝ) / n) = 2 * (k.val : ℝ) / n by ring] using h
  · rw [hmid]
    exact coefficientTransform_coefficient_lt_sq
      (axisCoefficients_admissible E.semiaxis E.semiaxis_pos) k hk hkn
  · rw [axisCoefficients_last, htop]

end EllipsoidVerification
