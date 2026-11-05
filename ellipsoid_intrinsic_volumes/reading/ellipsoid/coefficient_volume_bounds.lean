module

public import Ellipsoid.AugmentedCoefficientRecovery
public import Ellipsoid.UniformRootRecovery

@[expose] public section

noncomputable section

open Polynomial Set
open scoped BigOperators

namespace EllipsoidVerification

theorem FullEllipsoid.volume_error_le {n : ℕ} (E F : FullEllipsoid n) (k : Fin n) :
    |E.volume (k.val + 1) - F.volume (k.val + 1)| ≤ E.volumeDistance F := by
  unfold FullEllipsoid.volumeDistance
  exact le_ciSup (f := fun k : Fin n =>
    |E.volume (k.val + 1) - F.volume (k.val + 1)|) (Set.finite_range _).bddAbove k

theorem FullEllipsoid.volumeDistance_nonneg {n : ℕ} (hn : 0 < n)
    (E F : FullEllipsoid n) : 0 ≤ E.volumeDistance F :=
  (abs_nonneg _).trans (E.volume_error_le F ⟨0, hn⟩)

theorem FullEllipsoid.axisDistance_le_of_perm {n : ℕ} (E F : FullEllipsoid n)
    (σ : Equiv.Perm (Fin n)) {C : ℝ} (hC : 0 ≤ C)
    (hσ : ∀ i, |E.semiaxis i - F.semiaxis (σ i)| ≤ C) : E.axisDistance F ≤ C := by
  apply (ciInf_le (Set.finite_range _).bddBelow σ).trans
  exact Real.iSup_le hσ hC

theorem axisCoefficientData_reconstruct {m : ℕ} (a : Fin (m + 1) → ℝ) :
    fixedEndpoints m 1 (axisCoefficientData a).2 (axisCoefficientData a).1 =
      axisCoefficients a := by
  simpa only [axisCoefficientData, axisCoefficients_zero] using
    fixedEndpoints_internalCoefficients m (axisCoefficients a)

theorem realRootCoefficients_squared_axes {n : ℕ} (a : Fin n → ℝ) (i : Fin n) :
    realRootCoefficients (fun j => a j ^ 2) i =
      (((-1 : ℝ) ^ (n - i.val)) * axisCoefficients a ⟨n - i.val, by omega⟩ : ℝ) := by
  have hp : realRootPolynomial (fun j => a j ^ 2) =
      (∏ j : Fin n, (X + C (-(a j ^ 2)) : ℝ[X])).map Complex.ofRealHom := by
    simp [realRootPolynomial, Polynomial.map_prod, sub_eq_add_neg]
  rw [realRootCoefficients, hp, Polynomial.coeff_map]
  have h := coeff_prod_X_add_C (Finset.univ : Finset (Fin n)) (fun j => -(a j ^ 2))
    (k := n - i.val) (by simp)
  simp only [Finset.card_univ, Fintype.card_fin, Nat.sub_sub_self i.isLt.le] at h
  rw [h]
  have hs := elementaryOn_scaling (Finset.univ : Finset (Fin n)) (fun j => a j ^ 2)
    (-1) (n - i.val)
  simpa only [neg_one_mul, elementaryOn, axisCoefficients, axisCoefficientPolynomial,
    Complex.ofRealHom_eq_coe] using
    congrArg (fun x : ℝ => (x : ℂ)) hs

theorem rootCoefficients_squared_axes_bound {m : ℕ} (a b : Fin (m + 1) → ℝ) :
    ‖realRootCoefficients (fun i => a i ^ 2) - realRootCoefficients (fun i => b i ^ 2)‖ ≤
      ‖axisCoefficientData a - axisCoefficientData b‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  rw [Pi.sub_apply, realRootCoefficients_squared_axes, realRootCoefficients_squared_axes,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, ← mul_sub,
    abs_mul, abs_pow, abs_neg, abs_one,
    one_pow, one_mul]
  by_cases hi : i.val = 0
  · have heq : (⟨m + 1 - i.val, by omega⟩ : Fin (m + 2)) = Fin.last (m + 1) := by
      apply Fin.ext
      simp only [Fin.val_mk, Fin.val_last]
      omega
    rw [heq]
    exact (norm_snd_le (axisCoefficientData a - axisCoefficientData b))
  · let j : Fin m := ⟨m - i.val, by omega⟩
    have heq : (⟨m + 1 - i.val, by omega⟩ : Fin (m + 2)) =
        ⟨j.val + 1, by omega⟩ := Fin.ext (by dsimp [j]; omega)
    rw [heq]
    exact (norm_le_pi_norm ((axisCoefficientData a - axisCoefficientData b).1) j).trans
      (norm_fst_le _)

def volumeCoefficientBound (n : ℕ) (b : ℝ) : ℝ :=
  (∑ k : Fin n, (unitBallVolume (k.val + 1))⁻¹) +
    2 * b ^ n / unitBallVolume n + 1

theorem volumeCoefficientBound_pos {n : ℕ} {b : ℝ} (hb : 0 ≤ b) :
    0 < volumeCoefficientBound n b := by
  have hs : 0 ≤ ∑ k : Fin n, (unitBallVolume (k.val + 1))⁻¹ :=
    Finset.sum_nonneg fun k _ => inv_nonneg.mpr (unitBallVolume_pos _).le
  have ht : 0 ≤ 2 * b ^ n / unitBallVolume n :=
    div_nonneg (mul_nonneg (by norm_num) (pow_nonneg hb n)) (unitBallVolume_pos n).le
  dsimp [volumeCoefficientBound]
  linarith

theorem volumeCoefficientBound_ge_inv {n : ℕ} {b : ℝ} (hb : 0 ≤ b) (k : Fin n) :
    (unitBallVolume (k.val + 1))⁻¹ ≤ volumeCoefficientBound n b := by
  have hs := Finset.single_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) =>
      inv_nonneg.mpr (unitBallVolume_pos (j.val + 1)).le) (Finset.mem_univ k)
  have ht : 0 ≤ 2 * b ^ n / unitBallVolume n :=
    div_nonneg (mul_nonneg (by norm_num) (pow_nonneg hb n)) (unitBallVolume_pos n).le
  dsimp [volumeCoefficientBound]
  linarith

theorem volumeCoefficientBound_ge_top {n : ℕ} {b : ℝ} (hb : 0 ≤ b) :
    2 * b ^ n / unitBallVolume n ≤ volumeCoefficientBound n b := by
  have hs : 0 ≤ ∑ k : Fin n, (unitBallVolume (k.val + 1))⁻¹ :=
    Finset.sum_nonneg fun k _ => inv_nonneg.mpr (unitBallVolume_pos _).le
  dsimp [volumeCoefficientBound]
  linarith

theorem FullEllipsoid.semiaxis_prod_le {n : ℕ} (E : FullEllipsoid n) {b : ℝ}
    (hb : ∀ i, E.semiaxis i ≤ b) : (∏ i, E.semiaxis i) ≤ b ^ n := by
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    Finset.prod_le_prod₀ (s := Finset.univ) (g := fun _ : Fin n => b)
      (fun i _ => (E.semiaxis_pos i).le) (fun i _ => hb i)

/-- The augmented coefficient output is controlled by the exact intrinsic
volume discrepancy, with a constant depending only on dimension and the
upper semiaxis bound. -/
theorem augmentedCoefficientMap_axisData_volume_bound {m : ℕ}
    (E F : FullEllipsoid (m + 1)) {b : ℝ} (hb : 0 ≤ b)
    (hE : ∀ i, E.semiaxis i ≤ b) (hF : ∀ i, F.semiaxis i ≤ b) :
    ‖augmentedCoefficientMap m (axisCoefficientData E.semiaxis) -
      augmentedCoefficientMap m (axisCoefficientData F.semiaxis)‖ ≤
      volumeCoefficientBound (m + 1) b * E.volumeDistance F := by
  have hD := E.volumeDistance_nonneg (by omega) F
  have hM := (volumeCoefficientBound_pos (n := m + 1) hb).le
  apply norm_prod_le_iff.mpr
  constructor
  · apply (pi_norm_le_iff_of_nonneg (mul_nonneg hM hD)).mpr
    intro k
    change |coefficientTransform (fixedEndpoints m 1 _ _) (k.val + 1) -
      coefficientTransform (fixedEndpoints m 1 _ _) (k.val + 1)| ≤ _
    rw [axisCoefficientData_reconstruct, axisCoefficientData_reconstruct]
    have hEvol := E.volume_eq_coefficientTransform (k := k.val + 1) (by omega) (by omega)
    have hFvol := F.volume_eq_coefficientTransform (k := k.val + 1) (by omega) (by omega)
    have hscale : |coefficientTransform (axisCoefficients E.semiaxis) (k.val + 1) -
        coefficientTransform (axisCoefficients F.semiaxis) (k.val + 1)| =
        (unitBallVolume (k.val + 1))⁻¹ *
          |E.volume (k.val + 1) - F.volume (k.val + 1)| := by
      rw [hEvol, hFvol, ← mul_sub, abs_mul,
        abs_of_pos (unitBallVolume_pos (k.val + 1))]
      field_simp [(unitBallVolume_pos (k.val + 1)).ne']
    rw [hscale]
    exact mul_le_mul
      (volumeCoefficientBound_ge_inv (n := m + 1) hb ⟨k.val, by omega⟩)
      (E.volume_error_le F (⟨k.val, by omega⟩ : Fin (m + 1))) (abs_nonneg _) hM
  · change |axisCoefficients E.semiaxis (Fin.last (m + 1)) -
        axisCoefficients F.semiaxis (Fin.last (m + 1))| ≤ _
    rw [axisCoefficients_last, axisCoefficients_last]
    let u := ∏ i, E.semiaxis i
    let v := ∏ i, F.semiaxis i
    have hu : 0 < u := Finset.prod_pos fun i _ => E.semiaxis_pos i
    have hv : 0 < v := Finset.prod_pos fun i _ => F.semiaxis_pos i
    have huB := E.semiaxis_prod_le hE
    have hvB := F.semiaxis_prod_le hF
    have hdiff : |u - v| ≤ E.volumeDistance F / unitBallVolume (m + 1) := by
      apply (le_div_iff₀ (unitBallVolume_pos (m + 1))).mpr
      have h := E.volume_error_le F (Fin.last m)
      simp only [Fin.val_last] at h
      rw [E.volume_top (by omega), F.volume_top (by omega), ← mul_sub,
        abs_mul, abs_of_pos (unitBallVolume_pos (m + 1))] at h
      simpa only [mul_comm] using h
    calc
      |u ^ 2 - v ^ 2| = |u - v| * (u + v) := by
        rw [sq_sub_sq, abs_mul, abs_of_pos (add_pos hu hv)]
        ring
      _ ≤ (E.volumeDistance F / unitBallVolume (m + 1)) * (2 * b ^ (m + 1)) :=
        mul_le_mul hdiff (by dsimp [u, v]; linarith) (add_pos hu hv).le
          (div_nonneg hD (unitBallVolume_pos (m + 1)).le)
      _ = (2 * b ^ (m + 1) / unitBallVolume (m + 1)) * E.volumeDistance F := by ring
      _ ≤ volumeCoefficientBound (m + 1) b * E.volumeDistance F :=
        mul_le_mul_of_nonneg_right (volumeCoefficientBound_ge_top hb) hD

end EllipsoidVerification
