module

public import PaperVerification.FermionNewtonMatrixRecurrence

/-!
# The exact Schur determinant in Newton deletion

A determinant-preserving first-column operation proves the block formula
directly. The factor is the literal row pairing with the actual suffix
expansion; the argument does not invoke an unspecified nonzero constant.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Newton

open scoped BigOperators Matrix

variable {L : Type*} [Field L] {n : ℕ}

theorem adjoinPowerColumn_zero_row_det
    (z : L) (y scale : Fin n → L) (S : Matrix (Fin n) (Fin n) L) :
    (adjoinPowerColumn z y 0 scale S).det = z * (∏ k, scale k) * S.det := by
  let M := adjoinPowerColumn z y 0 scale S
  have hminor : M.submatrix Fin.succ Fin.succ = Matrix.diagonal scale * S := by
    ext k i
    simp only [M, Matrix.submatrix_apply, adjoinPowerColumn_succ_succ, Matrix.diagonal_mul]
  have h := Matrix.det_succ_row_zero M
  rw [Fin.sum_univ_succ] at h
  simp only [M, adjoinPowerColumn_zero_zero, adjoinPowerColumn_zero_succ,
    Pi.zero_apply, Fin.val_zero, pow_zero, one_mul, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero, Fin.succAbove_zero] at h
  change M.det = _
  rw [h, hminor, Matrix.det_mul, Matrix.det_diagonal]
  ring

theorem adjoinPowerColumn_det
    (z : L) (y row scale w : Fin n → L) (S : Matrix (Fin n) (Fin n) L)
    (hsolve : ∀ k, scale k * (S *ᵥ w) k = y k) :
    (adjoinPowerColumn z y row scale S).det =
      (z - row ⬝ᵥ w) * (∏ k, scale k) * S.det := by
  let M := adjoinPowerColumn z y row scale S
  let c : Fin (n + 1) → L := Fin.cases 1 (fun i ↦ -w i)
  let v : Fin (n + 1) → L := Fin.cases (z - row ⬝ᵥ w) 0
  have hcol : (fun k ↦ ∑ j, c j * M k j) = v := by
    funext k
    refine Fin.cases ?_ (fun k ↦ ?_) k
    · simp only [c, M, v, Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ,
        adjoinPowerColumn_zero_zero, adjoinPowerColumn_zero_succ, one_mul,
        neg_mul, Finset.sum_neg_distrib, dotProduct, sub_eq_add_neg]
      congr 2
      apply Finset.sum_congr rfl
      intro i hi
      ring
    · simp only [c, M, v, Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ,
        adjoinPowerColumn_succ_zero, adjoinPowerColumn_succ_succ, one_mul,
        neg_mul, Finset.sum_neg_distrib, Pi.zero_apply]
      have hs : (∑ i, w i * (scale k * S k i)) = scale k * (S *ᵥ w) k := by
        simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [hs, hsolve k, add_neg_cancel]
  let M' := Matrix.updateCol M 0 v
  have hdet : M'.det = M.det := by
    have h := Matrix.det_updateCol_sum M 0 c
    simp only [smul_eq_mul] at h
    rw [hcol] at h
    simpa only [c, Fin.cases_zero, one_mul, M'] using h
  have hzero (k : Fin (n + 1)) : M' k 0 = v k := Matrix.updateCol_self
  have hminor : M'.submatrix Fin.succ Fin.succ = Matrix.diagonal scale * S := by
    ext k i
    simp only [M', Matrix.submatrix_apply, Matrix.updateCol_ne (Fin.succ_ne_zero i),
      M, adjoinPowerColumn_succ_succ, Matrix.diagonal_mul]
  have hexpand := Matrix.det_succ_column_zero M'
  rw [Fin.sum_univ_succ] at hexpand
  simp only [hzero, v, Fin.cases_zero, Fin.cases_succ, Pi.zero_apply,
    Fin.val_zero, pow_zero, one_mul, mul_zero, zero_mul, Finset.sum_const_zero,
    add_zero, Fin.succAbove_zero, hminor, Matrix.det_mul, Matrix.det_diagonal] at hexpand
  rw [← hdet]
  exact hexpand.trans (by ring)

/-- The negative first-row factor used in the all-one profile. The actual
suffix coefficient vectors of powers one and two supply the eliminated
first column. -/
theorem adjoinPowerColumn_negative_det
    (z : L) (y r B₁ B₂ : Fin n → L) (hzy : ∀ k, y k ≠ z)
    (S : Matrix (Fin n) (Fin n) L)
    (hB₁ : S *ᵥ B₁ = y) (hB₂ : S *ᵥ B₂ = fun k ↦ y k ^ 2) :
    (adjoinPowerColumn z y (fun i ↦ z * r i) (fun k ↦ (y k - z)⁻¹) S).det =
      z * (1 - r ⬝ᵥ B₂ + z * (r ⬝ᵥ B₁)) *
        (∏ k, (y k - z)⁻¹) * S.det := by
  have hsolve : ∀ k, (y k - z)⁻¹ * (S *ᵥ (B₂ - z • B₁)) k = y k := by
    intro k
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hB₂, hB₁]
    change (y k - z)⁻¹ * (y k ^ 2 - z * y k) = y k
    rw [show y k ^ 2 - z * y k = (y k - z) * y k by ring,
      ← mul_assoc, inv_mul_cancel₀ (sub_ne_zero.mpr (hzy k)), one_mul]
  rw [adjoinPowerColumn_det z y (fun i ↦ z * r i) (fun k ↦ (y k - z)⁻¹)
    (B₂ - z • B₁) S hsolve]
  have hdot : (fun i ↦ z * r i) ⬝ᵥ (B₂ - z • B₁) =
      z * (r ⬝ᵥ B₂) - z ^ 2 * (r ⬝ᵥ B₁) := by
    simp only [dotProduct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring
  rw [hdot]
  ring

end PaperVerification.Fermion.Newton
