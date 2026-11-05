import bier.forster.leverage

/-! # The balanced orthogonal projection supplied by equal leverage scores

This is an equivalent algebraic form of radial isotropic positioning.  Its
diagonal is constant and its range contains the positively rescaled original
feature columns.  It avoids choosing an unverified matrix square root.
-/

noncomputable section

namespace Bier.Forster

open Classical Finset Matrix

variable {k n : ℕ}

def gramProjection (W : Matrix (Fin k) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Wᵀ * (W * Wᵀ)⁻¹ * W

theorem gramProjection_transpose (W : Matrix (Fin k) (Fin n) ℝ) :
    (gramProjection W)ᵀ = gramProjection W := by
  simp [gramProjection, Matrix.transpose_mul, Matrix.transpose_nonsing_inv,
    Matrix.mul_assoc]

theorem gramProjection_idempotent (W : Matrix (Fin k) (Fin n) ℝ)
    (hW : (W * Wᵀ).det ≠ 0) : gramProjection W * gramProjection W = gramProjection W := by
  let G := W * Wᵀ
  change (Wᵀ * G⁻¹ * W) * (Wᵀ * G⁻¹ * W) = Wᵀ * G⁻¹ * W
  calc
    (Wᵀ * G⁻¹ * W) * (Wᵀ * G⁻¹ * W) = Wᵀ * G⁻¹ * G * G⁻¹ * W := by
      dsimp [G]
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [Matrix.mul_assoc Wᵀ G⁻¹ G, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hW),
        Matrix.mul_one]

theorem gramProjection_mul_transpose (W : Matrix (Fin k) (Fin n) ℝ)
    (hW : (W * Wᵀ).det ≠ 0) : gramProjection W * Wᵀ = Wᵀ := by
  simp only [gramProjection, Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hW), Matrix.mul_one]

theorem gramProjection_diag (W : Matrix (Fin k) (Fin n) ℝ) (i : Fin n) :
    gramProjection W i i =
      (fun a => W a i) ⬝ᵥ ((W * Wᵀ)⁻¹ *ᵥ (fun a => W a i)) := by
  rw [gramProjection, Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.transpose_apply,
    dotProduct, Matrix.mulVec]

def sqrtWeighted (U : Matrix (Fin k) (Fin n) ℝ) (w : Fin n → ℝ) :
    Matrix (Fin k) (Fin n) ℝ := U * diagonal (fun i => Real.sqrt (w i))

@[simp] theorem sqrtWeighted_apply (U : Matrix (Fin k) (Fin n) ℝ)
    (w : Fin n → ℝ) (a : Fin k) (i : Fin n) :
    sqrtWeighted U w a i = U a i * Real.sqrt (w i) := Matrix.mul_diagonal _ _ _ _

theorem sqrtWeighted_gram (U : Matrix (Fin k) (Fin n) ℝ)
    (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) :
    sqrtWeighted U w * (sqrtWeighted U w)ᵀ = weightedGram U w := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.transpose_apply, sqrtWeighted_apply, weightedGram_apply]
  apply Finset.sum_congr rfl
  intro i hi
  have hs := Real.sq_sqrt (hw i)
  calc
    U a i * Real.sqrt (w i) * (U b i * Real.sqrt (w i)) =
        (Real.sqrt (w i)) ^ 2 * (U a i * U b i) := by ring
    _ = _ := by rw [hs]; ring

theorem sqrtWeighted_projection_diag (U : Matrix (Fin k) (Fin n) ℝ)
    (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (i : Fin n) :
    gramProjection (sqrtWeighted U w) i i = leverage U w i := by
  rw [gramProjection_diag, sqrtWeighted_gram U w hw]
  have hv : (fun a => sqrtWeighted U w a i) = Real.sqrt (w i) • (fun a => U a i) := by
    funext a
    simp [mul_comm]
  rw [hv, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul, leverage]
  have hs := Real.sq_sqrt (hw i)
  rw [← mul_assoc, ← pow_two, hs]

/-- Positive diagonal rescaling puts the represented subspace in exactly
balanced position. -/
theorem exists_balancedProjection (U : Matrix (Fin k) (Fin n) ℝ)
    (hk : 0 < k) (hkn : k < n)
    (hu : ∀ S : KSubset (Fin n) k, 0 < minorSquare U S) :
    ∃ w : Fin n → ℝ, (∀ i, 0 < w i) ∧
      ∃ P : Matrix (Fin n) (Fin n) ℝ,
        Pᵀ = P ∧ P * P = P ∧
        P * (sqrtWeighted U w)ᵀ = (sqrtWeighted U w)ᵀ ∧
        ∀ i, P i i = (k : ℝ) / n := by
  obtain ⟨w, hw, hD, hl⟩ := exists_equal_leverage U hk hkn hu
  have hW : ((sqrtWeighted U w) * (sqrtWeighted U w)ᵀ).det ≠ 0 := by
    rw [sqrtWeighted_gram U w (fun i => (hw i).le)]
    exact hD.det_pos.ne'
  exact ⟨w, hw, gramProjection (sqrtWeighted U w), gramProjection_transpose _,
    gramProjection_idempotent _ hW, gramProjection_mul_transpose _ hW,
    fun i => (sqrtWeighted_projection_diag U w (fun j => (hw j).le) i).trans (hl i)⟩

end Bier.Forster
