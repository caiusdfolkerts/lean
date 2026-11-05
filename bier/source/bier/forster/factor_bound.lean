import bier.forster.projection
import bier.forster.projection_bound
import bier.forster.generic_position
import bier.forster.rank_factor

/-! # The unrestricted Forster inequality for feature factorizations -/

noncomputable section

namespace Bier.Forster

open Classical Finset Matrix

variable {k n : ℕ} {C : Type*} [Fintype C]

theorem forster_bound_generic_factor (H : Matrix (Fin n) C ℝ)
    (hH : Bier.IsSignMatrix H) (U : Matrix (Fin k) (Fin n) ℝ)
    (V : Matrix (Fin k) C ℝ) (hUV : Bier.SignRealizes H (Uᵀ * V))
    (hk : 0 < k) (hkn : k < n)
    (hu : ∀ S : KSubset (Fin n) k, 0 < minorSquare U S)
    (L : ℝ) (hL : SquaredOperatorBound H L) :
    (n : ℝ) * Fintype.card C ≤ L * (k : ℝ) ^ 2 := by
  have hn : 0 < n := lt_trans hk hkn
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  obtain ⟨w, hw, P, hP, hPP, hPU, hdiag⟩ := exists_balancedProjection U hk hkn hu
  let N := (sqrtWeighted U w)ᵀ * V
  have hN : Bier.SignRealizes H N := by
    intro r c
    have he : N r c = Real.sqrt (w r) * (Uᵀ * V) r c := by
      simp only [N, Matrix.mul_apply, Matrix.transpose_apply, sqrtWeighted_apply]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    rw [he, ← mul_assoc, mul_comm (H r c), mul_assoc]
    exact mul_pos (Real.sqrt_pos.mpr (hw r)) (hUV r c)
  have hPN : P * N = N := by
    change P * ((sqrtWeighted U w)ᵀ * V) = (sqrtWeighted U w)ᵀ * V
    rw [← Matrix.mul_assoc, hPU]
  have hb := forster_bound_of_projection H N hH hN P hP hPP
    ((k : ℝ) / n) L (by positivity) hdiag hPN hL
  simp only [Fintype.card_fin] at hb
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have he : (n : ℝ) * (L * n * ((k : ℝ) / n) ^ 2) = L * (k : ℝ) ^ 2 := by
    field_simp
  exact (mul_le_mul_of_nonneg_left hb hnR.le).trans_eq he

theorem forster_bound_small_factor (H : Matrix (Fin n) C ℝ)
    (hH : Bier.IsSignMatrix H) (U : Matrix (Fin k) (Fin n) ℝ)
    (V : Matrix (Fin k) C ℝ) (hUV : Bier.SignRealizes H (Uᵀ * V))
    (hk : 0 < k) (hkn : k < n)
    (L : ℝ) (hL : SquaredOperatorBound H L) :
    (n : ℝ) * Fintype.card C ≤ L * (k : ℝ) ^ 2 := by
  obtain ⟨U', hsign, hgen⟩ := exists_generic_sign_factor H U V hUV
  exact forster_bound_generic_factor H hH U' V hsign hk hkn hgen L hL

end Bier.Forster
