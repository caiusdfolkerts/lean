import bier.sign_rank
import Mathlib.Analysis.Real.Sqrt

/-! # The spectral estimate from a balanced projection

Only ordinary finite sums, the actual projection identity, and Cauchy–Schwarz
are used. `SquaredOperatorBound` is the squared Euclidean operator estimate.
-/

noncomputable section

namespace Bier.Forster

open Classical Finset Matrix

variable {R C : Type*} [Fintype R] [Fintype C]

def SquaredOperatorBound (H : Matrix R C ℝ) (L : ℝ) : Prop :=
  ∀ x : R → ℝ, (∑ c, (∑ r, H r c * x r) ^ 2) ≤ L * ∑ r, (x r) ^ 2

theorem projection_row_square (P : Matrix R R ℝ) (hP : Pᵀ = P)
    (hPP : P * P = P) (r : R) : ∑ j, P r j ^ 2 = P r r := by
  have hs (j : R) : P j r = P r j := congrFun (congrFun hP r) j
  calc
    ∑ j, P r j ^ 2 = ∑ j, P r j * P j r := by simp [hs, pow_two]
    _ = (P * P) r r := rfl
    _ = P r r := by rw [hPP]

theorem sign_mul_eq_abs {h z : ℝ} (hh : h = 1 ∨ h = -1) (hz : 0 < h * z) :
    h * z = |z| := by
  rcases hh with rfl | rfl
  · simp only [one_mul] at hz ⊢
    exact (abs_of_pos hz).symm
  · have hn : z < 0 := by linarith
    rw [abs_of_neg hn]
    ring

theorem projection_column_lower_unit (P : Matrix R R ℝ) (hP : Pᵀ = P)
    (hPP : P * P = P) (t : ℝ) (ht : 0 ≤ t) (hdiag : ∀ r, P r r = t)
    (h z : R → ℝ) (hh : ∀ r, h r = 1 ∨ h r = -1)
    (hz : ∀ r, 0 < h r * z r) (hunit : ∑ r, z r ^ 2 = 1)
    (hfix : P *ᵥ z = z) :
    1 ≤ t * ∑ r, (P *ᵥ h) r ^ 2 := by
  have hcoord (r : R) : z r ^ 2 ≤ t := by
    have hc := Finset.sum_mul_sq_le_sq_mul_sq univ (fun j => P r j) z
    rw [projection_row_square P hP hPP r, hdiag r, hunit, mul_one] at hc
    change (P *ᵥ z) r ^ 2 ≤ t at hc
    simpa only [hfix] using hc
  have habs (r : R) : |z r| ≤ Real.sqrt t := by
    have hc := hcoord r
    have hs := Real.sq_sqrt ht
    have hn := Real.sqrt_nonneg t
    nlinarith [sq_abs (z r), abs_nonneg (z r)]
  have hsum : 1 ≤ Real.sqrt t * ∑ r, |z r| := by
    rw [← hunit, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r hr
    have hm := mul_le_mul_of_nonneg_right (habs r) (abs_nonneg (z r))
    nlinarith [sq_abs (z r)]
  have hdot : (P *ᵥ h) ⬝ᵥ z = ∑ r, |z r| := by
    rw [dotProduct_comm, ← hP, Matrix.dotProduct_transpose_mulVec, hfix]
    exact Finset.sum_congr rfl fun r _ => sign_mul_eq_abs (hh r) (hz r)
  have hc := Finset.sum_mul_sq_le_sq_mul_sq univ (P *ᵥ h) z
  change ((P *ᵥ h) ⬝ᵥ z) ^ 2 ≤ _ at hc
  rw [hdot, hunit, mul_one] at hc
  have hsum0 : 0 ≤ ∑ r, |z r| := Finset.sum_nonneg fun r _ => abs_nonneg _
  have hsq := pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by norm_num) hsum 2
  rw [mul_pow, Real.sq_sqrt ht, one_pow] at hsq
  exact hsq.trans (mul_le_mul_of_nonneg_left hc ht)

theorem projection_column_lower [Nonempty R] (P : Matrix R R ℝ) (hP : Pᵀ = P)
    (hPP : P * P = P) (t : ℝ) (ht : 0 ≤ t) (hdiag : ∀ r, P r r = t)
    (h z : R → ℝ) (hh : ∀ r, h r = 1 ∨ h r = -1)
    (hz : ∀ r, 0 < h r * z r) (hfix : P *ᵥ z = z) :
    1 ≤ t * ∑ r, (P *ᵥ h) r ^ 2 := by
  let S := ∑ r, z r ^ 2
  have hS : 0 < S := by
    apply Finset.sum_pos'
    · intro r hr; exact sq_nonneg _
    · let r : R := Classical.choice inferInstance
      refine ⟨r, mem_univ _, sq_pos_of_ne_zero ?_⟩
      intro he
      have hh := hz r
      simp [he] at hh
  let v : R → ℝ := fun r => z r / Real.sqrt S
  have hv : ∑ r, v r ^ 2 = 1 := by
    simp only [v, div_pow, ← Finset.sum_div, Real.sq_sqrt hS.le]
    exact div_self hS.ne'
  have hsv : ∀ r, 0 < h r * v r := by
    intro r
    simpa only [v, ← mul_div_assoc] using div_pos (hz r) (Real.sqrt_pos.mpr hS)
  have hfv : P *ᵥ v = v := by
    have he : v = (Real.sqrt S)⁻¹ • z := by
      funext r
      simp [v, div_eq_mul_inv, mul_comm]
    rw [he]
    rw [Matrix.mulVec_smul, hfix]
  exact projection_column_lower_unit P hP hPP t ht hdiag h v hh hsv hv hfv

theorem forster_bound_of_projection [Nonempty R]
    (H M : Matrix R C ℝ) (hH : Bier.IsSignMatrix H) (hM : Bier.SignRealizes H M)
    (P : Matrix R R ℝ) (hP : Pᵀ = P) (hPP : P * P = P)
    (t L : ℝ) (ht : 0 ≤ t) (hdiag : ∀ r, P r r = t)
    (hPM : P * M = M) (hL : SquaredOperatorBound H L) :
    (Fintype.card C : ℝ) ≤ L * Fintype.card R * t ^ 2 := by
  have hcol (c : C) : 1 ≤ t * ∑ r, (P *ᵥ (fun r => H r c)) r ^ 2 := by
    apply projection_column_lower P hP hPP t ht hdiag (fun r => H r c) (fun r => M r c)
      (fun r => hH r c) (fun r => hM r c)
    funext r
    exact congrFun (congrFun hPM r) c
  have hlo : (Fintype.card C : ℝ) ≤ t * ∑ c, ∑ r, (P *ᵥ (fun r => H r c)) r ^ 2 := by
    simpa only [Finset.sum_const, card_univ, nsmul_eq_mul, mul_one,
      Finset.mul_sum] using Finset.sum_le_sum (s := univ) (fun c _ => hcol c)
  have hup : (∑ c, ∑ r, (P *ᵥ (fun r => H r c)) r ^ 2) ≤
      L * Fintype.card R * t := by
    rw [Finset.sum_comm]
    calc
      (∑ r, ∑ c, (P *ᵥ (fun r => H r c)) r ^ 2) ≤
          ∑ r, L * ∑ j, P r j ^ 2 := by
        apply Finset.sum_le_sum
        intro r hr
        simpa only [Matrix.mulVec, dotProduct, mul_comm] using hL (fun j => P r j)
      _ = _ := by simp [projection_row_square P hP hPP, hdiag]; ring
  exact hlo.trans ((mul_le_mul_of_nonneg_left hup ht).trans_eq (by ring))

end Bier.Forster
