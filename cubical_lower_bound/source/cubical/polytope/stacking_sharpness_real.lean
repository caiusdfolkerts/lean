import cubical.polytope.stacking_sharpness

/-! # Stacked sharpness in the paper's displayed notation

These equalities explicitly translate the exact integer f-vector identities
into the rational-coefficient formulas in Theorem 1 and Corollary 5.
-/

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ} {P : ConvexPolytope n}

theorem IsStackedCubical.edge_equality_real (hP : IsStackedCubical P)
    (hdim : 3 ≤ P.dim) :
    ((P.dim : ℝ) + 1) / 2 * P.vertices.card - 2 ^ (P.dim - 1) = faceNumber P 1 := by
  have hNat := hP.edge_equality hdim
  have h : ((P.dim : ℝ) + 1) * P.vertices.card =
      2 * (faceNumber P 1 : ℝ) + 2 ^ P.dim := by exact_mod_cast hNat
  have hp : (2 : ℝ) ^ P.dim = 2 * 2 ^ (P.dim - 1) := by
    have he : P.dim - 1 + 1 = P.dim := by omega
    calc
      (2 : ℝ) ^ P.dim = 2 ^ (P.dim - 1 + 1) := congrArg (fun k : ℕ => (2 : ℝ) ^ k) he.symm
      _ = _ := by rw [pow_succ, mul_comm]
  rw [hp] at h
  linarith

theorem IsStackedCubical.face_equality_real (hP : IsStackedCubical P)
    (hdim : 3 ≤ P.dim) (i : ℕ) (hi : 1 ≤ i) (hid : i ≤ P.dim - 2) :
    ((P.dim.choose i : ℝ) + (P.dim - 1).choose (i - 1)) / 2 ^ i * P.vertices.card -
      2 ^ (P.dim - i) * (P.dim - 1).choose (i - 1) = faceNumber P i := by
  have hNat := hP.face_equality hdim i hi hid
  have h : ((P.dim.choose i : ℝ) + (P.dim - 1).choose (i - 1)) * P.vertices.card =
      2 ^ i * (faceNumber P i : ℝ) + 2 ^ P.dim * (P.dim - 1).choose (i - 1) := by
    exact_mod_cast hNat
  have hp : (2 : ℝ) ^ i * 2 ^ (P.dim - i) = 2 ^ P.dim := by
    rw [← pow_add, Nat.add_sub_of_le (by omega : i ≤ P.dim)]
  have hpos : (0 : ℝ) < 2 ^ i := pow_pos (by norm_num) _
  apply mul_left_cancel₀ (ne_of_gt hpos)
  calc
    2 ^ i * (((P.dim.choose i : ℝ) + (P.dim - 1).choose (i - 1)) / 2 ^ i *
        P.vertices.card - 2 ^ (P.dim - i) * (P.dim - 1).choose (i - 1)) =
      ((P.dim.choose i : ℝ) + (P.dim - 1).choose (i - 1)) * P.vertices.card -
        2 ^ P.dim * (P.dim - 1).choose (i - 1) := by
      rw [mul_sub, ← mul_assoc, mul_div_cancel₀ _ (ne_of_gt hpos), ← mul_assoc, hp]
    _ = 2 ^ i * faceNumber P i := by linarith

theorem IsStackedCubical.facet_equality_real (hP : IsStackedCubical P)
    (hdim : 3 ≤ P.dim) :
    ((P.dim : ℝ) - 1) / 2 ^ (P.dim - 2) * P.vertices.card -
      2 * ((P.dim : ℝ) - 2) = faceNumber P (P.dim - 1) := by
  have hNat := hP.facet_equality hdim
  have hd1 : 1 ≤ P.dim := by omega
  have hd2 : 2 ≤ P.dim := by omega
  have h : ((P.dim : ℝ) - 1) * P.vertices.card =
      2 ^ (P.dim - 2) * (faceNumber P (P.dim - 1) : ℝ) +
        ((P.dim : ℝ) - 2) * 2 ^ (P.dim - 1) := by exact_mod_cast hNat
  have hp : (2 : ℝ) ^ (P.dim - 1) = 2 * 2 ^ (P.dim - 2) := by
    have he : P.dim - 2 + 1 = P.dim - 1 := by omega
    rw [← he, pow_succ, mul_comm]
  have hpos : (0 : ℝ) < 2 ^ (P.dim - 2) := pow_pos (by norm_num) _
  apply mul_left_cancel₀ (ne_of_gt hpos)
  calc
    2 ^ (P.dim - 2) * (((P.dim : ℝ) - 1) / 2 ^ (P.dim - 2) * P.vertices.card -
        2 * ((P.dim : ℝ) - 2)) =
      ((P.dim : ℝ) - 1) * P.vertices.card - ((P.dim : ℝ) - 2) * 2 ^ (P.dim - 1) := by
      rw [mul_sub, ← mul_assoc, mul_div_cancel₀ _ (ne_of_gt hpos), hp]
      ring
    _ = 2 ^ (P.dim - 2) * faceNumber P (P.dim - 1) := by linarith

end LeanEval.Geometry.PlatonicClassification
