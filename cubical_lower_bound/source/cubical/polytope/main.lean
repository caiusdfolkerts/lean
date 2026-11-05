import cubical.polytope.main_higher
import cubical.polytope.dimension_three

/-! # Theorem 1 in its complete dimension range -/

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Theorem 1: the exact integer cubical edge lower bound for every d≥3. -/
theorem IsCubical.edge_bound_nat (P : ConvexPolytope n) (hc : IsCubical P)
    (hdim : 3 ≤ P.dim) :
    (P.dim + 1) * P.vertices.card ≤ 2 * faceNumber P 1 + 2 ^ P.dim := by
  by_cases hd4 : 4 ≤ P.dim
  · exact hc.edge_bound_high_dimension_nat P hd4
  · have hd3 : P.dim = 3 := by omega
    have h := hc.edge_lower_bound_three P hd3
    rw [hd3]
    norm_num
    omega

/-- Theorem 1 in the fractional form displayed in the paper. -/
theorem IsCubical.edge_bound (P : ConvexPolytope n) (hc : IsCubical P)
    (hdim : 3 ≤ P.dim) :
    ((P.dim : ℝ) + 1) / 2 * P.vertices.card - 2 ^ (P.dim - 1) ≤ faceNumber P 1 := by
  have hN := hc.edge_bound_nat P hdim
  have h : ((P.dim : ℝ) + 1) * P.vertices.card ≤
      2 * (faceNumber P 1 : ℝ) + 2 ^ P.dim := by exact_mod_cast hN
  have hd : P.dim - 1 + 1 = P.dim := by omega
  have hpow : (2 : ℝ) ^ P.dim = 2 * 2 ^ (P.dim - 1) := by
    conv_lhs => rw [← hd, pow_succ]
    ring
  rw [hpow] at h
  nlinarith

/-- The principal theorem expressed solely in the paper's face-number notation. -/
theorem cubical_lower_bound (P : ConvexPolytope n) (hc : IsCubical P)
    (hdim : 3 ≤ P.dim) :
    ((P.dim : ℝ) + 1) / 2 * faceNumber P 0 - 2 ^ (P.dim - 1) ≤ faceNumber P 1 := by
  rw [faceNumber_zero]
  exact hc.edge_bound P hdim

end LeanEval.Geometry.PlatonicClassification
