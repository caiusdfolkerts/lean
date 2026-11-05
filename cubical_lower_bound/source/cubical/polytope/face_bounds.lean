import cubical.polytope.mpw
import cubical.polytope.main_higher
import cubical.polytope.dimension_three

/-!
# All cubical face-number lower bounds

The hypotheses are exactly those of a convex cubical polytope. The integral
forms retain all constants; the real forms below state the displayed
inequalities in the paper.
-/

open Classical

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope Cubical.Bipartite

variable {n : ℕ}

/-- The natural-number distance used by the integral formulas is exactly
the paper's absolute color imbalance. -/
theorem nat_dist_cast_real (a b : ℕ) : (Nat.dist a b : ℝ) = |(a : ℝ) - b| := by
  rcases le_total a b with h | h
  · rw [Nat.dist_eq_sub_of_le h, Nat.cast_sub h,
      abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast h))]
    ring
  · rw [Nat.dist_eq_sub_of_le_right h, Nat.cast_sub h,
      abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h))]

/-- The final paragraph's strengthened proper-face bound. -/
theorem IsCubical.strengthened_face_lower_bound_nat (P : ConvexPolytope n)
    (hc : IsCubical P) (hdim : 4 ≤ P.dim) (c : (polytopeGraph P).Coloring Bool)
    (i : ℕ) (hi : 1 ≤ i) (hid : i ≤ P.dim - 2) :
    (P.dim.choose i + (P.dim - 1).choose (i - 1)) * P.vertices.card +
        (P.dim - 1) * (P.dim - 1).choose (i - 1) *
          Nat.dist (Fintype.card (Black c)) (Fintype.card (White c)) ≤
      2 ^ i * faceNumber P i + 2 ^ P.dim * (P.dim - 1).choose (i - 1) :=
  hc.face_lower_bound_of_edge_bound P hdim i hi hid _
    (hc.strengthened_edge_bound_nat P hdim c)

/-- The final paragraph's strengthened facet bound. -/
theorem IsCubical.strengthened_facet_lower_bound_nat (P : ConvexPolytope n)
    (hc : IsCubical P) (hdim : 4 ≤ P.dim) (c : (polytopeGraph P).Coloring Bool) :
    2 * (P.dim - 1) * P.vertices.card + (P.dim - 1) * (P.dim - 2) *
        Nat.dist (Fintype.card (Black c)) (Fintype.card (White c)) ≤
      2 ^ (P.dim - 1) * faceNumber P (P.dim - 1) + (P.dim - 2) * 2 ^ P.dim :=
  hc.facet_lower_bound_of_edge_bound P hdim _
    (hc.strengthened_edge_bound_nat P hdim c)

/-- Corollary 5, all proper-face bounds, with integral scaling. -/
theorem IsCubical.face_lower_bound_nat (P : ConvexPolytope n)
    (hc : IsCubical P) (hdim : 3 ≤ P.dim) (i : ℕ)
    (hi : 1 ≤ i) (hid : i ≤ P.dim - 2) :
    (P.dim.choose i + (P.dim - 1).choose (i - 1)) * P.vertices.card ≤
      2 ^ i * faceNumber P i + 2 ^ P.dim * (P.dim - 1).choose (i - 1) := by
  by_cases hd4 : 4 ≤ P.dim
  · have h := hc.face_lower_bound_of_edge_bound P hd4 i hi hid 0
      (by simpa using hc.edge_bound_high_dimension_nat P hd4)
    simpa only [Nat.mul_zero, Nat.add_zero] using h
  · have hd3 : P.dim = 3 := by omega
    have hi1 : i = 1 := by omega
    have h := hc.edge_lower_bound_three P hd3
    norm_num [hd3, hi1]
    omega

/-- Corollary 5, the facet bound, with integral scaling. -/
theorem IsCubical.facet_lower_bound_nat (P : ConvexPolytope n)
    (hc : IsCubical P) (hdim : 3 ≤ P.dim) :
    (P.dim - 1) * P.vertices.card ≤
      2 ^ (P.dim - 2) * faceNumber P (P.dim - 1) + (P.dim - 2) * 2 ^ (P.dim - 1) := by
  by_cases hd4 : 4 ≤ P.dim
  · exact hc.facet_lower_bound_unstrengthened_of_edge_bound P hd4
      (hc.edge_bound_high_dimension_nat P hd4)
  · have hd3 : P.dim = 3 := by omega
    have h := hc.facet_lower_bound_three P hd3
    norm_num [hd3]
    omega

/-- Corollary 5 in the paper's displayed real-valued form. -/
theorem IsCubical.face_lower_bound (P : ConvexPolytope n)
    (hc : IsCubical P) (hdim : 3 ≤ P.dim) (i : ℕ)
    (hi : 1 ≤ i) (hid : i ≤ P.dim - 2) :
    ((P.dim.choose i : ℝ) + (P.dim - 1).choose (i - 1)) / 2 ^ i * P.vertices.card -
      2 ^ (P.dim - i) * (P.dim - 1).choose (i - 1) ≤ faceNumber P i := by
  have hNat := hc.face_lower_bound_nat P hdim i hi hid
  have h : ((P.dim.choose i : ℝ) + (P.dim - 1).choose (i - 1)) * P.vertices.card ≤
      2 ^ i * (faceNumber P i : ℝ) + 2 ^ P.dim * (P.dim - 1).choose (i - 1) := by
    exact_mod_cast hNat
  have hp : (2 : ℝ) ^ i * 2 ^ (P.dim - i) = 2 ^ P.dim := by
    rw [← pow_add, Nat.add_sub_of_le (by omega : i ≤ P.dim)]
  have hpos : (0 : ℝ) < 2 ^ i := pow_pos (by norm_num) _
  apply (mul_le_mul_iff_right₀ hpos).mp
  calc
    2 ^ i * (((P.dim.choose i : ℝ) + (P.dim - 1).choose (i - 1)) / 2 ^ i *
        P.vertices.card - 2 ^ (P.dim - i) * (P.dim - 1).choose (i - 1)) =
      ((P.dim.choose i : ℝ) + (P.dim - 1).choose (i - 1)) * P.vertices.card -
        2 ^ P.dim * (P.dim - 1).choose (i - 1) := by
      rw [mul_sub, ← mul_assoc, mul_div_cancel₀ _ (ne_of_gt hpos),
        ← mul_assoc, hp]
    _ ≤ 2 ^ i * faceNumber P i := by linarith

/-- Corollary 5's displayed facet formula. -/
theorem IsCubical.facet_lower_bound (P : ConvexPolytope n)
    (hc : IsCubical P) (hdim : 3 ≤ P.dim) :
    ((P.dim : ℝ) - 1) / 2 ^ (P.dim - 2) * P.vertices.card -
      2 * ((P.dim : ℝ) - 2) ≤ faceNumber P (P.dim - 1) := by
  have hNat := hc.facet_lower_bound_nat P hdim
  have hd1 : 1 ≤ P.dim := by omega
  have hd2 : 2 ≤ P.dim := by omega
  have h : ((P.dim : ℝ) - 1) * P.vertices.card ≤
      2 ^ (P.dim - 2) * (faceNumber P (P.dim - 1) : ℝ) +
        ((P.dim : ℝ) - 2) * 2 ^ (P.dim - 1) := by
    exact_mod_cast hNat
  have hp : (2 : ℝ) ^ (P.dim - 1) = 2 * 2 ^ (P.dim - 2) := by
    have he : P.dim - 2 + 1 = P.dim - 1 := by omega
    rw [← he, pow_succ, mul_comm]
  have hpos : (0 : ℝ) < 2 ^ (P.dim - 2) := pow_pos (by norm_num) _
  apply (mul_le_mul_iff_right₀ hpos).mp
  calc
    2 ^ (P.dim - 2) * (((P.dim : ℝ) - 1) / 2 ^ (P.dim - 2) * P.vertices.card -
        2 * ((P.dim : ℝ) - 2)) =
      ((P.dim : ℝ) - 1) * P.vertices.card - ((P.dim : ℝ) - 2) * 2 ^ (P.dim - 1) := by
      rw [mul_sub, ← mul_assoc, mul_div_cancel₀ _ (ne_of_gt hpos), hp]
      ring
    _ ≤ 2 ^ (P.dim - 2) * faceNumber P (P.dim - 1) := by linarith

/-- The strengthened proper-face formula in the paper's real-valued notation. -/
theorem IsCubical.strengthened_face_lower_bound (P : ConvexPolytope n)
    (hc : IsCubical P) (hdim : 4 ≤ P.dim) (c : (polytopeGraph P).Coloring Bool)
    (i : ℕ) (hi : 1 ≤ i) (hid : i ≤ P.dim - 2) :
    ((P.dim.choose i : ℝ) + (P.dim - 1).choose (i - 1)) / 2 ^ i * P.vertices.card -
      2 ^ (P.dim - i) * (P.dim - 1).choose (i - 1) +
      ((P.dim : ℝ) - 1) * (P.dim - 1).choose (i - 1) / 2 ^ i *
        |(Fintype.card (Black c) : ℝ) - Fintype.card (White c)| ≤ faceNumber P i := by
  have hNat := hc.strengthened_face_lower_bound_nat P hdim c i hi hid
  have hd1 : 1 ≤ P.dim := by omega
  have h : ((P.dim.choose i : ℝ) + (P.dim - 1).choose (i - 1)) * P.vertices.card +
      ((P.dim : ℝ) - 1) * (P.dim - 1).choose (i - 1) *
        (Nat.dist (Fintype.card (Black c)) (Fintype.card (White c)) : ℝ) ≤
      2 ^ i * (faceNumber P i : ℝ) + 2 ^ P.dim * (P.dim - 1).choose (i - 1) := by
    exact_mod_cast hNat
  rw [nat_dist_cast_real] at h
  have hp : (2 : ℝ) ^ i * 2 ^ (P.dim - i) = 2 ^ P.dim := by
    rw [← pow_add, Nat.add_sub_of_le (by omega : i ≤ P.dim)]
  have hpos : (0 : ℝ) < 2 ^ i := pow_pos (by norm_num) _
  apply (mul_le_mul_iff_right₀ hpos).mp
  calc
    2 ^ i * (((P.dim.choose i : ℝ) + (P.dim - 1).choose (i - 1)) / 2 ^ i *
        P.vertices.card - 2 ^ (P.dim - i) * (P.dim - 1).choose (i - 1) +
        ((P.dim : ℝ) - 1) * (P.dim - 1).choose (i - 1) / 2 ^ i *
          |(Fintype.card (Black c) : ℝ) - Fintype.card (White c)|) =
      ((P.dim.choose i : ℝ) + (P.dim - 1).choose (i - 1)) * P.vertices.card -
        2 ^ P.dim * (P.dim - 1).choose (i - 1) +
        ((P.dim : ℝ) - 1) * (P.dim - 1).choose (i - 1) *
          |(Fintype.card (Black c) : ℝ) - Fintype.card (White c)| := by
      rw [mul_add, mul_sub, ← mul_assoc, mul_div_cancel₀ _ (ne_of_gt hpos),
        ← mul_assoc, hp, ← mul_assoc, mul_div_cancel₀ _ (ne_of_gt hpos)]
    _ ≤ 2 ^ i * faceNumber P i := by linarith

/-- The strengthened facet formula, with the exact factor `2^(1-d)`
written as division by a positive natural power. -/
theorem IsCubical.strengthened_facet_lower_bound (P : ConvexPolytope n)
    (hc : IsCubical P) (hdim : 4 ≤ P.dim) (c : (polytopeGraph P).Coloring Bool) :
    ((P.dim : ℝ) - 1) / 2 ^ (P.dim - 2) * P.vertices.card -
      2 * ((P.dim : ℝ) - 2) +
      ((P.dim : ℝ) - 1) * ((P.dim : ℝ) - 2) / 2 ^ (P.dim - 1) *
        |(Fintype.card (Black c) : ℝ) - Fintype.card (White c)| ≤
      faceNumber P (P.dim - 1) := by
  have hNat := hc.strengthened_facet_lower_bound_nat P hdim c
  have hd1 : 1 ≤ P.dim := by omega
  have hd2 : 2 ≤ P.dim := by omega
  have h : 2 * ((P.dim : ℝ) - 1) * P.vertices.card +
      ((P.dim : ℝ) - 1) * ((P.dim : ℝ) - 2) *
        (Nat.dist (Fintype.card (Black c)) (Fintype.card (White c)) : ℝ) ≤
      2 ^ (P.dim - 1) * (faceNumber P (P.dim - 1) : ℝ) +
        ((P.dim : ℝ) - 2) * 2 ^ P.dim := by exact_mod_cast hNat
  rw [nat_dist_cast_real] at h
  have hp1 : (2 : ℝ) ^ (P.dim - 1) = 2 * 2 ^ (P.dim - 2) := by
    have he : P.dim - 2 + 1 = P.dim - 1 := by omega
    rw [← he, pow_succ, mul_comm]
  have hp2 : (2 : ℝ) ^ P.dim = 2 * 2 ^ (P.dim - 1) := by
    have he : P.dim - 1 + 1 = P.dim := by omega
    calc
      (2 : ℝ) ^ P.dim = 2 ^ (P.dim - 1 + 1) := congrArg (fun k : ℕ => (2 : ℝ) ^ k) he.symm
      _ = _ := by rw [pow_succ, mul_comm]
  have hpos : (0 : ℝ) < 2 ^ (P.dim - 1) := pow_pos (by norm_num) _
  have hpos' : (0 : ℝ) < 2 ^ (P.dim - 2) := pow_pos (by norm_num) _
  apply (mul_le_mul_iff_right₀ hpos).mp
  calc
    2 ^ (P.dim - 1) * (((P.dim : ℝ) - 1) / 2 ^ (P.dim - 2) * P.vertices.card -
        2 * ((P.dim : ℝ) - 2) +
        ((P.dim : ℝ) - 1) * ((P.dim : ℝ) - 2) / 2 ^ (P.dim - 1) *
          |(Fintype.card (Black c) : ℝ) - Fintype.card (White c)|) =
      2 * ((P.dim : ℝ) - 1) * P.vertices.card - ((P.dim : ℝ) - 2) * 2 ^ P.dim +
        ((P.dim : ℝ) - 1) * ((P.dim : ℝ) - 2) *
          |(Fintype.card (Black c) : ℝ) - Fintype.card (White c)| := by
      rw [hp2, hp1]
      field_simp
    _ ≤ 2 ^ (P.dim - 1) * faceNumber P (P.dim - 1) := by linarith

end LeanEval.Geometry.PlatonicClassification
