import cubical.polytope.lower_bound
import cubical.polytope.link_rigidity

/-! # The cubical lower bound theorem in dimensions at least four

These are unconditional statements about genuine convex cubical polytopes.
All local rigidity and facet-cover hypotheses have been discharged.
-/

open Classical

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope Cubical.Bipartite

variable {n : ℕ}

/-- The asymmetric count underlying Theorem 1. -/
theorem IsCubical.asymmetric_edge_bound (P : ConvexPolytope n) (hc : IsCubical P)
    (hdim : 4 ≤ P.dim) (c : (polytopeGraph P).Coloring Bool) :
    P.dim * Fintype.card (Black c) + Fintype.card (White c) ≤
      faceNumber P 1 + 2 ^ (P.dim - 1) :=
  hc.asymmetric_edge_bound_of_rigid_links P hdim
    (hc.neighborLink_genericallyRigid P hdim) c

/-- The exact integer form of the strengthened inequality. -/
theorem IsCubical.strengthened_edge_bound_nat (P : ConvexPolytope n) (hc : IsCubical P)
    (hdim : 4 ≤ P.dim) (c : (polytopeGraph P).Coloring Bool) :
    (P.dim + 1) * P.vertices.card + (P.dim - 1) *
      Nat.dist (Fintype.card (Black c)) (Fintype.card (White c)) ≤
        2 * faceNumber P 1 + 2 ^ P.dim := by
  have hb := hc.asymmetric_edge_bound P hdim c
  have hw := hc.asymmetric_edge_bound P hdim (swapColoring c)
  rw [Fintype.card_congr (swappedBlackEquiv c),
    Fintype.card_congr (swappedWhiteEquiv c)] at hw
  have hw' : Fintype.card (Black c) + P.dim * Fintype.card (White c) ≤
      faceNumber P 1 + 2 ^ (P.dim - 1) := by simpa only [Nat.add_comm] using hw
  have h := Cubical.Counting.strengthened_nat P.dim (Fintype.card (Black c))
    (Fintype.card (White c)) (faceNumber P 1) (2 ^ (P.dim - 1)) (by omega) hb hw'
  have hsum : Fintype.card (Black c) + Fintype.card (White c) = P.vertices.card := by
    simpa only [VertexType, Fintype.card_coe] using card_vertices c
  have hd : P.dim - 1 + 1 = P.dim := by omega
  have hpow : 2 ^ P.dim = 2 * 2 ^ (P.dim - 1) := by
    conv_lhs => rw [← hd, pow_succ]
    exact Nat.mul_comm _ _
  rwa [hsum, ← hpow] at h

theorem IsCubical.edge_bound_high_dimension_nat (P : ConvexPolytope n)
    (hc : IsCubical P) (hdim : 4 ≤ P.dim) :
    (P.dim + 1) * P.vertices.card ≤ 2 * faceNumber P 1 + 2 ^ P.dim := by
  let c : (polytopeGraph P).Coloring Bool := (hc.bipartite P (by omega)).toColoring (by simp)
  exact (Nat.le_add_right _ _).trans (hc.strengthened_edge_bound_nat P hdim c)

/-- Theorem 1, the full imbalance-strengthened bound in dimension at least four. -/
theorem IsCubical.strengthened_edge_bound (P : ConvexPolytope n) (hc : IsCubical P)
    (hdim : 4 ≤ P.dim) (c : (polytopeGraph P).Coloring Bool) :
    ((P.dim : ℝ) + 1) / 2 * P.vertices.card - 2 ^ (P.dim - 1) +
      ((P.dim : ℝ) - 1) / 2 *
        |(Fintype.card (Black c) : ℝ) - Fintype.card (White c)| ≤ faceNumber P 1 :=
  hc.strengthened_edge_bound_of_rigid_links P hdim
    (hc.neighborLink_genericallyRigid P hdim) c

/-- The unstrengthened bound in dimensions at least four. -/
theorem IsCubical.edge_bound_high_dimension (P : ConvexPolytope n) (hc : IsCubical P)
    (hdim : 4 ≤ P.dim) :
    ((P.dim : ℝ) + 1) / 2 * P.vertices.card - 2 ^ (P.dim - 1) ≤ faceNumber P 1 := by
  let c : (polytopeGraph P).Coloring Bool := (hc.bipartite P (by omega)).toColoring (by simp)
  have h := hc.strengthened_edge_bound P hdim c
  have hd : (1 : ℝ) ≤ P.dim := by exact_mod_cast (by omega : 1 ≤ P.dim)
  have hcorr : 0 ≤ ((P.dim : ℝ) - 1) / 2 *
      |(Fintype.card (Black c) : ℝ) - Fintype.card (White c)| :=
    mul_nonneg (by linarith) (abs_nonneg _)
  linarith

end LeanEval.Geometry.PlatonicClassification
