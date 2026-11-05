import cubical.polytope.simplicial_face_counts
import cubical.polytope.vertex_slice_simplicial
import cubical.polytope.edge_counts
import cubical.mpw

/-!
# Cubical MPW reduction on actual convex polytopes

Every local simplicial lower bound is applied to an actual hyperplane vertex
figure. The incidence equalities count the exposed faces of the original
polytope. No combinatorial or rigidity hypotheses are assumed in the
incidence inequalities below.
-/

open Set Classical
open scoped BigOperators

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- The exact geometric incidence form of the cubical MPW argument for
proper faces below facets. -/
theorem IsCubical.face_mpw_incidence (P : ConvexPolytope n) (hc : IsCubical P)
    (hdim : 4 ≤ P.dim) (i : ℕ) (hi : 1 ≤ i) (hid : i ≤ P.dim - 2) :
    2 * (P.dim - 1).choose (i - 1) * faceNumber P 1 ≤
      2 ^ i * faceNumber P i + (i - 1) * P.dim.choose i * P.vertices.card := by
  let D : (v : VertexType P) → DatiFetta P v.val := fun v =>
    Classical.choice (esiste_datiFetta P v.property (by change 1 ≤ P.dim; omega))
  have hd (v : VertexType P) : (D v).politopo.dim = P.dim - 1 := by
    have := (D v).politopo_dim_add_one (by omega)
    omega
  have hi' : i - 1 + 1 = i := by omega
  have hd' : P.dim - 1 + 1 = P.dim := by omega
  have hlocal (v : VertexType P) :
      (P.dim - 1).choose (i - 1) * (polytopeGraph P).degree v ≤
        faceNumber (D v).politopo (i - 1) + (i - 1) * P.dim.choose i := by
    have hs := (D v).isSimplicial_of_cubical hc (by omega)
    have h := hs.face_lower_bound (D v).politopo (by rw [hd]; omega)
      (i - 1) (by rw [hd]; omega)
    rw [(D v).vertices_card_eq_degree, hd, hd', hi'] at h
    exact h
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hlocal v)
  have hfaces := sum_vertexFigure_faceNumber_of_uniform_vertices D (i - 1) (2 ^ i)
    (fun F => by
      have h := hc.face_vertices_card P (by omega) F.val.property
        (by rw [F.property]; omega)
      simpa only [F.property, hi'] using h)
  rw [hi'] at hfaces
  have hdeg := sum_degrees_eq_two_faceNumber P (by omega)
  simpa only [← Finset.mul_sum, Finset.sum_add_distrib, hfaces, hdeg,
    Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul, VertexType,
    Fintype.card_coe, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hsum

/-- The exact geometric incidence form of the separate facet MPW argument. -/
theorem IsCubical.facet_mpw_incidence (P : ConvexPolytope n) (hc : IsCubical P)
    (hdim : 4 ≤ P.dim) :
    2 * (P.dim - 2) * faceNumber P 1 ≤
      2 ^ (P.dim - 1) * faceNumber P (P.dim - 1) +
        P.dim * (P.dim - 3) * P.vertices.card := by
  let D : (v : VertexType P) → DatiFetta P v.val := fun v =>
    Classical.choice (esiste_datiFetta P v.property (by change 1 ≤ P.dim; omega))
  have hd (v : VertexType P) : (D v).politopo.dim = P.dim - 1 := by
    have := (D v).politopo_dim_add_one (by omega)
    omega
  have hd1 : P.dim - 1 - 1 = P.dim - 2 := by omega
  have hd2 : P.dim - 1 - 2 = P.dim - 3 := by omega
  have hd3 : P.dim - 1 + 1 = P.dim := by omega
  have hd4 : P.dim - 2 + 1 = P.dim - 1 := by omega
  have hlocal (v : VertexType P) :
      (P.dim - 2) * (polytopeGraph P).degree v ≤
        faceNumber (D v).politopo (P.dim - 2) + P.dim * (P.dim - 3) := by
    have hs := (D v).isSimplicial_of_cubical hc (by omega)
    have h := hs.facet_lower_bound (D v).politopo (by rw [hd]; omega)
    rw [(D v).vertices_card_eq_degree, hd, hd1, hd2, hd3] at h
    simpa only [Nat.mul_comm] using h
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hlocal v)
  have hfaces := sum_vertexFigure_faceNumber_of_uniform_vertices D
    (P.dim - 2) (2 ^ (P.dim - 1)) (fun F => by
      have h := hc.face_vertices_card P (by omega) F.val.property
        (by rw [F.property]; omega)
      simpa only [F.property, hd4] using h)
  rw [hd4] at hfaces
  have hdeg := sum_degrees_eq_two_faceNumber P (by omega)
  simpa only [← Finset.mul_sum, Finset.sum_add_distrib, hfaces, hdeg,
    Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul, VertexType,
    Fintype.card_coe, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hsum

/-- Every cubical proper-face lower bound, retaining any available integral
imbalance improvement in the edge bound. -/
theorem IsCubical.face_lower_bound_of_edge_bound (P : ConvexPolytope n)
    (hc : IsCubical P) (hdim : 4 ≤ P.dim) (i : ℕ)
    (hi : 1 ≤ i) (hid : i ≤ P.dim - 2) (Δ : ℕ)
    (hedge : (P.dim + 1) * P.vertices.card + (P.dim - 1) * Δ ≤
      2 * faceNumber P 1 + 2 ^ P.dim) :
    (P.dim.choose i + (P.dim - 1).choose (i - 1)) * P.vertices.card +
        (P.dim - 1) * (P.dim - 1).choose (i - 1) * Δ ≤
      2 ^ i * faceNumber P i + 2 ^ P.dim * (P.dim - 1).choose (i - 1) :=
  Cubical.MPW.face_bound_from_incidence (by omega) hi hedge
    (hc.face_mpw_incidence P hdim i hi hid)

/-- The full facet lower bound, retaining the edge imbalance improvement. -/
theorem IsCubical.facet_lower_bound_of_edge_bound (P : ConvexPolytope n)
    (hc : IsCubical P) (hdim : 4 ≤ P.dim) (Δ : ℕ)
    (hedge : (P.dim + 1) * P.vertices.card + (P.dim - 1) * Δ ≤
      2 * faceNumber P 1 + 2 ^ P.dim) :
    2 * (P.dim - 1) * P.vertices.card + (P.dim - 1) * (P.dim - 2) * Δ ≤
      2 ^ (P.dim - 1) * faceNumber P (P.dim - 1) + (P.dim - 2) * 2 ^ P.dim :=
  Cubical.MPW.facet_bound_from_incidence (by omega) hedge
    (hc.facet_mpw_incidence P hdim)

/-- The unstrengthened facet formula with the factor of two cancelled,
exactly matching Corollary 5. -/
theorem IsCubical.facet_lower_bound_unstrengthened_of_edge_bound
    (P : ConvexPolytope n) (hc : IsCubical P) (hdim : 4 ≤ P.dim)
    (hedge : (P.dim + 1) * P.vertices.card ≤ 2 * faceNumber P 1 + 2 ^ P.dim) :
    (P.dim - 1) * P.vertices.card ≤
      2 ^ (P.dim - 2) * faceNumber P (P.dim - 1) + (P.dim - 2) * 2 ^ (P.dim - 1) :=
  Cubical.MPW.facet_bound_unstrengthened (by omega) hedge
    (hc.facet_mpw_incidence P hdim)

end LeanEval.Geometry.PlatonicClassification
