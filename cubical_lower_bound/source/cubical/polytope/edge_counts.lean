import cubical.polytope.vertex_slice_counts
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! # The geometric one-face count is the ordinary graph edge count -/

open Set
open Classical

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

theorem edge_vertices_card (P : ConvexPolytope n)
    {F : Set (E n)} (hF : P.IsFace F) (hdF : faceDim F = 1) :
    (facePolytope P hF).vertices.card = 2 := by
  obtain ⟨v, hv⟩ := (facePolytope P hF).vertices_nonempty
  have hvP := (Finset.mem_filter.mp hv).1
  have hvF := (Finset.mem_filter.mp hv).2
  obtain ⟨w, hwP, hwF, hwv, hseg⟩ := spigolo_segmento P hF hdF hvP hvF
  have hvertices : (facePolytope P hF).vertices = {v, w} := by
    ext z
    simp only [facePolytope, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hzP, hzF⟩
      exact vertice_in_segmento_estremo_generico P hF hseg hzP hzF
    · rintro (rfl | rfl)
      · exact ⟨hvP, hvF⟩
      · exact ⟨hwP, hwF⟩
  rw [hvertices]
  simp [hwv.symm]

theorem incidentFaceNumber_one_eq_degree (P : ConvexPolytope n)
    (hdim : 1 ≤ P.dim) (v : VertexType P) :
    incidentFaceNumber P v 1 = (polytopeGraph P).degree v := by
  let D : DatiFetta P v.val := Classical.choice (esiste_datiFetta P v.property hdim)
  calc
    incidentFaceNumber P v 1 = faceNumber D.politopo 0 :=
      (D.faceNumber_eq_incidentFaceNumber 0).symm
    _ = D.politopo.vertices.card := faceNumber_zero D.politopo
    _ = (polytopeGraph P).degree v := D.vertices_card_eq_degree

theorem sum_degrees_eq_two_faceNumber (P : ConvexPolytope n) (hdim : 1 ≤ P.dim) :
    ∑ v : VertexType P, (polytopeGraph P).degree v = faceNumber P 1 * 2 := by
  calc
    _ = ∑ v : VertexType P, incidentFaceNumber P v 1 := by
      apply Finset.sum_congr rfl
      intro v _
      exact (incidentFaceNumber_one_eq_degree P hdim v).symm
    _ = faceNumber P 1 * 2 :=
      sum_incidentFaceNumber_of_uniform_vertices P 1 2
        (fun F => edge_vertices_card P F.val.property F.property)

/-- In positive dimension, graph edges and exposed one-faces have the same count. -/
theorem edgeSet_card_eq_faceNumber (P : ConvexPolytope n) (hdim : 1 ≤ P.dim) :
    Fintype.card (polytopeGraph P).edgeSet = faceNumber P 1 := by
  have h := (polytopeGraph P).sum_degrees_eq_twice_card_edges
  rw [sum_degrees_eq_two_faceNumber P hdim] at h
  rw [SimpleGraph.card_edgeSet]
  omega

end LeanEval.Geometry.PlatonicClassification
