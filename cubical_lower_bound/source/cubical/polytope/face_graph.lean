import cubical.polytope.combinatorial_transport

/-! # The graph of a geometric face is the induced graph on its vertices -/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

def faceVertexEquiv (P : ConvexPolytope n) {F : Set (E n)} (hF : P.IsFace F) :
    VertexType (facePolytope P hF) ≃ {v : VertexType P // v.val ∈ F} := by
  classical
  exact {
  toFun v := ⟨⟨v.val, (Finset.mem_filter.mp v.property).1⟩,
    (Finset.mem_filter.mp v.property).2⟩
  invFun v := ⟨v.val.val, Finset.mem_filter.mpr ⟨v.val.property, v.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl }

def faceVertexInclusion (P : ConvexPolytope n) {F : Set (E n)} (hF : P.IsFace F)
    (v : VertexType (facePolytope P hF)) : VertexType P :=
  (faceVertexEquiv P hF v).val

theorem facePolytope_graph_adj_iff (P : ConvexPolytope n)
    {F : Set (E n)} (hF : P.IsFace F)
    (u v : VertexType (facePolytope P hF)) :
    (polytopeGraph (facePolytope P hF)).Adj u v ↔
      (polytopeGraph P).Adj (faceVertexInclusion P hF u) (faceVertexInclusion P hF v) := by
  constructor
  · rintro ⟨hne, G, hG, hdG, hu, hv⟩
    refine ⟨?_, G, isFace_of_facePolytope P hF hG, hdG, hu, hv⟩
    intro h
    exact hne (Subtype.ext (congrArg (fun x : VertexType P => x.val) h))
  · rintro ⟨hne, G, hG, hdG, hu, hv⟩
    have huF := (faceVertexEquiv P hF u).property
    have hvF := (faceVertexEquiv P hF v).property
    have huv : u.val ≠ v.val := by
      intro h
      exact hne (Subtype.ext h)
    have hseg := edge_eq_segment P hG hdG
      (faceVertexInclusion P hF u).property
      (faceVertexInclusion P hF v).property hu hv huv
    have hGF : G ⊆ F := by
      rw [hseg]
      exact (hF.1.convex (convex_convexHull ℝ _)).segment_subset huF hvF
    refine ⟨?_, G, facePolytope_isFace_of P hF hG hGF, hdG, hu, hv⟩
    intro h
    exact huv (congrArg Subtype.val h)

def faceGraphIso (P : ConvexPolytope n) {F : Set (E n)} (hF : P.IsFace F) :
    polytopeGraph (facePolytope P hF) ≃g
      (polytopeGraph P).induce {v : VertexType P | v.val ∈ F} where
  __ := faceVertexEquiv P hF
  map_rel_iff' := by
    intro u v
    exact (facePolytope_graph_adj_iff P hF u v).symm

end LeanEval.Geometry.PlatonicClassification
