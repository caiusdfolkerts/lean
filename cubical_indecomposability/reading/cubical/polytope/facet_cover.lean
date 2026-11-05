import cubical.polytope.cube_face_counts
import cubical.polytope.figura_al_vertice
import cubical.colored_graph
import cubical.facet_determination

/-! # The actual facet cover of a cubical convex polytope -/

open Set Classical

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope Cubical.Bipartite

variable {n : ℕ}

abbrev FacetType (P : ConvexPolytope n) :=
  {F : FaceType P // faceDim F.val + 1 = P.dim}

def facetStep (P : ConvexPolytope n) (f g : FacetType P) : Prop :=
  ∃ R : Set (E n), P.IsFace R ∧ R ⊆ f.val.val ∧ R ⊆ g.val.val ∧
    faceDim R + 2 = P.dim

theorem facet_proper (P : ConvexPolytope n) (f : FacetType P) :
    f.val.val ⊂ P.toSet := by
  refine (face_subset_toSet P f.val.property).ssubset_of_ne ?_
  intro heq
  have h := congrArg faceDim heq
  change faceDim f.val.val = P.dim at h
  have := f.property
  omega

theorem facetStep_connected (P : ConvexPolytope n) (hdim : 2 ≤ P.dim)
    (f g : FacetType P) : Relation.ReflTransGen (facetStep P) f g := by
  have hpath := ridgeConnectedAboveOne_sempre P P.toSet (toSet_isFace P) hdim
    f.val.val g.val.val f.val.property g.val.property
    (facet_proper P f) (facet_proper P g) f.property g.property
  let lift (X : Set (E n)) : FacetType P :=
    if hX : P.IsFace X ∧ faceDim X + 1 = P.dim then ⟨⟨X, hX.1⟩, hX.2⟩ else f
  have hstep : ∀ X Y,
      (P.IsFace X ∧ P.IsFace Y ∧ X ⊂ P.toSet ∧ Y ⊂ P.toSet ∧
        faceDim X + 1 = faceDim P.toSet ∧ faceDim Y + 1 = faceDim P.toSet ∧
        ∃ R, P.IsFace R ∧ R ⊂ X ∧ R ⊂ Y ∧ faceDim R + 2 = faceDim P.toSet) →
      facetStep P (lift X) (lift Y) := by
    rintro X Y ⟨hX, hY, _, _, hdX, hdY, R, hR, hRX, hRY, hdR⟩
    have hX' : P.IsFace X ∧ faceDim X + 1 = P.dim := ⟨hX, hdX⟩
    have hY' : P.IsFace Y ∧ faceDim Y + 1 = P.dim := ⟨hY, hdY⟩
    simp only [lift, dif_pos hX', dif_pos hY']
    exact ⟨R, hR, hRX.1, hRY.1, hdR⟩
  have h := Relation.ReflTransGen.lift lift hstep _ _ hpath
  have hf' : P.IsFace f.val.val ∧ faceDim f.val.val + 1 = P.dim :=
    ⟨f.val.property, f.property⟩
  have hg' : P.IsFace g.val.val ∧ faceDim g.val.val + 1 = P.dim :=
    ⟨g.val.property, g.property⟩
  change Relation.ReflTransGen (facetStep P) (lift f.val.val) (lift g.val.val) at h
  simpa only [lift, dif_pos hf', dif_pos hg'] using h

theorem vertex_in_facet (P : ConvexPolytope n) (hdim : 1 ≤ P.dim)
    (v : VertexType P) : ∃ f : FacetType P, v.val ∈ f.val.val := by
  obtain ⟨F, hF, hdF, hvF⟩ := face_contained_in_facet P
    (vertex_isFace P v.property) (by rw [faceDim_singleton]; omega)
  exact ⟨⟨⟨F, hF⟩, hdF⟩, hvF (Set.mem_singleton v.val)⟩

/-- A cubical facet has an incident edge at each of its vertices. -/
theorem IsCubical.facet_neighbor (P : ConvexPolytope n) (hc : IsCubical P)
    (hdim : 3 ≤ P.dim) (f : FacetType P) (v : VertexType P)
    (hv : v.val ∈ f.val.val) :
    ∃ a : VertexType P, a.val ∈ f.val.val ∧ (polytopeGraph P).Adj v a := by
  have hdF := f.property
  have hcard := hc.face_neighbor_card P (by omega) f.val.property (by omega) v hv
  have hpos : 0 < Fintype.card
      {a : VertexType P // a.val ∈ f.val.val ∧ (polytopeGraph P).Adj v a} := by
    rw [hcard]
    omega
  obtain ⟨a⟩ := Fintype.card_pos_iff.mp hpos
  exact ⟨a.val, a.property⟩

/-- If two cubical facets share a ridge, each new vertex is adjacent to a
vertex in that ridge. This is a geometric consequence of cube matching. -/
theorem IsCubical.facet_crossing (P : ConvexPolytope n) (hc : IsCubical P)
    (hdim : 3 ≤ P.dim) (f g : FacetType P) (hfg : facetStep P f g)
    (v : VertexType P) (hvg : v.val ∈ g.val.val) (hvf : v.val ∉ f.val.val) :
    ∃ w : VertexType P, w.val ∈ f.val.val ∧ (polytopeGraph P).Adj v w := by
  obtain ⟨R, hR, hRf, hRg, hdR⟩ := hfg
  obtain ⟨φ⟩ := hc g.val.val g.val.property g.property
  let Q := facePolytope P g.val.property
  let v' : VertexType Q := ⟨v.val, Finset.mem_filter.mpr ⟨v.property, hvg⟩⟩
  have hRQ : Q.IsFace R := facePolytope_isFace_of P g.val.property hR hRg
  obtain ⟨w', hwR, hvw'⟩ := cube_equivalence_ridge_matching Q (by omega) φ
    hRQ (by omega) v' (fun h => hvf (hRf h))
  exact ⟨faceVertexInclusion P g.val.property w', hRf hwR,
    (facePolytope_graph_adj_iff P g.val.property v' w').mp hvw'⟩

/-- The cover used in Proposition 3, instantiated with the actual vertices,
edges, facets, and ridge adjacency of the given convex polytope. -/
def cubicalFacetCover (P : ConvexPolytope n) (hc : IsCubical P)
    (hdim : 3 ≤ P.dim) (c : (polytopeGraph P).Coloring Bool) :
    Cubical.FacetCover (black c) (white c) (FacetType P) where
  blackMem f b := b.val.val ∈ f.val.val
  whiteMem f w := w.val.val ∈ f.val.val
  edgeMem f e := e.val.1.val.val ∈ f.val.val ∧ e.val.2.val.val ∈ f.val.val
  edgeBlack _ _ h := h.1
  edgeWhite _ _ h := h.2
  coverBlack b := vertex_in_facet P (by omega) b.val
  coverWhite w := vertex_in_facet P (by omega) w.val
  whiteIncident f w hw := by
    obtain ⟨a, ha, hwa⟩ := hc.facet_neighbor P hdim f w.val hw
    let b : Black c := ⟨a, color_black_of_adj_white c w hwa⟩
    exact ⟨⟨(b, w), hwa.symm⟩, ⟨ha, hw⟩, rfl⟩
  step := facetStep P
  connected := facetStep_connected P (by omega)
  crossing f g hfg b hb := by
    by_cases hbf : b.val.val ∈ f.val.val
    · exact Or.inl hbf
    · obtain ⟨w, hwf, hbw⟩ := hc.facet_crossing P hdim f g hfg b.val hb hbf
      let w' : White c := ⟨w, color_white_of_adj_black c b hbw⟩
      exact Or.inr ⟨⟨(b, w'), hbw⟩, rfl, hwf⟩

end LeanEval.Geometry.PlatonicClassification
