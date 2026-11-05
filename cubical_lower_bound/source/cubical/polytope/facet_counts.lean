import cubical.polytope.facet_cover

/-! # Color-class and edge counts within actual cubical facets -/

open Set Classical

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope Cubical.Bipartite

variable {n : ℕ}

def faceColoring (P : ConvexPolytope n) (c : (polytopeGraph P).Coloring Bool)
    {F : Set (E n)} (hF : P.IsFace F) :
    (polytopeGraph (facePolytope P hF)).Coloring Bool :=
  SimpleGraph.Coloring.mk (fun v => c (faceVertexInclusion P hF v))
    (fun {_ _} h => c.valid ((facePolytope_graph_adj_iff P hF _ _).mp h))

def faceBlackEquiv (P : ConvexPolytope n) (c : (polytopeGraph P).Coloring Bool)
    {F : Set (E n)} (hF : P.IsFace F) :
    {b : Black c // b.val.val ∈ F} ≃ Black (faceColoring P c hF) where
  toFun b := ⟨⟨b.val.val.val, Finset.mem_filter.mpr ⟨b.val.val.property, b.property⟩⟩,
    b.val.property⟩
  invFun b := ⟨⟨faceVertexInclusion P hF b.val, b.property⟩,
    (faceVertexEquiv P hF b.val).property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def faceWhiteEquiv (P : ConvexPolytope n) (c : (polytopeGraph P).Coloring Bool)
    {F : Set (E n)} (hF : P.IsFace F) :
    {w : White c // w.val.val ∈ F} ≃ White (faceColoring P c hF) where
  toFun w := ⟨⟨w.val.val.val, Finset.mem_filter.mpr ⟨w.val.val.property, w.property⟩⟩,
    w.val.property⟩
  invFun w := ⟨⟨faceVertexInclusion P hF w.val, w.property⟩,
    (faceVertexEquiv P hF w.val).property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem cube_equivalence_color_cards (P : ConvexPolytope n) (k : ℕ)
    (φ : FaceType P ≃o FaceType (standardCube (k + 1)))
    (c : (polytopeGraph P).Coloring Bool) :
    Fintype.card (Black c) = 2 ^ k ∧ Fintype.card (White c) = 2 ^ k := by
  let ψ := cubeCodeGraphIso P (by omega : 1 ≤ k + 1) φ
  let colors : Cubical.Cube.Vertex (k + 1) → Bool := fun t => c (ψ.symm t)
  have hcolors : Cubical.Cube.ProperColoring colors := by
    intro t i
    exact color_eq_not_of_adj c (ψ.symm.map_rel_iff.mpr ⟨i, rfl⟩)
  let eb : Black c ≃ Cubical.Cube.Black colors :=
    ψ.toEquiv.subtypeEquiv fun v => by simp [colors]
  let ew : White c ≃ Cubical.Cube.White colors :=
    ψ.toEquiv.subtypeEquiv fun v => by simp [colors]
  have h := Cubical.Cube.card_colors colors hcolors
  exact ⟨(Fintype.card_congr eb).trans h.1, (Fintype.card_congr ew).trans h.2⟩

theorem IsCubical.facet_color_cards (P : ConvexPolytope n) (hc : IsCubical P)
    (hdim : 3 ≤ P.dim) (c : (polytopeGraph P).Coloring Bool) (f : FacetType P) :
    Fintype.card {b : Black c // b.val.val ∈ f.val.val} = 2 ^ (P.dim - 2) ∧
    Fintype.card {w : White c // w.val.val ∈ f.val.val} = 2 ^ (P.dim - 2) := by
  obtain ⟨φ⟩ := hc f.val.val f.val.property f.property
  have hd : P.dim - 1 = (P.dim - 2) + 1 := by omega
  rw [hd] at φ
  have h := cube_equivalence_color_cards (facePolytope P f.val.property)
    (P.dim - 2) φ (faceColoring P c f.val.property)
  exact ⟨(Fintype.card_congr (faceBlackEquiv P c f.val.property)).trans h.1,
    (Fintype.card_congr (faceWhiteEquiv P c f.val.property)).trans h.2⟩

def facetEdgeNeighborEquiv (P : ConvexPolytope n) (hc : IsCubical P)
    (hdim : 3 ≤ P.dim) (c : (polytopeGraph P).Coloring Bool) (f : FacetType P)
    (b : {b : Black c // (cubicalFacetCover P hc hdim c).blackMem f b}) :
    {e : {e : Edge c // (cubicalFacetCover P hc hdim c).edgeMem f e} //
      (cubicalFacetCover P hc hdim c).facetBlack f e = b} ≃
    {a : VertexType P // a.val ∈ f.val.val ∧ (polytopeGraph P).Adj b.val.val a} where
  toFun e := ⟨e.val.val.val.2.val, e.val.property.2, by
    have hb := congrArg
      (fun x : {b : Black c // (cubicalFacetCover P hc hdim c).blackMem f b} => x.val.val)
      e.property
    change e.val.val.val.1.val = b.val.val at hb
    rw [← hb]
    exact e.val.val.property⟩
  invFun a := ⟨⟨⟨(b.val, ⟨a.val, color_white_of_adj_black c b.val a.property.2⟩),
    a.property.2⟩, ⟨b.property, a.property.1⟩⟩, rfl⟩
  left_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (congrArg Subtype.val e.property).symm rfl
  right_inv _ := rfl

theorem IsCubical.facet_black_degree (P : ConvexPolytope n) (hc : IsCubical P)
    (hdim : 3 ≤ P.dim) (c : (polytopeGraph P).Coloring Bool) (f : FacetType P)
    (b : {b : Black c // (cubicalFacetCover P hc hdim c).blackMem f b}) :
    Fintype.card {e : {e : Edge c // (cubicalFacetCover P hc hdim c).edgeMem f e} //
      (cubicalFacetCover P hc hdim c).facetBlack f e = b} = P.dim - 1 := by
  rw [Fintype.card_congr (facetEdgeNeighborEquiv P hc hdim c f b)]
  have hdF := f.property
  have h := hc.face_neighbor_card P (by omega) f.val.property (by omega) b.val.val b.property
  exact h.trans (by omega)

theorem IsCubical.facet_edges_card (P : ConvexPolytope n) (hc : IsCubical P)
    (hdim : 3 ≤ P.dim) (c : (polytopeGraph P).Coloring Bool) (f : FacetType P) :
    Fintype.card {e : Edge c // (cubicalFacetCover P hc hdim c).edgeMem f e} =
      (P.dim - 1) * 2 ^ (P.dim - 2) := by
  let C := cubicalFacetCover P hc hdim c
  rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv (C.facetBlack f)), Fintype.card_sigma]
  dsimp only [C]
  simp_rw [hc.facet_black_degree P hdim c f]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  change Fintype.card {b : Black c // b.val.val ∈ f.val.val} * (P.dim - 1) = _
  rw [(hc.facet_color_cards P hdim c f).1]
  exact Nat.mul_comm _ _

theorem facet_whiteEndpoint_injective (P : ConvexPolytope n) (hc : IsCubical P)
    (hdim : 3 ≤ P.dim) (c : (polytopeGraph P).Coloring Bool) (f : FacetType P)
    (b : {b : Black c // (cubicalFacetCover P hc hdim c).blackMem f b}) :
    Function.Injective (fun e :
      {e : {e : Edge c // (cubicalFacetCover P hc hdim c).edgeMem f e} //
        (cubicalFacetCover P hc hdim c).facetBlack f e = b} =>
      (cubicalFacetCover P hc hdim c).facetWhite f e.val) := by
  intro e e' h
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext (congrArg Subtype.val (e.property.trans e'.property.symm))
    (congrArg Subtype.val h)

theorem facet_global_whiteEndpoint_injective (P : ConvexPolytope n) (hc : IsCubical P)
    (hdim : 3 ≤ P.dim) (c : (polytopeGraph P).Coloring Bool) (f : FacetType P)
    (b : {b : Black c // (cubicalFacetCover P hc hdim c).blackMem f b}) :
    Function.Injective (fun e :
      {e : {e : Edge c // (cubicalFacetCover P hc hdim c).edgeMem f e} //
        (cubicalFacetCover P hc hdim c).facetBlack f e = b} => white c e.val.val) := by
  intro e e' h
  exact facet_whiteEndpoint_injective P hc hdim c f b (Subtype.ext h)

end LeanEval.Geometry.PlatonicClassification
