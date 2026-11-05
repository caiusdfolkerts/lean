import cubical.quadrilateral_triangulation
import cubical.polytope.facet_geometry
import cubical.polytope.facet_counts
import cubical.polytope.edge_counts
import cubical.polytope.two_faces

/-!
# The cubical lower bounds in dimension three

The actual geometric facets form a quadrilateral surface. Its black
diagonals give a verified simplicial 2-cycle, so the full Fogelsanger
theorem supplies the remaining low-dimensional case of the cubical
lower bound theorem.
-/

open Set Classical

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope Cubical.Bipartite

variable {n : ℕ}

def blackFacetVertices (P : ConvexPolytope n) (c : (polytopeGraph P).Coloring Bool)
    (f : FacetType P) : Finset (Black c) :=
  Finset.univ.filter (fun b => b.val.val ∈ f.val.val)

def whiteFacetVertices (P : ConvexPolytope n) (c : (polytopeGraph P).Coloring Bool)
    (f : FacetType P) : Finset (White c) :=
  Finset.univ.filter (fun w => w.val.val ∈ f.val.val)

@[simp] theorem mem_blackFacetVertices (P : ConvexPolytope n)
    (c : (polytopeGraph P).Coloring Bool) (f : FacetType P) (b : Black c) :
    b ∈ blackFacetVertices P c f ↔ b.val.val ∈ f.val.val := by
  simp [blackFacetVertices]

@[simp] theorem mem_whiteFacetVertices (P : ConvexPolytope n)
    (c : (polytopeGraph P).Coloring Bool) (f : FacetType P) (w : White c) :
    w ∈ whiteFacetVertices P c f ↔ w.val.val ∈ f.val.val := by
  simp [whiteFacetVertices]

theorem IsCubical.facet_color_cards_three (P : ConvexPolytope n) (hc : IsCubical P)
    (hdim : P.dim = 3) (c : (polytopeGraph P).Coloring Bool) (f : FacetType P) :
    (blackFacetVertices P c f).card = 2 ∧ (whiteFacetVertices P c f).card = 2 := by
  have h := hc.facet_color_cards P (by omega) c f
  simpa only [blackFacetVertices, whiteFacetVertices, ← Fintype.card_subtype,
    hdim, Nat.reduceSub, pow_one] using h

theorem IsCubical.blackFacetVertices_injective_three (P : ConvexPolytope n)
    (hc : IsCubical P) (hdim : P.dim = 3) (c : (polytopeGraph P).Coloring Bool) :
    Function.Injective (blackFacetVertices P c) := by
  intro f g hfg
  obtain ⟨b, b', hbb', hp⟩ := Finset.card_eq_two.mp
    (hc.facet_color_cards_three P hdim c f).1
  have hbf : b.val.val ∈ f.val.val := (mem_blackFacetVertices P c f b).mp (by rw [hp]; simp)
  have hb'f : b'.val.val ∈ f.val.val := (mem_blackFacetVertices P c f b').mp (by rw [hp]; simp)
  have hbg : b.val.val ∈ g.val.val := (mem_blackFacetVertices P c g b).mp
    (by rw [← hfg, hp]; simp)
  have hb'g : b'.val.val ∈ g.val.val := (mem_blackFacetVertices P c g b').mp
    (by rw [← hfg, hp]; simp)
  have hne : b.val ≠ b'.val := fun h => hbb' (Subtype.ext h)
  have hnadj : ¬(polytopeGraph P).Adj b.val b'.val := fun h =>
    c.valid h (b.property.trans b'.property.symm)
  have hfd := f.property
  have hgd := g.property
  exact Subtype.ext (Subtype.ext (two_faces_eq_of_nonadjacent_vertices P
    f.val.property g.val.property (by omega) (by omega) b.val b'.val
    hbf hb'f hbg hb'g hne hnadj))

/-- The induced graph of a geometric square is complete between its
two color classes. This is deduced from the actual cube vertex degrees. -/
theorem IsCubical.facet_complete_three (P : ConvexPolytope n) (hc : IsCubical P)
    (hdim : P.dim = 3) (c : (polytopeGraph P).Coloring Bool) (f : FacetType P)
    (b : Black c) (hb : b.val.val ∈ f.val.val)
    (w : White c) (hw : w.val.val ∈ f.val.val) :
    (polytopeGraph P).Adj b.val w.val := by
  let N := {a : VertexType P // a.val ∈ f.val.val ∧ (polytopeGraph P).Adj b.val a}
  let Q := {w : White c // w.val.val ∈ f.val.val}
  let inc : N → Q := fun a =>
    ⟨⟨a.val, color_white_of_adj_black c b a.property.2⟩, a.property.1⟩
  have hinj : Function.Injective inc := by
    intro a a' h
    exact Subtype.ext (congrArg (fun q : Q => q.val.val) h)
  have hN : Fintype.card N = 2 := by
    have hfd := f.property
    exact (hc.face_neighbor_card P (by omega) f.val.property (by omega) b.val hb).trans (by omega)
  have hQ : Fintype.card Q = 2 := by
    simpa only [hdim, Nat.reduceSub, pow_one] using
      (hc.facet_color_cards P (by omega) c f).2
  have hsurj : Function.Surjective inc := by
    by_contra h
    have hlt := Fintype.card_lt_of_injective_not_surjective inc hinj h
    omega
  obtain ⟨a, ha⟩ := hsurj ⟨w, hw⟩
  have hav : a.val = w.val := congrArg (fun q : Q => q.val.val) ha
  exact hav ▸ a.property.2

/-- The two endpoint condition is equivalent to containment of an edge
in a facet, using the geometric segment theorem and convexity. -/
theorem edge_subset_facet_iff (P : ConvexPolytope n) {R : Set (E n)}
    (hR : P.IsFace R) (hdR : faceDim R = 1)
    (u v : VertexType P) (hu : u.val ∈ R) (hv : v.val ∈ R) (hne : u ≠ v)
    (f : FacetType P) : R ⊆ f.val.val ↔ u.val ∈ f.val.val ∧ v.val ∈ f.val.val := by
  constructor
  · intro h
    exact ⟨h hu, h hv⟩
  · rintro ⟨huf, hvf⟩
    rw [edge_eq_segment P hR hdR u.property v.property hu hv
      (fun h => hne (Subtype.ext h))]
    exact (f.val.property.1.convex (convex_convexHull ℝ _)).segment_subset huf hvf

theorem edge_card_facets_three (P : ConvexPolytope n) (hdim : P.dim = 3)
    (u v : VertexType P) (h : (polytopeGraph P).Adj u v) :
    (Finset.univ.filter (fun f : FacetType P => u.val ∈ f.val.val ∧ v.val ∈ f.val.val)).card = 2 := by
  obtain ⟨hne, R, hR, hdR, hu, hv⟩ := h
  have heq : Finset.univ.filter (fun f : FacetType P => u.val ∈ f.val.val ∧ v.val ∈ f.val.val) =
      Finset.univ.filter (fun f : FacetType P => R ⊆ f.val.val) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (edge_subset_facet_iff P hR hdR u v hu hv hne f).symm
  rw [heq]
  exact card_facets_containing_ridge P hR (by omega)

/-- A ridge step in dimension three contains a black-white geometric
edge, so it is a step of the quadrilateral surface. -/
theorem facetStep_three (P : ConvexPolytope n) (hdim : P.dim = 3)
    (c : (polytopeGraph P).Coloring Bool) (f g : FacetType P) (h : facetStep P f g) :
    Cubical.Quadrilateral.FacetStep (blackFacetVertices P c) (whiteFacetVertices P c) f g := by
  obtain ⟨R, hR, hRf, hRg, hdR⟩ := h
  obtain ⟨u, hu⟩ := (facePolytope P hR).vertices_nonempty
  have huP := (Finset.mem_filter.mp hu).1
  have huR := (Finset.mem_filter.mp hu).2
  obtain ⟨v, hvP, hvR, hvu, _⟩ := spigolo_segmento P hR (by omega) huP huR
  let u' : VertexType P := ⟨u, huP⟩
  let v' : VertexType P := ⟨v, hvP⟩
  have huv : (polytopeGraph P).Adj u' v' :=
    ⟨fun h => hvu (congrArg Subtype.val h).symm, R, hR, by omega, huR, hvR⟩
  cases hcu : c u' with
  | false =>
    let b : Black c := ⟨u', hcu⟩
    let w : White c := ⟨v', color_white_of_adj_black c b huv⟩
    exact ⟨b, (mem_blackFacetVertices P c f b).mpr (hRf huR),
      (mem_blackFacetVertices P c g b).mpr (hRg huR),
      w, (mem_whiteFacetVertices P c f w).mpr (hRf hvR),
      (mem_whiteFacetVertices P c g w).mpr (hRg hvR)⟩
  | true =>
    let w : White c := ⟨u', hcu⟩
    let b : Black c := ⟨v', color_black_of_adj_white c w huv⟩
    exact ⟨b, (mem_blackFacetVertices P c f b).mpr (hRf hvR),
      (mem_blackFacetVertices P c g b).mpr (hRg hvR),
      w, (mem_whiteFacetVertices P c f w).mpr (hRf huR),
      (mem_whiteFacetVertices P c g w).mpr (hRg huR)⟩

/-- The genuine quadrilateral facet surface of a cubical three-polytope. -/
def IsCubical.quadrilateralSurface (P : ConvexPolytope n) (hc : IsCubical P)
    (hdim : P.dim = 3) (c : (polytopeGraph P).Coloring Bool) :
    Cubical.Quadrilateral.Surface (fun b : Black c => fun w : White c =>
      (polytopeGraph P).Adj b.val w.val) (FacetType P) where
  black := blackFacetVertices P c
  white := whiteFacetVertices P c
  black_card f := (hc.facet_color_cards_three P hdim c f).1
  white_card f := (hc.facet_color_cards_three P hdim c f).2
  black_injective := hc.blackFacetVertices_injective_three P hdim c
  complete f b hb w hw := hc.facet_complete_three P hdim c f b
    ((mem_blackFacetVertices P c f b).mp hb) w ((mem_whiteFacetVertices P c f w).mp hw)
  edge_facets b w h := by
    simpa only [mem_blackFacetVertices, mem_whiteFacetVertices] using
      edge_card_facets_three P hdim b.val w.val h
  cover_black b := by
    obtain ⟨f, hf⟩ := vertex_in_facet P (by omega) b.val
    exact ⟨f, (mem_blackFacetVertices P c f b).mpr hf⟩
  cover_white w := by
    obtain ⟨f, hf⟩ := vertex_in_facet P (by omega) w.val
    exact ⟨f, (mem_whiteFacetVertices P c f w).mpr hf⟩
  connected f g := by
    have h := facetStep_connected P (by omega) f g
    exact Relation.ReflTransGen.mono (fun a b hab => facetStep_three P hdim c a b hab) f g h

theorem card_facetType_three (P : ConvexPolytope n) (hdim : P.dim = 3) :
    Fintype.card (FacetType P) = faceNumber P 2 := by
  let e : FacetType P ≃ DimFaceType P 2 :=
    Equiv.subtypeEquivRight (fun F => by rw [hdim]; omega)
  exact (Fintype.card_congr e).trans (card_dimFaceType P 2)

/-- Exact edge-facet incidence for a cubical three-polytope. -/
theorem IsCubical.edge_facet_incidence_three (P : ConvexPolytope n) (hc : IsCubical P)
    (hdim : P.dim = 3) : faceNumber P 1 = 2 * faceNumber P 2 := by
  let c : (polytopeGraph P).Coloring Bool := (hc.bipartite P (by omega)).toColoring (by simp)
  have h := (hc.quadrilateralSurface P hdim c).incidence_count
  change 2 * Fintype.card (Edge c) = 4 * Fintype.card (FacetType P) at h
  rw [card_edges c, edgeSet_card_eq_faceNumber P (by omega), card_facetType_three P hdim] at h
  omega

theorem IsCubical.edge_lower_bound_three (P : ConvexPolytope n) (hc : IsCubical P)
    (hdim : P.dim = 3) : 2 * P.vertices.card ≤ faceNumber P 1 + 4 := by
  let c : (polytopeGraph P).Coloring Bool := (hc.bipartite P (by omega)).toColoring (by simp)
  obtain ⟨v, hv⟩ := P.vertices_nonempty
  obtain ⟨f, _⟩ := vertex_in_facet P (by omega) ⟨v, hv⟩
  letI : Nonempty (FacetType P) := ⟨f⟩
  have h := (hc.quadrilateralSurface P hdim c).edge_lower_bound
  change 2 * (Fintype.card (Black c) + Fintype.card (White c)) ≤ Fintype.card (Edge c) + 4 at h
  rw [card_vertices c, card_edges c, edgeSet_card_eq_faceNumber P (by omega)] at h
  simpa only [VertexType, Fintype.card_coe] using h

/-- The principal facet bound in dimension three. -/
theorem IsCubical.facet_lower_bound_three (P : ConvexPolytope n) (hc : IsCubical P)
    (hdim : P.dim = 3) : P.vertices.card ≤ faceNumber P 2 + 2 := by
  have h := hc.edge_lower_bound_three P hdim
  rw [hc.edge_facet_incidence_three P hdim] at h
  omega

end LeanEval.Geometry.PlatonicClassification
