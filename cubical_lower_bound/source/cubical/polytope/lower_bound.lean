import cubical.polytope.square_stars
import cubical.polytope.facet_counts
import cubical.polytope.edge_counts
import cubical.abstract_card_bound

/-! # Applying the rank argument to actual convex cubical polytopes

The intermediate statements expose the vertex-link rigidity input. The
geometric rigidity theorem subsequently discharges that input in full.
-/

open Set Classical

noncomputable section

set_option maxHeartbeats 300000

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope Cubical.Bipartite

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

theorem IsCubical.asymmetric_edge_bound_of_rigid_links (P : ConvexPolytope n)
    (hc : IsCubical P) (hdim : 4 ≤ P.dim)
    (hlinks : ∀ v : VertexType P, Cubical.Rigidity.GenericallyRigid
      (neighborLinkGraph v) (EuclideanSpace ℝ (Fin (P.dim - 1))))
    (c : (polytopeGraph P).Coloring Bool) :
    P.dim * Fintype.card (Black c) + Fintype.card (White c) ≤
      faceNumber P 1 + 2 ^ (P.dim - 1) := by
  have hd3 : 3 ≤ P.dim := by omega
  let C := cubicalFacetCover P hc hd3 c
  let D := cubicalStarCover hc hd3 c
  have hpin : ∀ j : (cubicalFacetCover P hc hd3 c).WhiteIncidence,
      Fintype.card (FacetPins j.val.1 j.val.2.val) = P.dim - 1 := by
    intro j
    exact hc.facetPins_card hd3 j.val.1 j.val.2.val j.property
  have hblack_count : ∀ f : FacetType P,
      Nat.card {b : Black c // (cubicalFacetCover P hc hd3 c).blackMem f b} =
        2 ^ ((P.dim - 1) - 1) := by
    intro f
    calc
      _ = Fintype.card {b : Black c // b.val.val ∈ f.val.val} := Nat.card_eq_fintype_card
      _ = 2 ^ (P.dim - 2) := (hc.facet_color_cards P hd3 c f).1
      _ = _ := by congr 1
  have hwhite_count : ∀ f : FacetType P,
      Nat.card {w : White c // (cubicalFacetCover P hc hd3 c).whiteMem f w} =
        2 ^ ((P.dim - 1) - 1) := by
    intro f
    calc
      _ = Fintype.card {w : White c // w.val.val ∈ f.val.val} := Nat.card_eq_fintype_card
      _ = 2 ^ (P.dim - 2) := (hc.facet_color_cards P hd3 c f).2
      _ = _ := by congr 1
  have hedge_count : ∀ f : FacetType P,
      Nat.card {e : Edge c // (cubicalFacetCover P hc hd3 c).edgeMem f e} =
        (P.dim - 1) * 2 ^ ((P.dim - 1) - 1) := by
    intro f
    rw [Nat.card_eq_fintype_card]
    convert hc.facet_edges_card P hd3 c f using 1
  obtain ⟨v, hv⟩ := P.vertices_nonempty
  obtain ⟨f, _⟩ := vertex_in_facet P (by omega) ⟨v, hv⟩
  have hk : 0 < P.dim - 1 := by omega
  have hlink : ∀ j : C.WhiteIncidence,
      Cubical.Rigidity.GenericallyRigid (D.link j) (EuclideanSpace ℝ (Fin (P.dim - 1))) := by
    intro j
    exact hlinks j.val.2.val
  have hwhite : ∀ f (b : {b : Black c // C.blackMem f b}),
      Function.Injective (fun e : C.EdgeAtBlack f b => white c e.val.val) := by
    intro f b
    exact facet_global_whiteEndpoint_injective P hc hd3 c f b
  have hdegree : ∀ f (b : {b : Black c // C.blackMem f b}),
      Nat.card (C.EdgeAtBlack f b) ≤ (P.dim - 1) + 1 := by
    intro f b
    have hcard := hc.facet_black_degree P hd3 c f b
    have heq : Fintype.card (C.EdgeAtBlack f b) = P.dim - 1 := by
      exact (Fintype.card_congr (Equiv.refl _)).trans hcard
    rw [Nat.card_eq_fintype_card, heq]
    exact Nat.le_succ _
  have h := D.asymmetric_edge_bound_intrinsic (P.dim - 1) hk hpin hlink hwhite hdegree
    hblack_count hwhite_count hedge_count f
  have hdim' : P.dim - 1 + 1 = P.dim := by omega
  rw [hdim', card_edges c, edgeSet_card_eq_faceNumber P (by omega)] at h
  exact h

theorem IsCubical.strengthened_edge_bound_of_rigid_links (P : ConvexPolytope n)
    (hc : IsCubical P) (hdim : 4 ≤ P.dim)
    (hlinks : ∀ v : VertexType P, Cubical.Rigidity.GenericallyRigid
      (neighborLinkGraph v) (EuclideanSpace ℝ (Fin (P.dim - 1))))
    (c : (polytopeGraph P).Coloring Bool) :
    ((P.dim : ℝ) + 1) / 2 * P.vertices.card - 2 ^ (P.dim - 1) +
      ((P.dim : ℝ) - 1) / 2 *
        |(Fintype.card (Black c) : ℝ) - Fintype.card (White c)| ≤ faceNumber P 1 := by
  have hbN := hc.asymmetric_edge_bound_of_rigid_links P hdim hlinks c
  have hwN := hc.asymmetric_edge_bound_of_rigid_links P hdim hlinks (swapColoring c)
  rw [Fintype.card_congr (swappedBlackEquiv c),
    Fintype.card_congr (swappedWhiteEquiv c)] at hwN
  have hb : (P.dim : ℝ) * Fintype.card (Black c) + Fintype.card (White c) ≤
      (faceNumber P 1 : ℝ) + 2 ^ (P.dim - 1) := by exact_mod_cast hbN
  have hw : (Fintype.card (Black c) : ℝ) + (P.dim : ℝ) * Fintype.card (White c) ≤
      (faceNumber P 1 : ℝ) + 2 ^ (P.dim - 1) := by
    exact_mod_cast (by simpa only [Nat.add_comm] using hwN :
      Fintype.card (Black c) + P.dim * Fintype.card (White c) ≤
        faceNumber P 1 + 2 ^ (P.dim - 1))
  have hsum : (Fintype.card (Black c) : ℝ) + Fintype.card (White c) = P.vertices.card := by
    have h := card_vertices c
    simpa only [VertexType, Fintype.card_coe] using (show
      (Fintype.card (Black c) : ℝ) + Fintype.card (White c) =
        Fintype.card (VertexType P) by exact_mod_cast h)
  have hd : (1 : ℝ) ≤ P.dim := by exact_mod_cast (by omega : 1 ≤ P.dim)
  have h := Cubical.Counting.strengthened_of_asymmetric (P.dim : ℝ)
    (Fintype.card (Black c)) (Fintype.card (White c)) (faceNumber P 1)
    (2 ^ (P.dim - 1)) hd hb hw
  rwa [hsum] at h

end LeanEval.Geometry.PlatonicClassification
