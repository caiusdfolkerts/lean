import cubical.polytope.lower_bound
import cubical.polytope.link_rigidity

/-! # Lemma 2 and Proposition 3 for actual convex cubical polytopes

Genericity is expressed by a nonzero polynomial in all coordinates of
the parameters at white vertices. Every placement where that polynomial
does not vanish has all the stated properties simultaneously.
-/

open Set Classical

noncomputable section

set_option maxHeartbeats 300000

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope Cubical.Bipartite

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

/-- The common generic certificate underlying Lemma 2 and Proposition 3.
All local rigidity and incidence facts are proved from cubical convexity. -/
theorem IsCubical.generic_facet_certificate (P : ConvexPolytope n)
    (hc : IsCubical P) (hdim : 4 ≤ P.dim)
    (c : (polytopeGraph P).Coloring Bool) :
    let C := cubicalFacetCover P hc (by omega) c
    ∃ Q : MvPolynomial (White c × Fin P.dim) ℝ, Q ≠ 0 ∧
      ∀ x : White c × Fin P.dim → ℝ, MvPolynomial.eval x Q ≠ 0 →
        C.LocalPropagation P.dim (fun w i => x (w, i)) ∧
        (∀ f, Function.Injective (C.restriction P.dim (fun w i => x (w, i)) f)) ∧
        (∀ f, Module.finrank ℝ (Cubical.solutionSpace P.dim
          (C.facetBlack f) (C.facetWhite f)
          (fun w : {w : White c // C.whiteMem f w} => fun i => x (w.val, i))) =
            2 ^ (P.dim - 1)) := by
  have hd3 : 3 ≤ P.dim := by omega
  let C := cubicalFacetCover P hc hd3 c
  let D := cubicalStarCover hc hd3 c
  have hpin : ∀ j : C.WhiteIncidence,
      Fintype.card (FacetPins j.val.1 j.val.2.val) = P.dim - 1 := by
    intro j
    exact hc.facetPins_card hd3 j.val.1 j.val.2.val j.property
  have hblack_count : ∀ f : FacetType P,
      Nat.card {b : Black c // C.blackMem f b} = 2 ^ ((P.dim - 1) - 1) := by
    intro f
    calc
      _ = Fintype.card {b : Black c // b.val.val ∈ f.val.val} := Nat.card_eq_fintype_card
      _ = 2 ^ (P.dim - 2) := (hc.facet_color_cards P hd3 c f).1
      _ = _ := by congr 1
  have hwhite_count : ∀ f : FacetType P,
      Nat.card {w : White c // C.whiteMem f w} = 2 ^ ((P.dim - 1) - 1) := by
    intro f
    calc
      _ = Fintype.card {w : White c // w.val.val ∈ f.val.val} := Nat.card_eq_fintype_card
      _ = 2 ^ (P.dim - 2) := (hc.facet_color_cards P hd3 c f).2
      _ = _ := by congr 1
  have hedge_count : ∀ f : FacetType P,
      Nat.card {e : Edge c // C.edgeMem f e} =
        (P.dim - 1) * 2 ^ ((P.dim - 1) - 1) := by
    intro f
    rw [Nat.card_eq_fintype_card]
    convert hc.facet_edges_card P hd3 c f using 1
  have hlink : ∀ j : C.WhiteIncidence,
      Cubical.Rigidity.GenericallyRigid (D.link j)
        (EuclideanSpace ℝ (Fin (P.dim - 1))) := by
    intro j
    exact hc.neighborLink_genericallyRigid P hdim j.val.2.val
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
  have h := D.generic_facet_certificate_intrinsic (P.dim - 1) (by omega)
    hpin hlink hwhite hdegree hblack_count hwhite_count hedge_count
  have hdim' : P.dim - 1 + 1 = P.dim := by omega
  rw [hdim'] at h
  exact h

/-- Lemma 2: generically, vanishing at the black neighbours of a white
vertex in one incident facet forces vanishing at every black neighbour. -/
theorem IsCubical.generic_local_propagation (P : ConvexPolytope n)
    (hc : IsCubical P) (hdim : 4 ≤ P.dim)
    (c : (polytopeGraph P).Coloring Bool) :
    ∃ Q : MvPolynomial (White c × Fin P.dim) ℝ, Q ≠ 0 ∧
      ∀ x : White c × Fin P.dim → ℝ, MvPolynomial.eval x Q ≠ 0 →
        (cubicalFacetCover P hc (by omega) c).LocalPropagation P.dim
          (fun w i => x (w, i)) := by
  obtain ⟨Q, hQ, h⟩ := hc.generic_facet_certificate P hdim c
  exact ⟨Q, hQ, fun x hx => (h x hx).1⟩

/-- Proposition 3, including the exact dimension of the solution space
of the subsystem on every facet. -/
theorem IsCubical.generic_facet_determination (P : ConvexPolytope n)
    (hc : IsCubical P) (hdim : 4 ≤ P.dim)
    (c : (polytopeGraph P).Coloring Bool) :
    let C := cubicalFacetCover P hc (by omega) c
    ∃ Q : MvPolynomial (White c × Fin P.dim) ℝ, Q ≠ 0 ∧
      ∀ x : White c × Fin P.dim → ℝ, MvPolynomial.eval x Q ≠ 0 →
        (∀ f, Function.Injective (C.restriction P.dim (fun w i => x (w, i)) f)) ∧
        (∀ f, Module.finrank ℝ (Cubical.solutionSpace P.dim
          (C.facetBlack f) (C.facetWhite f)
          (fun w : {w : White c // C.whiteMem f w} => fun i => x (w.val, i))) =
            2 ^ (P.dim - 1)) := by
  obtain ⟨Q, hQ, h⟩ := hc.generic_facet_certificate P hdim c
  exact ⟨Q, hQ, fun x hx => (h x hx).2⟩

end LeanEval.Geometry.PlatonicClassification
