module

public import Papers.GraphicalZonotopes.ThreeTreeClassification
public import Papers.GraphicalZonotopes.ThreeTreeLatticeDilation

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
open scoped Pointwise

/-- The existence predicate in Theorem 6.1 is unchanged if indecomposability
is quantified over ordinary polytopes instead of all compact convex bodies.
The generalized-permutahedron presentation is derived from the actual sum. -/
theorem supportsFullIndecomposable_iff_polytopal {V : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    SupportsFullIndecomposable G ↔
      ∃ Q : Set (V → ℝ), IsFinitePolytope Q ∧ PolytopalMinkowskiIndecomposable Q ∧
        FullDimension Q ∧ IsWeakMinkowskiSummand Q (graphicalZonotope G) := by
  constructor
  · rintro ⟨Q,hQ,hi,hd,hs⟩
    refine ⟨Q,hQ,⟨hi.1,?_⟩,hd,hs⟩
    intro P R hP hR he
    exact hi.2 P R hP.compact hR.compact hP.convex hR.convex he
  · rintro ⟨Q,hQ,hi,hd,a,ha,R,hR,hcR,hnR,he⟩
    obtain ⟨hn,hsm,hbody,_,_⟩ := actual_summand_lowerSupport
      hQ.compact hQ.convex hi.1 hR hcR hnR ha.le he
    have hgp : IsGeneralizedPermutahedron Q := ⟨lowerSupport Q,hn,hsm,hbody⟩
    exact ⟨Q,hQ,(minkowskiIndecomposable_iff_polytopal hgp).mpr hi,hd,
      a,ha,R,hR,hcR,hnR,he⟩

/-- The two equivalences of Theorem 6.1 with the paper's literal maximal-clique
and induced-deletion conditions and its ordinary polytope convention. The
quantitative lattice witness is `admissible_threeTree_lattice_witness`. -/
theorem threeTree_classification_polytopal {n : ℕ} (hn : 4≤n)
    {G : SimpleGraph (Fin n)} (hG : IsThreeTree G) :
    ((∃ Q : Set (Fin n → ℝ), IsFinitePolytope Q ∧
      PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope G)) ↔
      ∀ T : Finset (Fin n),T.card=3 → G.IsClique T →
        (univ.filter (fun C : Finset (Fin n) => C.card=4 ∧
          Maximal G.IsClique (C : Set (Fin n)) ∧ T⊆C)).card≤3) ∧
    ((∃ Q : Set (Fin n → ℝ), IsFinitePolytope Q ∧
      PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope G)) ↔
      ∀ T : Finset (Fin n),T.card=3 → G.IsClique T →
        Nat.card (G.induce ((T : Set (Fin n))ᶜ)).ConnectedComponent≤3) := by
  have h := threeTree_classification_literal hn hG
  exact ⟨(supportsFullIndecomposable_iff_polytopal G).symm.trans h.1,
    (supportsFullIndecomposable_iff_polytopal G).symm.trans h.2⟩

end GraphicalZonotopes
