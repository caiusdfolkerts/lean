module

public import Consolidated.SixActualAssembly
public import Papers.GlobalEightRowsPaper

@[expose] public section

/-!
# The paper's residual hypotheses, without a supplied labelling

For a ten-vertex four-polytope, the hypotheses excluded before Proposition 9
are exactly the applicability conditions of Theorem 3 and Proposition 8.
The small relation-row condition is existential over all realizations of the
ordinary face lattice. It is not restricted to the displayed realization.

This file identifies the literal paper count with the cardinality used by the
finite coverage theorem and constructs the finite vertex labels internally.
It assumes no finite classification result except at the final, explicitly
conditional coverage bridge.
-/

noncomputable section
set_option autoImplicit false

namespace Papers.RationalityTen.PaperResidualInterface

open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting
open Papers.PolytopeIncidenceCounting Papers.PolytopeFacetSurplus
open Papers.PolytopeRelationBudget Papers.PolytopeMasterBudget
open ChirotopeDensity ActualResidualTargetAssembly ActualLeafTargetCoverage

/-- The integer `c` in equation (4), with every actual local polygon-relation
rank retained. The finite labels only name the vertices of this realization. -/
def paperRelationRowCount {n : ℕ} (P : ConvexPolytope 4)
    (e : Fin n ≃ P.vertices) : ℤ :=
  facetExcess P - polygonExcess P +
    ∑ F : Face P 3, (facetPolygonExcess P F -
      (actualPolygonRelationRank P e F : ℤ))

/-- Equation (4) agrees with the actual number of selected facet-relation rows. -/
theorem paperRelationRowCount_eq_shared {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices) :
    paperRelationRowCount P e =
      sharedRelationCount P (actualPolygonRelationRank P e) :=
  (GlobalEightRowsPaper.selected_row_count_paper_formula P hP e).symm

/-- The sparse row indexing used by the exhaustive classification counts
exactly the same relations, including all local relation excesses. -/
theorem paperRelationRowCount_eq_sparse {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices) :
    paperRelationRowCount P e = (Fintype.card (SparseSharedRowIndex P e) : ℤ) := by
  rw [paperRelationRowCount_eq_shared P hP e, sparseSharedRowIndex_card P e]

/-- The word "admitting" in Proposition 8(iii): some full-dimensional
realization of this face lattice has at most eight selected relation rows. -/
def AdmitsEightSelectedFacetRelations (P : ConvexPolytope 4) : Prop :=
  ∃ Q : ConvexPolytope 4, Q.IsFullDim ∧
    CombinatoriallyEquivalent P Q ∧
    ∃ (n : ℕ) (e : Fin n ≃ Q.vertices), paperRelationRowCount Q e ≤ 8

/-- The existential paper predicate is precisely the input of the closed
global density theorem, not merely a bound at one chosen set of coordinates. -/
theorem admitsEightSelectedFacetRelations_iff (P : ConvexPolytope 4) :
    AdmitsEightSelectedFacetRelations P ↔
      ∃ Q : ConvexPolytope 4, Q.IsFullDim ∧
        CombinatoriallyEquivalent P Q ∧
        ∃ (n : ℕ) (e : Fin n ≃ Q.vertices),
          sharedRelationCount Q (actualPolygonRelationRank Q e) ≤ 8 := by
  constructor
  · rintro ⟨Q, hQ, hPQ, n, e, hc⟩
    exact ⟨Q, hQ, hPQ, n, e, (paperRelationRowCount_eq_shared Q hQ e) ▸ hc⟩
  · rintro ⟨Q, hQ, hPQ, n, e, hc⟩
    exact ⟨Q, hQ, hPQ, n, e, (paperRelationRowCount_eq_shared Q hQ e).symm ▸ hc⟩

/-- The exact earlier applicability conditions. The first disjunct includes
the vertex bound required for simple-vertex deletion; the next three are
Proposition 8(i) and both alternatives of Proposition 8(ii). -/
def EarlierReductionsApply (P : ConvexPolytope 4) : Prop :=
  (4 + 1 < P.vertices.card ∧ ∃ v : VertexType P, IsSimpleVertex P v) ∨
  P.vertices.card ≤ 9 ∨
  (nonsimplicialFacets P).card ≤ 9 ∨
  (nonsimpleVertices P).card ≤ 9 ∨
  AdmitsEightSelectedFacetRelations P

/-- A geometric, label-free description of the cases remaining in
Proposition 9. At ten vertices the nonsimple-vertex alternative is excluded
by `no_simple_vertex` itself; the precise equivalence is proved below. -/
structure RemainsAfterEarlyReductions (P : ConvexPolytope 4) : Prop where
  no_simple_vertex : ∀ v : VertexType P, ¬ IsSimpleVertex P v
  many_nonsimplicial_facets : 9 < (nonsimplicialFacets P).card
  no_eight_row_realization : ¬ AdmitsEightSelectedFacetRelations P

/-- If there is no simple vertex, the nonsimple-vertex count is the full
vertex count, without introducing a further hypothesis. -/
theorem nonsimpleVertices_card_of_no_simple
    (P : ConvexPolytope 4)
    (h : ∀ v : VertexType P, ¬ IsSimpleVertex P v) :
    (nonsimpleVertices P).card = P.vertices.card := by
  have heq : nonsimpleVertices P = Finset.univ := by
    unfold nonsimpleVertices
    apply Finset.filter_eq_self.mpr
    intro v _
    exact h v
  rw [heq, Finset.card_univ, Fintype.card_coe]

/-- The convenient residual structure is equivalent to the paper's words
"not removed by Theorem 3 and Proposition 8" in the stated ten-vertex domain. -/
theorem remains_iff_not_removed (P : ConvexPolytope 4)
    (hn : P.vertices.card = 10) :
    RemainsAfterEarlyReductions P ↔ ¬ EarlierReductionsApply P := by
  constructor
  · intro h hremoved
    rcases hremoved with ⟨_, v, hv⟩ | hnine | hfacets | hvertices | hrows
    · exact h.no_simple_vertex v hv
    · omega
    · have hlarge := h.many_nonsimplicial_facets
      omega
    · have hcount := nonsimpleVertices_card_of_no_simple P h.no_simple_vertex
      omega
    · exact h.no_eight_row_realization hrows
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro v hv
      exact h (Or.inl ⟨by omega, v, hv⟩)
    · by_contra hsmall
      apply h
      exact Or.inr (Or.inr (Or.inl (by omega)))
    · intro hrows
      exact h (Or.inr (Or.inr (Or.inr (Or.inr hrows))))

/-- Every realization and every labelling of a remaining type has at least
nine selected rows. This follows from the existential exclusion, not from an
assumption that local polygon-relation ranks are combinatorially invariant. -/
theorem RemainsAfterEarlyReductions.sparse_rows_ge_nine {n : ℕ}
    {P : ConvexPolytope 4} (h : RemainsAfterEarlyReductions P)
    (hP : P.IsFullDim) (e : Fin n ≃ P.vertices) :
    9 ≤ Fintype.card (SparseSharedRowIndex P e) := by
  by_contra hsmall
  have hcount := paperRelationRowCount_eq_sparse P hP e
  apply h.no_eight_row_realization
  refine ⟨P, hP, ⟨OrderIso.refl _⟩, n, e, ?_⟩
  omega

/-- The complete finite coverage theorem applies to the paper's geometric
residual hypotheses. The ten vertex labels are constructed from cardinality. -/
theorem hasTerminal_of_coverage
    (hcoverage : TenVertexResidualTargetCoverage)
    (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (hn : P.vertices.card = 10) (h : RemainsAfterEarlyReductions P) :
    HasTerminal P := by
  let e : Fin 10 ≃ P.vertices := (Finset.equivFinOfCardEq hn).symm
  exact hcoverage P hP e hn h.no_simple_vertex
    (by have hN := h.many_nonsimplicial_facets; omega)
    (h.sparse_rows_ge_nine hP e)

#print axioms paperRelationRowCount_eq_sparse
#print axioms remains_iff_not_removed
#print axioms hasTerminal_of_coverage

end Papers.RationalityTen.PaperResidualInterface
