module

public import Consolidated.GlobalEightRowsCompletion

@[expose] public section

/-!
# Proposition 8(iii) in the paper's numerical and combinatorial formulations

The count is equation (4), with every local polygon-relation rank included.
The small count need hold at only one realization of the type. Global
rational density concerns every realization, including ones where local
polygon ranks drop. `GlobalEightRowsCompletion` proves that stronger bridge.
-/

noncomputable section
open Matrix Module Set Filter Topology
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting
open Papers.PolytopeIncidenceCounting Papers.PolytopeFacetSurplus
open Papers.PolytopeRelationBudget Papers.PolytopeMasterBudget

namespace Papers.RationalityTen.GlobalEightRowsPaper

open ChirotopeDensity MatroidChecked.MatrixClassificationCore

/-- The selected-row count is exactly equation (4), including all local
relation excesses. -/
theorem selected_row_count_paper_formula {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices) :
    sharedRelationCount P (actualPolygonRelationRank P e) =
      facetExcess P - polygonExcess P +
        ∑ F : Face P 3, (facetPolygonExcess P F -
          (actualPolygonRelationRank P e F : ℤ)) := by
  rw [Finset.sum_sub_distrib, sum_facet_polygon_excess P hP]
  unfold sharedRelationCount
  omega

/-- Proposition 8(iii), stated with the exact numerical count. The separate
rank-four classification is its sole input. -/
theorem proposition8iii_of_rank_four_density {n : ℕ}
    (hDensity : RankFourDensityInput)
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (hc : sharedRelationCount P (actualPolygonRelationRank P e) ≤ 8) :
    RationallyDense P := by
  apply actual_global_eight_shared_relations_of_rank_four_density hDensity P hP e
  have hcount := actualSharedRowIndex_card P e
  omega

/-- The same theorem with its hypothesis written literally as equation (4). -/
theorem proposition8iii_paper_formula_of_rank_four_density {n : ℕ}
    (hDensity : RankFourDensityInput)
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (hc : facetExcess P - polygonExcess P +
      (∑ F : Face P 3, (facetPolygonExcess P F -
        (actualPolygonRelationRank P e F : ℤ))) ≤ 8) :
    RationallyDense P := by
  apply proposition8iii_of_rank_four_density hDensity P hP e
  rw [selected_row_count_paper_formula P hP e]
  exact hc

/-- The word "admitting" permits the small-row witness to be any
full-dimensional realization of the combinatorial type. -/
theorem proposition8iii_of_type_admitting_rows
    (hDensity : RankFourDensityInput) (P : ConvexPolytope 4)
    (hadmit : ∃ Q : ConvexPolytope 4, Q.IsFullDim ∧
      CombinatoriallyEquivalent P Q ∧
      ∃ (n : ℕ) (e : Fin n ≃ Q.vertices),
        sharedRelationCount Q (actualPolygonRelationRank Q e) ≤ 8) :
    RationallyDense P := by
  obtain ⟨Q, hQ, ⟨φPQ⟩, n, e, hc⟩ := hadmit
  have hdense := proposition8iii_of_rank_four_density hDensity Q hQ e hc
  intro R hPR
  obtain ⟨φPR⟩ := hPR
  exact hdense R ⟨φPQ.symm.trans φPR⟩

#print axioms selected_row_count_paper_formula
#print axioms proposition8iii_of_type_admitting_rows

end Papers.RationalityTen.GlobalEightRowsPaper
