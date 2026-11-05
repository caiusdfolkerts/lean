module

public import Papers.GlobalEightRowsPaper
public import Consolidated.RankFourTheorems

@[expose] public section
noncomputable section
set_option autoImplicit false

open LeanEval.Geometry.PlatonicClassification
open Papers.Polytopes Papers.PolytopeRelationBudget Papers.PolytopeMasterBudget

namespace Papers.RationalityTen.ChirotopeDensity

/-- Proposition 8(iii): the full global density conclusion from eight
selected relation rows in one realization, with all inputs discharged. -/
theorem proposition8iii_global {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (hc : Fintype.card (ActualSharedRowIndex P e) ≤ 8) : RationallyDense P :=
  actual_global_eight_shared_relations_of_rank_four_density
    MatroidChecked.VerifiedRankFour.lemma11_rank_four_dense P hP e hc

/-- The numerical form uses exactly the paper's selected-row count. -/
theorem proposition8iii {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (hc : sharedRelationCount P (actualPolygonRelationRank P e) ≤ 8) :
    RationallyDense P :=
  GlobalEightRowsPaper.proposition8iii_of_rank_four_density
    MatroidChecked.VerifiedRankFour.lemma11_rank_four_dense P hP e hc

/-- The full combinatorial-type formulation: one realization witnesses the
row budget, while rational density holds near every realization. -/
theorem proposition8iii_admitting_rows (P : ConvexPolytope 4)
    (hadmit : ∃ Q : ConvexPolytope 4, Q.IsFullDim ∧
      CombinatoriallyEquivalent P Q ∧
      ∃ (n : ℕ) (e : Fin n ≃ Q.vertices),
        sharedRelationCount Q (actualPolygonRelationRank Q e) ≤ 8) :
    RationallyDense P :=
  GlobalEightRowsPaper.proposition8iii_of_type_admitting_rows
    MatroidChecked.VerifiedRankFour.lemma11_rank_four_dense P hadmit

#print axioms proposition8iii_global
#print axioms proposition8iii
#print axioms proposition8iii_admitting_rows

end Papers.RationalityTen.ChirotopeDensity
