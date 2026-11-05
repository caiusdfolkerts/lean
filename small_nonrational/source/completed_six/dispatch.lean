module
public import CompletedSix.Classification0
public import CompletedSix.Classification1
public import CompletedSix.Classification2
public import CompletedSix.Classification3


@[expose] public section

/-!
# Exhaustive dispatch of all 478 six-facet budgets

Each of the 477 rooted rows has a complete placement and classification
certificate. The single remaining row is sent to the independent induced
graph classification. Membership in the complete numerical catalogue is
checked here, so the dispatch has no omitted parameter range or local type.
-/

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.CompletedSix

open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting
open ChirotopeDensity SixFacetProfileRefinement SixBudgetEnumeration
open ActualResidualPartition ActualLeafTargetCoverage

/-- The unique row handled by the complete induced-graph search. -/
def graphRow : Row := RowData.graphRow

def certifiedRows : List Row :=
  Group00.rows ++ Group01.rows ++ Group02.rows ++ Group03.rows ++ Group04.rows ++ Group05.rows ++ Group06.rows ++ Group07.rows ++ Group08.rows ++ Group09.rows ++ Group10.rows ++ Group11.rows ++ Group12.rows ++ Group13.rows ++ Group14.rows ++ Group15.rows ++ Group16.rows ++ Group17.rows ++ Group18.rows ++ Group19.rows ++ Group20.rows ++ Group21.rows ++ Group22.rows ++ Group23.rows

theorem all_certifiedRows : ∀ B ∈ certifiedRows, Nonempty (RootedRowCertificate B) := by
  simp only [certifiedRows, List.forall_mem_append, and_assoc]
  exact ⟨Group00.certified, Group01.certified, Group02.certified, Group03.certified, Group04.certified, Group05.certified, Group06.certified, Group07.certified, Group08.certified, Group09.certified, Group10.certified, Group11.certified, Group12.certified, Group13.certified, Group14.certified, Group15.certified, Group16.certified, Group17.certified, Group18.certified, Group19.certified, Group20.certified, Group21.certified, Group22.certified, Group23.certified⟩

/-- Every row in the complete enumeration is handled by one of
the available rooted certificates or by the remaining graph row. -/
theorem catalogue_covered : ∀ B ∈ catalogue, B = graphRow ∨ B ∈ certifiedRows := by
  have hrows : certifiedRows = RowData.rows := rfl
  rw [hrows]
  exact RowData.catalogue_covered

/-- The only nonrooted input has one explicitly fixed numerical row. -/
def GraphRowCoverage : Prop :=
  ∀ (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (hnonsimple : ∀ v : P.vertices, ¬ IsSimpleVertex P v) (C : SixCase P),
    (countsOf P C.assignment.kind).toRow (actualAllSixFacetBudget P) = graphRow →
    HasTerminal P

/-- Complete six-facet coverage, conditional only on the separately checked
induced-graph row. The final assembly supplies that theorem explicitly. -/
theorem hasTerminal_of_graphRow (hgraph : GraphRowCoverage)
    (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (hnonsimple : ∀ v : P.vertices, ¬ IsSimpleVertex P v) (C : SixCase P) :
    HasTerminal P := by
  rcases catalogue_covered _ C.budget with hgraphRow | hrooted
  · exact hgraph P hP hnonsimple C hgraphRow
  · obtain ⟨D⟩ := all_certifiedRows _ hrooted
    exact D.hasTerminal P hP hnonsimple C rfl

#print axioms catalogue_covered
#print axioms hasTerminal_of_graphRow

end Papers.RationalityTen.CompletedSix
