module

public import Papers.GraphicalZonotopes.GraphModels
public import Papers.GraphicalZonotopes.ZonotopeEdges

/-! # Uniqueness of standard root direction lines

This elementary geometric fact is independent of the sharp dimension bounds
and their path-family attainment construction.
-/

@[expose] public section
noncomputable section
namespace GraphicalZonotopes

/-- Distinct unordered pairs represent distinct unoriented root directions.
Together with all-edge coverage, this identifies the graph edge count with
the number of geometric edge directions. -/
theorem root_parallel_pair_eq {V : Type*} [Fintype V] [DecidableEq V]
    {u v a b : V} (huv : u ≠ v) (hab : a ≠ b) {c d : ℝ} (hc : c ≠ 0)
    (h : c • (basisVector u-basisVector v)=d • (basisVector a-basisVector b)) :
    ({u,v} : Finset V)={a,b} := by
  classical
  have hedge : (cliqueGraph ({a,b} : Finset V)).Adj a b :=
    ⟨hab,by simp,by simp⟩
  have he := adjacency_of_root_parallel (cliqueGraph ({a,b} : Finset V)) huv hedge hc h
  apply Finset.eq_of_subset_of_card_le
  · intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact he.2.1
    · have hwv := Finset.mem_singleton.mp hw
      simpa only [hwv] using he.2.2
  · simpa only [Finset.card_pair huv,Finset.card_pair hab] using (Nat.le_refl 2)

end GraphicalZonotopes
