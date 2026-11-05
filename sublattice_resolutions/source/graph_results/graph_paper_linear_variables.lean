module
public import graph_foundation.part009

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.GraphPaperLinearVariables -/
section

/-!
# The minimum-neighbor intervals in Section 6.1

The coefficient calculations use the intrinsic adjacency predicate for the
linear colon variables. This file identifies it with the manuscript's
minimum-neighbor cutoff, including the convention at an isolated vertex.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 20000
set_option synthInstance.maxHeartbeats 5000
noncomputable section

namespace FourPapers.Sublattice

open Classical
universe u
variable {N : ℕ}

/-- The vertices smaller than j which are adjacent to j. -/
def graphLowerNeighbors (G : SimpleGraph (Fin N)) (j : Fin N) : Finset (Fin N) :=
  Finset.univ.filter (fun i => i < j ∧ G.Adj i j)

/-- The paper's a(j): the least smaller neighbor, or j if none exists. -/
def graphNeighborCutoff (G : SimpleGraph (Fin N)) (j : Fin N) : Fin N :=
  if h : (graphLowerNeighbors G j).Nonempty then (graphLowerNeighbors G j).min' h else j

lemma graphNeighborCutoff_le_of_adj (G : SimpleGraph (Fin N))
    {i j : Fin N} (hij : i < j) (hG : G.Adj i j) :
    graphNeighborCutoff G j ≤ i := by
  have hi : i ∈ graphLowerNeighbors G j := by
    simp only [graphLowerNeighbors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hij, hG⟩
  have hn : (graphLowerNeighbors G j).Nonempty := ⟨i, hi⟩
  simp only [graphNeighborCutoff, dif_pos hn]
  exact Finset.min'_le _ _ hi

lemma graph_adj_of_cutoff_le (G : SimpleGraph (Fin N)) (hG : IntervalLabeling G)
    {i j : Fin N} (hij : i < j) (hcut : graphNeighborCutoff G j ≤ i) :
    G.Adj i j := by
  by_cases hn : (graphLowerNeighbors G j).Nonempty
  · have hm := Finset.min'_mem (graphLowerNeighbors G j) hn
    have hm' : (graphLowerNeighbors G j).min' hn < j ∧
        G.Adj ((graphLowerNeighbors G j).min' hn) j := by
      simpa only [graphLowerNeighbors, Finset.mem_filter, Finset.mem_univ, true_and] using hm
    simp only [graphNeighborCutoff, dif_pos hn] at hcut
    exact interval_adj_left hG hm'.2 hcut hij
  · simp only [graphNeighborCutoff, dif_neg hn] at hcut
    exact (not_lt_of_ge hcut hij).elim

/-- The displayed intervals defining L_ij in Section 6.1. -/
def graphPaperLinearVariables (G : SimpleGraph (Fin N))
    (a : FiniteTuple (GraphRows N)) : Finset (FiniteVariable.{u} (GraphRows N)) :=
  Finset.univ.filter (fun v =>
    (v.1 = 0 ∧ graphNeighborCutoff G (a 1) ≤ v.2.down ∧ v.2.down < a 0) ∨
    (v.1 = 1 ∧ a 0 < v.2.down ∧ v.2.down < a 1))

/-- The actual linear colon-variable set equals the paper's interval formula. -/
theorem graphLinearVariables_eq_paper (G : SimpleGraph (Fin N))
    (hG : IntervalLabeling G) {a : FiniteTuple (GraphRows N)}
    (ha : a ∈ graphEdgeLattice G) :
    graphLinearVariables.{u} G a = graphPaperLinearVariables G a := by
  have ha01 := ((mem_graphEdgeLattice G a).mp ha).1
  apply Finset.ext
  intro v
  simp only [graphLinearVariables, graphPaperLinearVariables, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro (⟨hr, hi, hadj⟩ | hy)
    · exact Or.inl ⟨hr, graphNeighborCutoff_le_of_adj G (hi.trans ha01) hadj, hi⟩
    · exact Or.inr hy
  · rintro (⟨hr, hcut, hi⟩ | hy)
    · exact Or.inl ⟨hr, hi, graph_adj_of_cutoff_le G hG (hi.trans ha01) hcut⟩
    · exact Or.inr hy

end FourPapers.Sublattice

end
end
end


end
