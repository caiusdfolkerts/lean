module

public import Papers.GraphicalZonotopes.TreeJoinDimension
public import Papers.GraphicalZonotopes.HamiltonianThreeTree
public import Papers.GraphicalZonotopes.BookPrincipal

/-! # Corollary 6.9

The three clauses are `three_hub_book_maximum`,
`TreeJoin.paper_corollary_6_9_tree_join`, and
`hamiltonian_threeTree_lattice_polytopal_finite`. The latter two include
lattice attainment and ordinary polytopal Minkowski indecomposability.
-/

@[expose] public section
noncomputable section
namespace GraphicalZonotopes

theorem three_hub_book_maximum (k : ℕ) (hk : 1≤k) :
    maximumIndecomposableDimension (cliqueBook 3 k)=min (k+2) 5 := by
  have h := (clique_book_classification 3 k (by decide) hk).1
  have hc : cliqueCapacity 3=3 := by decide
  rw [hc] at h
  have hn : 3+k-1=k+2 := by omega
  simpa only [hn] using h

end GraphicalZonotopes
