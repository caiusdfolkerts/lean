module

public import Papers.GraphicalZonotopes.SpanningTetrahedra
public import Papers.GraphicalZonotopes.Translation

@[expose] public section
noncomputable section
namespace GraphicalZonotopes

/-- Theorem4.1, with all translations and no clique-number restriction.
The matching path-cube attainment is the separate principal family theorem. -/
theorem direction_bounds (n : ℕ) (hn : 4 ≤ n) (Q : Set (Fin n → ℝ))
    (hQ : IsGeneralizedPermutahedron Q) (hi : MinkowskiIndecomposable Q)
    (hd : FullDimension Q) :
    3*n-6 ≤ directionCount Q ∧ min (n-1) 6 ≤ maximumDirectionDegree Q ∧
    (directionCount Q=3*n-6 → IsThreeTree (actualDirectionGraph Q)) := by
  obtain ⟨z,hzn,hzs,rfl⟩ := hQ
  have hdim : Module.finrank ℝ (vectorSpan ℝ (basePolytope (normalize z)))=n-1 := by
    rw [vectorSpan_basePolytope_normalize]
    simpa [FullDimension] using hd
  have hne : normalize z ≠ 0 := by
    intro hz0
    rw [hz0,basePolytope_zero] at hdim
    have hspan : vectorSpan ℝ ({0} : Set (Fin n → ℝ)) =
        (⊥ : Submodule ℝ (Fin n → ℝ)) :=
      _root_.vectorSpan_singleton ℝ (0 : Fin n → ℝ)
    rw [hspan, _root_.finrank_bot] at hdim
    omega
  have hext := hi.extremeSupermodular_normalize hzn hzs hne
  obtain ⟨hedges,heq⟩ := hext.direction_count_bound hn hdim
  have hdegree := hext.maximum_degree_bound hn hdim
  have hgraph := actualDirectionGraph_normalize z
  have hecount : directionCount (basePolytope (normalize z))=directionCount (basePolytope z) := by
    unfold directionCount
    rw [hgraph]
  have hedegree : maximumDirectionDegree (basePolytope (normalize z))=
      maximumDirectionDegree (basePolytope z) := by
    unfold maximumDirectionDegree
    rw [hgraph]
  rw [hecount] at hedges heq
  rw [hedegree] at hdegree
  exact ⟨hedges,hdegree,fun h => by simpa only [hgraph] using heq h⟩

/-- The same theorem with the traditional polytope-summand definition in
its hypothesis. This prevents the stronger-looking compact-convex wording
from concealing a restriction on the paper's class of indecomposable polytopes. -/
theorem direction_bounds_polytopal (n : ℕ) (hn : 4≤n) (Q : Set (Fin n → ℝ))
    (hQ : IsGeneralizedPermutahedron Q) (hi : PolytopalMinkowskiIndecomposable Q)
    (hd : FullDimension Q) :
    3*n-6≤directionCount Q ∧ min (n-1) 6≤maximumDirectionDegree Q ∧
    (directionCount Q=3*n-6 → IsThreeTree (actualDirectionGraph Q)) :=
  direction_bounds n hn Q hQ ((minkowskiIndecomposable_iff_polytopal hQ).mpr hi) hd

end GraphicalZonotopes
