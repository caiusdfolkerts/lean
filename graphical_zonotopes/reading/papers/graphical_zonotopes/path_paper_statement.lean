module

public import Papers.GraphicalZonotopes.PathPrincipal

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace Path
open scoped BigOperators

/-- Equation (3.1) with subtraction in the real numbers, exactly as in the
paper. The lower bound on n justifies the natural-subtraction cast used by
the uniform finite-window definition. -/
theorem polytope_defining_equations_real {n : ℕ} (hn : 4 ≤ n) :
    polytope n = {x : Fin n → ℝ | subsetSum x Finset.univ = (n : ℝ)-2 ∧
      ∀ S, setFunction n S ≤ subsetSum x S} := by
  simpa only [Nat.cast_sub (show 2 ≤ n by omega), Nat.cast_ofNat] using
    polytope_defining_equations n

/-- The same literal statement in ordinary finite-sum notation. -/
theorem polytope_defining_equations_sums {n : ℕ} (hn : 4 ≤ n) :
    polytope n = {x : Fin n → ℝ | (∑ i, x i) = (n : ℝ)-2 ∧
      ∀ S : Finset (Fin n), setFunction n S ≤ ∑ i ∈ S, x i} := by
  simpa only [subsetSum] using polytope_defining_equations_real hn

end Path
end GraphicalZonotopes
