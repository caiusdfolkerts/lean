module

public import Papers.GraphicalZonotopes.AppendixPositiveMinima
public import Papers.GraphicalZonotopes.PathNewtonMinima
public import Papers.GraphicalZonotopes.NewtonPathIrreducibility

/-!
# The literal determinant has exactly the path Newton polytope

The positive determinant recurrence and the actual path base polytope have
the same attained minimum for every real coordinate weight. Separation of
closed convex sets therefore proves their equality. No generic Newton-product
formula, graphic-matroid representation, or spanning-tree enumeration is
assumed in this argument.

Together with the separately proved determinant stability, degree and
characteristic-independent irreducibility, this closes Proposition A.2.
-/

@[expose] public section

noncomputable section
open scoped Classical BigOperators

namespace GraphicalZonotopes.PathDeterminant

open PositivePolynomial NewtonGeometry PathNewtonMinima

/-- The ordinary real Newton polytope of the displayed determinant is the
literal lower base polytope of the paper's path set function, at every size.
In particular, the theorem includes the empty determinant and its point polytope. -/
theorem polynomial_newtonPolytope (m : ℕ) :
    newtonPolytope (polynomial ℝ m) = Path.polytope (m + 2) := by
  apply eq_of_same_linear_minima
    (newton_lattice (polynomial ℝ m)).convex
    (newton_lattice (polynomial ℝ m)).compact.isClosed
    (Path.polytope_lattice (m + 2)).convex
    (Path.polytope_compact (m + 2)).isClosed
  intro w
  refine ⟨minimum w (polynomial ℝ m), ?_, ?_⟩
  · exact minimum_isLeast_convexHull w (polynomial_ne_zero m)
  · rw [minimum_polynomial]
    change IsLeast ((fun x : Fin (m + 2) → ℝ => ∑ i, w i * x i) ''
      Path.polytope (m + 2)) (TropicalContinuant.first (extendedWeights m w) m)
    simpa only [extendedWeights_fin] using
      path_polytope_minimum m (extendedWeights m w)

/-- All assertions of Proposition A.2 for the determinant as defined by the
displayed matrix. The real Newton identity holds in characteristic zero;
absolute irreducibility is quantified independently over every field.
The paper uses `m = n - 2 ≥ 2`; this statement also includes `m = 1`. -/
theorem proposition_A_2 (K : Type*) [Field K] (m : ℕ) (hm : 0 < m) :
    newtonPolytope (polynomial ℝ m) = Path.polytope (m + 2) ∧
    (polynomial ℝ m).IsHomogeneous m ∧
    (polynomial ℝ m).totalDegree = m ∧
    IsRealStable (polynomial ℝ m) ∧
    Irreducible (MvPolynomial.map (algebraMap K (AlgebraicClosure K))
      (polynomial K m)) :=
  ⟨polynomial_newtonPolytope m, polynomial_homogeneous ℝ m,
    polynomial_totalDegree m, polynomial_realStable m,
    proposition_A_2_absoluteIrreducible K m hm⟩

end GraphicalZonotopes.PathDeterminant
