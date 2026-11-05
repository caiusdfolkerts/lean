module

public import Papers.GraphicalZonotopes.BookLatticeAttainment
public import Papers.GraphicalZonotopes.BookDimensionUpper
public import Papers.GraphicalZonotopes.PrincipalTargets
public import Papers.GraphicalZonotopes.PolytopalDimension

/-! # Exact clique-book classification, with lattice attainment -/

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open scoped Pointwise

/-- Theorem 7.1, preserving every hub count, every branch count, the full
polytope maximum, the capacity equivalence, and the stated integral dilation. -/
theorem clique_book_classification : Targets.CliqueBookClassification := by
  intro s k hs hk
  have hatt := book_lattice_attainment s k hs hk
  refine ⟨le_antisymm (BookDimension.maximum_dimension_upper s k hs)
    hatt.dimension_le_maximum,?_,hatt.polytope⟩
  constructor
  · exact BookDimension.capacity_necessary s k hs
  · intro hcap
    have hfull := book_lattice_full s k hs hk hcap
    apply LatticeExtremeAt.supports_full
    simpa only [Fintype.card_sum,Fintype.card_fin] using hfull

/-- The literal polytopal version of Theorem 7.1. The equivalence of the
dimension invariant and the supporting predicate is proved, not assumed. -/
theorem clique_book_classification_polytopal (s k : ℕ) (hs : 2≤s) (hk : 1≤k) :
    (sSup {d : ℕ | ∃ Q : Set ((Fin s⊕Fin k) → ℝ),IsFinitePolytope Q ∧
      PolytopalMinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope (cliqueBook s k)) ∧
      Module.finrank ℝ (vectorSpan ℝ Q)=d}) =
        min (s+k-1) (s+cliqueCapacity s-1) ∧
    ((∃ Q : Set ((Fin s⊕Fin k) → ℝ),IsFinitePolytope Q ∧
      PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope (cliqueBook s k))) ↔
        k≤cliqueCapacity s) ∧
    ∃ Q : Set ((Fin s⊕Fin k) → ℝ),LatticePolytope Q ∧
      PolytopalMinkowskiIndecomposable Q ∧
      Module.finrank ℝ (vectorSpan ℝ Q)=min (s+k-1) (s+cliqueCapacity s-1) ∧
      IsMinkowskiSummand Q ((((s-1)*min k (cliqueCapacity s) : ℕ) : ℝ) •
        graphicalZonotope (cliqueBook s k)) := by
  obtain ⟨hd,hfull,Q,hQ,hi,hDim,hSum⟩ := clique_book_classification s k hs hk
  refine ⟨?_,?_,Q,hQ,?_,hDim,hSum⟩
  · rw [←maximumIndecomposableDimension_eq_polytopal_supremum]
    exact hd
  · rw [←supportsFullIndecomposable_iff_polytopal_weak]
    exact hfull
  · exact ⟨hi.1,fun P R hP hR he =>
      hi.2 P R hP.compact hR.compact hP.convex hR.convex he⟩

end GraphicalZonotopes
