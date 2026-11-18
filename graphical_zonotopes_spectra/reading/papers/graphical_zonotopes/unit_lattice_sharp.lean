module

public import Papers.GraphicalZonotopes.UnitLatticeClassification
public import Papers.GraphicalZonotopes.DoubledPrincipal

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open scoped Pointwise

/-- The entire statement of Theorem 9.5: the unrestricted classification and
its actual seven-dimensional lattice equality witness. -/
theorem unit_lattice_classification_sharp :
    Targets.UnitLatticeClassification ∧
      ∃ Q : Set ((Fin 4×Fin 2) → ℝ),LatticePolytope Q ∧
        MinkowskiIndecomposable Q ∧ Module.finrank ℝ (vectorSpan ℝ Q)=7 ∧
        IsMinkowskiSummand Q (graphicalZonotope (doubledPartGraph 4)) ∧
        actualDirectionGraph Q=doubledPartGraph 4 := by
  obtain ⟨Q,R,hQ,hR,hiQ,hiR,hdQ,hdR,he,hgraph,hgraphR,hrest⟩ :=
    DoubledParts.principal_boolean_phase_theorem 4 (by norm_num)
  exact ⟨unit_lattice_classification,Q,hQ,hiQ,
    by simpa only [FullDimension,Fintype.card_prod,Fintype.card_fin] using hdQ,
    ⟨R,hR.compact,hR.convex,hiR.1,he⟩,hgraph⟩

end GraphicalZonotopes
