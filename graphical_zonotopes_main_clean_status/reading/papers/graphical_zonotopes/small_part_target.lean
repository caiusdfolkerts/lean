module

public import Papers.GraphicalZonotopes.GraphDefinitions

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace Targets
open Finset
open scoped BigOperators Pointwise
attribute [local instance] Classical.propDecidable

/-- The graph-specific statement of Corollary9.11, for all sixteen part-size
patterns. Its additional all-dimensions consequence also uses9.8 and9.10. -/
def FourSmallPartsDecomposition : Prop :=
  ∀ a : Fin 4 → ℕ, (∀ i, a i = 1 ∨ a i = 2) →
    ∃ Q R : Set ((Σ i : Fin 4, Fin (a i)) → ℝ),
      LatticePolytope Q ∧ LatticePolytope R ∧
      MinkowskiIndecomposable Q ∧ MinkowskiIndecomposable R ∧
      FullDimension Q ∧ FullDimension R ∧ Q+R = graphicalZonotope (fourPartite a) ∧
      actualDirectionGraph Q = fourPartite a ∧ actualDirectionGraph R = fourPartite a ∧
      BooleanElemental Q ∧ BooleanElemental R

end Targets
end GraphicalZonotopes
