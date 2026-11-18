module

public import Papers.GraphicalZonotopes.SaturatedBookPrincipal
public import Papers.GraphicalZonotopes.GeometricDirectionCount

/-! # The saturated-book minimum as a count of geometric lines

Theorem 7.12 is stated here using the actual real lines spanned by exposed
edges. The counting equivalence and finiteness theorem in
`GeometricDirectionCount` identify this formulation with the root-pair
formulation proved in `SaturatedBookPrincipal`.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.SaturatedDirections
open Finset
attribute [local instance] Classical.propDecidable

/-- Theorem 7.12 with ordinary polytopal indecomposability and the literal
cardinality of geometric, unoriented edge-direction lines. -/
theorem paper_theorem_7_12_geometric :
    ∀ s : ℕ,2 ≤ s →
      (∀ Q : Set ((Fin s ⊕ Fin (cliqueCapacity s)) → ℝ),
        IsFinitePolytope Q → PolytopalMinkowskiIndecomposable Q → FullDimension Q →
        IsWeakMinkowskiSummand Q (graphicalZonotope (cliqueBook s (cliqueCapacity s))) →
        s.choose 2 + s*saturatedHubNeighbors s ≤ (actualEdgeDirectionLines Q).ncard ∧
        (3 ≤ s → ∀ i j : Fin s,i ≠ j → ActualRootEdge Q (Sum.inl i) (Sum.inl j)) ∧
        ∀ i : Fin s,saturatedHubNeighbors s ≤
          (univ.filter (fun j : Fin (cliqueCapacity s) =>
            ActualRootEdge Q (Sum.inl i) (Sum.inr j))).card) ∧
      ∃ Q : Set ((Fin s ⊕ Fin (cliqueCapacity s)) → ℝ),
        LatticePolytope Q ∧ PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
        IsWeakMinkowskiSummand Q (graphicalZonotope (cliqueBook s (cliqueCapacity s))) ∧
        (actualEdgeDirectionLines Q).ncard = s.choose 2 + s*saturatedHubNeighbors s ∧
        ∀ i : Fin s,(univ.filter (fun j : Fin (cliqueCapacity s) =>
          ActualRootEdge Q (Sum.inl i) (Sum.inr j))).card = saturatedHubNeighbors s := by
  intro s hs
  obtain ⟨hlower,Q,hL,hI,hD,hW,hE,hS⟩ := paper_theorem_7_12_polytopal s hs
  refine ⟨?_,Q,hL,hI,hD,hW,?_,hS⟩
  · intro Q hQ hi hd hw
    obtain ⟨hc,hh,hn⟩ := hlower Q hQ hi hd hw
    refine ⟨?_,hh,hn⟩
    rw [←directionCount_eq_geometric_line_count hQ hw]
    exact hc
  · rw [←directionCount_eq_geometric_line_count hL.finitePolytope hW]
    exact hE

end GraphicalZonotopes.SaturatedDirections
