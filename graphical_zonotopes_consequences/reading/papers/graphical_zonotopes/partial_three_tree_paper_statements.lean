module

public import Papers.GraphicalZonotopes.SmallCliqueDimension
public import Papers.GraphicalZonotopes.SeparatorPaperStatements

/-! # Finite-graph formulations of Corollaries 6.6--6.8

An ordering of the finite vertex set is chosen inside each statement. It is
used only by the geometric coordinate machinery and is not an extra graph
hypothesis. The support and spectrum statements use ordinary polytopal
Minkowski indecomposability, with its equivalence proved for actual weak
summands before invoking the core results.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical Pointwise
namespace GraphicalZonotopes

/-- Corollary 6.6 on every finite vertex type, with the actual direction
graph induced on its active coordinate set and no order assumption. -/
theorem partial_threeTree_support_classification_polytopal_finite
    {V : Type*} [Fintype V] :
    letI : LinearOrder V := Separator.finiteVertexOrder V;
    ∀ (G : SimpleGraph V), IsPartialThreeTree G → ∀ H : SimpleGraph V,
      (∃ Q : Set (V → ℝ), IsFinitePolytope Q ∧
        PolytopalMinkowskiIndecomposable Q ∧
        IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
        3 ≤ Module.finrank ℝ (vectorSpan ℝ Q) ∧ actualDirectionGraph Q = H) ↔
      ∃ U : Finset V, H = inducedOn G U ∧ ThreeTreeOn U H ∧ Admissible H := by
  letI : LinearOrder V := Separator.finiteVertexOrder V
  intro G hG H
  constructor
  · rintro ⟨Q,hQ,hi,hw,hd,ha⟩
    exact (partial_threeTree_support_classification hG H).mp
      ⟨Q,hQ,(weakSummand_indecomposable_iff_polytopal hQ hw).mpr hi,hw,hd,ha⟩
  · intro h
    obtain ⟨Q,hQ,hi,hw,hd,ha⟩ :=
      (partial_threeTree_support_classification hG H).mpr h
    exact ⟨Q,hQ,(weakSummand_indecomposable_iff_polytopal hQ hw).mp hi,hw,hd,ha⟩

/-- Corollary 6.8's complete piecewise maximum on arbitrary finite graphs:
`M(G)+2`, two, one, or zero according to tetrahedra, triangles, and edges. -/
theorem partial_threeTree_piecewise_maximum_finite {V : Type*} [Fintype V] :
    letI : LinearOrder V := Separator.finiteVertexOrder V;
    ∀ (G : SimpleGraph V), IsPartialThreeTree G →
      maximumIndecomposableDimension G = partialThreeTreeDimension G := by
  letI : LinearOrder V := Separator.finiteVertexOrder V
  exact fun G hG => partial_threeTree_piecewise_maximum hG

/-- Every positive dimension up to the sharp maximum occurs on every
partial three-tree, with an actual lattice polytope and the ordinary
polytopal indecomposability convention. -/
theorem partial_threeTree_full_dimension_spectrum_polytopal_finite
    {V : Type*} [Fintype V] :
    letI : LinearOrder V := Separator.finiteVertexOrder V;
    ∀ (G : SimpleGraph V), IsPartialThreeTree G → ∀ d : ℕ,
      1 ≤ d → d ≤ maximumIndecomposableDimension G →
      ∃ Q : Set (V → ℝ), LatticePolytope Q ∧
        PolytopalMinkowskiIndecomposable Q ∧
        IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
        Module.finrank ℝ (vectorSpan ℝ Q) = d := by
  letI : LinearOrder V := Separator.finiteVertexOrder V
  intro G hG d hd hmax
  obtain ⟨Q,hQ,hi,hw,hD⟩ := partial_threeTree_full_dimension_spectrum hG d hd hmax
  exact ⟨Q,hQ,(weakSummand_indecomposable_iff_polytopal hQ.finitePolytope hw).mp hi,hw,hD⟩

end GraphicalZonotopes
