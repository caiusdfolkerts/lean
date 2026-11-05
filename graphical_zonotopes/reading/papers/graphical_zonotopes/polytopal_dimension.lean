module

public import Papers.GraphicalZonotopes.PolytopalWeakSummands

/-! # Dimension invariants with the paper's polytopal convention -/

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The dimension supremum is unchanged when indecomposability is defined
using only finite polytopal Minkowski decompositions, as in the paper. -/
theorem maximumIndecomposableDimension_eq_polytopal_supremum (G : SimpleGraph V) :
    maximumIndecomposableDimension G =
      sSup {d : ℕ | ∃ Q : Set (V → ℝ),IsFinitePolytope Q ∧
        PolytopalMinkowskiIndecomposable Q ∧
        IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
        Module.finrank ℝ (vectorSpan ℝ Q)=d} := by
  unfold maximumIndecomposableDimension
  congr 1
  ext d
  constructor
  · rintro ⟨Q,hQ,hi,hw,hd⟩
    exact ⟨Q,hQ,(weakSummand_indecomposable_iff_polytopal hQ hw).mp hi,hw,hd⟩
  · rintro ⟨Q,hQ,hi,hw,hd⟩
    exact ⟨Q,hQ,(weakSummand_indecomposable_iff_polytopal hQ hw).mpr hi,hw,hd⟩

theorem supportsFullIndecomposable_iff_polytopal_weak (G : SimpleGraph V) :
    SupportsFullIndecomposable G ↔
      ∃ Q : Set (V → ℝ),IsFinitePolytope Q ∧
        PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
        IsWeakMinkowskiSummand Q (graphicalZonotope G) := by
  constructor
  · rintro ⟨Q,hQ,hi,hd,hw⟩
    exact ⟨Q,hQ,(weakSummand_indecomposable_iff_polytopal hQ hw).mp hi,hd,hw⟩
  · rintro ⟨Q,hQ,hi,hd,hw⟩
    exact ⟨Q,hQ,(weakSummand_indecomposable_iff_polytopal hQ hw).mpr hi,hd,hw⟩

end GraphicalZonotopes
