module

public import Papers.GraphicalZonotopes.DiamondBookCapacity
public import Papers.GraphicalZonotopes.WeakSummandReduction
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

@[expose] public section
noncomputable section
namespace GraphicalZonotopes.DiamondBook
open Finset

theorem actual_summand_dimension_bound (k : ℕ) {Q : Set (Vertex k → ℝ)}
    (hQ : IsFinitePolytope Q) (hi : MinkowskiIndecomposable Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope (graph k))) :
    Module.finrank ℝ (vectorSpan ℝ Q)≤min (k+3) 9 := by
  apply le_min
  · have hb:=weak_summand_dimension_le hQ hi hw
    simp only [Fintype.card_fin] at hb
    omega
  · obtain ⟨z,hz,hzero|hext,hd⟩:=weak_summand_extreme_or_zero hQ hi hw
    · rw [hd,hzero,basePolytope_zero,vectorSpan_singleton,finrank_bot]
      norm_num
    · rw [hd]
      exact dimension_le_nine k z hext

/-- The upper half of the paper's complete dimension formula, with its
literal supremum over all actual indecomposable weak polytope summands. -/
theorem maximum_dimension_upper (k : ℕ) :
    maximumIndecomposableDimension (graph k)≤min (k+3) 9 := by
  apply csSup_le'
  rintro d ⟨Q,hQ,hi,hw,hd⟩
  rw [← hd]
  exact actual_summand_dimension_bound k hQ hi hw

end GraphicalZonotopes.DiamondBook
