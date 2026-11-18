module

public import Papers.GraphicalZonotopes.DiamondBookUpperBound
public import Papers.GraphicalZonotopes.DiamondBookSmallDimension
public import Papers.GraphicalZonotopes.DiamondBookLargeDimension

@[expose] public section
noncomputable section
namespace GraphicalZonotopes.DiamondBook

/-- The unbounded maximum-dimension formula for every positive private-part
size. All lower witnesses and the upper supremum bound refer to actual
indecomposable Minkowski summands. -/
theorem maximum_dimension (k : ℕ) (hk : 1≤k) :
    maximumIndecomposableDimension (graph k)=min (k+3) 9 := by
  apply le_antisymm (maximum_dimension_upper k)
  by_cases hs:k≤5
  · exact (min_le_left _ _).trans (small_dimension_lower k hk hs)
  · exact (min_le_right _ _).trans (large_dimension_lower k (by omega))

end GraphicalZonotopes.DiamondBook
