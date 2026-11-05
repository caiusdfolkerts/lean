module

public import Mathlib.Analysis.Real.Sqrt
public import Projection.AMGMAlgebra

@[expose] public section

set_option autoImplicit false

namespace Projection

/-- A quantitative arithmetic--geometric mean inequality on a bounded positive interval.
The constant depends only on the common upper bound; no positive lower bound on either
variable is required. -/
theorem quantitative_amgm (x y M : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hxM : x ≤ M) (hyM : y ≤ M) :
    (x - y) ^ 2 / (8 * M ^ 2) ≤
      (x + y) / (2 * Real.sqrt (x * y)) - 1 := by
  exact quantitative_amgm_of_square x y M (Real.sqrt (x * y)) hx hy hxM hyM
    (Real.sqrt_pos.mpr (mul_pos hx hy)) (Real.sq_sqrt (mul_nonneg hx.le hy.le))

end Projection
