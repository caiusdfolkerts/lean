module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.Ring.Basic

@[expose] public section

set_option autoImplicit false

namespace Projection

/-- The algebraic form of quantitative AMGM. The positive number `s` is specified
by its defining square equation, so the argument works in every ordered field. -/
theorem quantitative_amgm_of_square {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] (x y M s : R)
    (hx : 0 < x) (hy : 0 < y) (hxM : x ≤ M) (hyM : y ≤ M)
    (hs : 0 < s) (hs2 : s ^ 2 = x * y) :
    (x - y) ^ 2 / (8 * M ^ 2) ≤ (x + y) / (2 * s) - 1 := by
  have hM : 0 < M := lt_of_lt_of_le hx hxM
  have hsM : s ≤ M := by
    apply (sq_le_sq₀ hs.le hM.le).mp
    rw [hs2, pow_two]
    exact mul_le_mul hxM hyM hy.le hM.le
  have h2s : 0 < 2 * s := mul_pos zero_lt_two hs
  have ht : 0 < x + y + 2 * s := by linarith
  have hd : 0 < 2 * s * (x + y + 2 * s) := mul_pos h2s ht
  have hbound : 2 * s * (x + y + 2 * s) ≤ 8 * M ^ 2 := by
    calc
      2 * s * (x + y + 2 * s) ≤ (2 * M) * (4 * M) :=
        mul_le_mul (by linarith) (by linarith) ht.le (by linarith)
      _ = 8 * M ^ 2 := by ring
  calc
    (x - y) ^ 2 / (8 * M ^ 2) ≤
        (x - y) ^ 2 / (2 * s * (x + y + 2 * s)) :=
      div_le_div_of_nonneg_left (sq_nonneg (x - y)) hd hbound
    _ = (x + y) / (2 * s) - 1 := by
      apply (div_eq_iff hd.ne').mpr
      symm
      calc
        ((x + y) / (2 * s) - 1) * (2 * s * (x + y + 2 * s)) =
            (((x + y) / (2 * s) - 1) * (2 * s)) * (x + y + 2 * s) :=
          (mul_assoc _ _ _).symm
        _ = (x + y - 2 * s) * (x + y + 2 * s) := by
          rw [sub_mul, div_mul_cancel₀ _ h2s.ne', one_mul]
        _ = (x - y) ^ 2 := by nlinarith [hs2]

end Projection
