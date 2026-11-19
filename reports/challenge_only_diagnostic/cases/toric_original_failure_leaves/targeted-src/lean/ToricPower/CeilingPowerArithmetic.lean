module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic

/-!
# Exact ceiling arithmetic for the normalized dual Cartier labels

The minus-one boundary correction is essential on the integral walls.
The formulas below hold for all real points, all integral translations,
and every positive integer power, including points on those walls.
-/

@[expose] public section

namespace ToricPower

/-- The normalized dual coefficient commutes exactly with positive power
division. This includes all equality walls. -/
theorem normalizedDualCeiling_ediv (x : ℝ) (a : ℤ) (ell : ℕ) (positive : 0 < ell) :
    (⌈x⌉ - 1 + a) / (ell : ℤ) = ⌈(x + a) / (ell : ℝ)⌉ - 1 := by
  let q := (⌈x⌉ - 1 + a) / (ell : ℤ)
  have hℤ : (0 : ℤ) < ell := by exact_mod_cast positive
  have hℝ : (0 : ℝ) < ell := by exact_mod_cast positive
  have bounds : q * (ell : ℤ) ≤ ⌈x⌉ - 1 + a ∧
      ⌈x⌉ - 1 + a < q * (ell : ℤ) + ell :=
    (Int.ediv_eq_iff_of_pos hℤ).mp rfl
  have lower : (q : ℝ) * ell ≤ (⌈x⌉ : ℝ) - 1 + a := by exact_mod_cast bounds.1
  have upperInt : ⌈x⌉ + a ≤ q * (ell : ℤ) + ell := by omega
  have upper : (⌈x⌉ : ℝ) + a ≤ (q : ℝ) * ell + ell := by exact_mod_cast upperInt
  have ceiling : ⌈(x + a) / (ell : ℝ)⌉ = q + 1 := by
    apply Int.ceil_eq_iff.mpr
    constructor
    · rw [Int.cast_add, Int.cast_one]
      have hx := Int.ceil_lt_add_one x
      have inequality : (q : ℝ) < (x + a) / (ell : ℝ) := by
        apply (lt_div_iff₀ hℝ).mpr
        linarith
      linarith
    · rw [Int.cast_add, Int.cast_one]
      apply (div_le_iff₀ hℝ).mpr
      have hx := Int.le_ceil x
      nlinarith
  change q = _
  omega

/-- The ceiling of the scaled translate depends only on the original
ceiling, hence is constant throughout each actual arrangement cell. -/
theorem ceil_scaled_translate (x : ℝ) (a : ℤ) (ell : ℕ) (positive : 0 < ell) :
    ⌈(x + a) / (ell : ℝ)⌉ = (⌈x⌉ - 1 + a) / (ell : ℤ) + 1 := by
  have h := normalizedDualCeiling_ediv x a ell positive
  omega

/-- The precise wall condition after scaling: the original value must
already be integral, and its translated integer must be divisible by the power. -/
theorem scaled_translate_is_integer_iff (x : ℝ) (a : ℤ) (ell : ℕ) (positive : 0 < ell) :
    (∃ z : ℤ, (x + a) / (ell : ℝ) = z) ↔
      ∃ z : ℤ, x = z ∧ (ell : ℤ) ∣ z + a := by
  have hℝ : (ell : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt positive)
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨(ell : ℤ)*z-a, ?_, ?_⟩
    · rw [Int.cast_sub, Int.cast_mul, Int.cast_natCast]
      have equality := (div_eq_iff hℝ).mp hz
      linarith
    · refine ⟨z, ?_⟩
      ring
  · rintro ⟨z, rfl, w, hw⟩
    refine ⟨w, ?_⟩
    rw [← Int.cast_add, hw, Int.cast_mul, Int.cast_natCast]
    exact mul_div_cancel_left₀ (w : ℝ) hℝ

end ToricPower

end
