module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

@[expose] public section

/-! # The exact normalized Thomsen wall formula

These identities retain the sign correction from oppositely oriented edges.
They also justify translation by an integral arrangement vertex.
-/

noncomputable section
open scoped BigOperators
namespace Unimodular.CycleBounds

 theorem ceil_of_abs_lt_one {x : ℝ} (hxlo : -1 < x) (hxhi : x < 1) :
    ⌈x⌉ = if 0 < x then (1 : ℤ) else 0 := by
  by_cases hx : 0 < x
  · rw [if_pos hx]
    exact Int.ceil_eq_iff.mpr ⟨by simpa using hx, by simpa using hxhi.le⟩
  · rw [if_neg hx]
    exact Int.ceil_eq_iff.mpr ⟨by simpa using hxlo, by simpa using le_of_not_gt hx⟩

/-- An oriented edge contributes a decrease, minus one precisely when it is
oppositely oriented and has nonzero pairing. -/
theorem signed_ceil_eq_descent {x : ℝ} (hxlo : -1 < x) (hxhi : x < 1)
    (ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
    ε * ⌈x⌉ = (if 0 < (ε : ℝ) * x then (1 : ℤ) else 0) -
      (if ε = -1 ∧ x ≠ 0 then 1 else 0) := by
  rw [ceil_of_abs_lt_one hxlo hxhi]
  rcases hε with rfl | rfl
  · simp
  · rcases lt_trichotomy x 0 with hx | rfl | hx
    · have hn : ¬0 < x := not_lt.mpr hx.le
      have hp : 0 < -x := neg_pos.mpr hx
      simp [hn, hp, hx.ne]
    · simp
    · have hn : ¬0 < -x := not_lt.mpr (neg_nonpos.mpr hx.le)
      simp [hx, hn, hx.ne']

/-- The displayed intersection formula of Proposition 6.8, for every finite
oriented circuit support and every normalized real pairing. -/
theorem wall_sum_eq_descents_sub_reverse {E : Type*} [Fintype E]
    (x : E → ℝ) (ε : E → ℤ)
    (hxlo : ∀ e, -1 < x e) (hxhi : ∀ e, x e < 1)
    (hε : ∀ e, ε e = 1 ∨ ε e = -1) :
    (∑ e, ε e * ⌈x e⌉) =
      (∑ e, if 0 < (ε e : ℝ) * x e then (1 : ℤ) else 0) -
      (∑ e, if ε e = -1 ∧ x e ≠ 0 then 1 else 0) := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun e _ ↦ signed_ceil_eq_descent (hxlo e) (hxhi e) (ε e) (hε e))

theorem wall_sum_le_descents {E : Type*} [Fintype E]
    (x : E → ℝ) (ε : E → ℤ)
    (hxlo : ∀ e, -1 < x e) (hxhi : ∀ e, x e < 1)
    (hε : ∀ e, ε e = 1 ∨ ε e = -1) :
    (∑ e, ε e * ⌈x e⌉) ≤
      ∑ e, if 0 < (ε e : ℝ) * x e then (1 : ℤ) else 0 := by
  rw [wall_sum_eq_descents_sub_reverse x ε hxlo hxhi hε]
  apply sub_le_self
  exact Finset.sum_nonneg (fun e _ ↦ by split_ifs <;> norm_num)

/-- Integral translation preserves a circuit wall value, because the integral
translation pairings satisfy the same circuit relation. -/
theorem wall_sum_integral_translation {E : Type*} [Fintype E]
    (x : E → ℝ) (ε m : E → ℤ) (hm : ∑ e, ε e * m e = 0) :
    (∑ e, ε e * ⌈x e - (m e : ℝ)⌉) = ∑ e, ε e * ⌈x e⌉ := by
  simp_rw [Int.ceil_sub_intCast, mul_sub]
  rw [Finset.sum_sub_distrib, hm, sub_zero]

#print axioms wall_sum_eq_descents_sub_reverse
#print axioms wall_sum_integral_translation
end Unimodular.CycleBounds
