module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Order.Interval.Finset.Nat

/-!
# A finite Hilbert-series formula and its exact coefficient meaning

This elementary equivalence retains the constant coefficient, every positive
coefficient through the specified cutoff, and every coefficient beyond it.
It allows a graded dimension calculation to be restated as the literal
finite power-series identity used in the paper.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.FiniteHilbertSeries

open scoped BigOperators PowerSeries

def expression (a : ℕ → ℕ) (d : ℕ) : ℕ⟦X⟧ :=
  1 + ∑ s ∈ Finset.Icc 1 d, PowerSeries.C (a s) * PowerSeries.X ^ s

theorem coeff_expression (a : ℕ → ℕ) (d s : ℕ) :
    PowerSeries.coeff s (expression a d) =
      (if s = 0 then 1 else 0) + (if 1 ≤ s ∧ s ≤ d then a s else 0) := by
  simp only [expression, map_add, map_sum, PowerSeries.coeff_one,
    PowerSeries.coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_Icc]

/-- Equality to the displayed finite series is equivalent to all three
parts of the coefficient statement; no degree is omitted. -/
theorem mk_eq_expression_iff (h a : ℕ → ℕ) (d : ℕ) :
    PowerSeries.mk h = expression a d ↔
      h 0 = 1 ∧
      (∀ s, 1 ≤ s → s ≤ d → h s = a s) ∧
      (∀ s, d < s → h s = 0) := by
  constructor
  · intro heq
    have hc (s : ℕ) : h s = PowerSeries.coeff s (expression a d) := by
      rw [← heq, PowerSeries.coeff_mk]
    refine ⟨?_, ?_, ?_⟩
    · simpa [coeff_expression] using hc 0
    · intro s hs hd
      have hs0 : s ≠ 0 := by omega
      simpa [coeff_expression, hs0, hs, hd] using hc s
    · intro s hd
      have hs0 : s ≠ 0 := by omega
      have hs : ¬ s ≤ d := Nat.not_le.mpr hd
      simpa [coeff_expression, hs0, hs] using hc s
  · rintro ⟨h0, hlo, hhi⟩
    apply PowerSeries.ext
    intro s
    rw [PowerSeries.coeff_mk, coeff_expression]
    by_cases hs0 : s = 0
    · subst s
      simpa using h0
    · have hs : 1 ≤ s := by omega
      by_cases hd : s ≤ d
      · simpa [hs0, hs, hd] using hlo s hs hd
      · simpa [hs0, hd] using hhi s (Nat.lt_of_not_ge hd)

end PaperVerification.FiniteHilbertSeries
