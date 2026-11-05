module

public import paper_verification.toric002

@[expose] public section

/-!
# Why the simplex scaling degrees are integral

Lemma 4.4 and its applications use integral fiber degrees. This separate
one-dimensional obstruction records that a version with arbitrary real
scales would be false. It is not a counterexample to the intended integral
statement or to any principal theorem, and does not replace their proofs.
-/

namespace ToricQuadratic

/-- With both real interval lengths `11/10`, the integral target `2` is
interior to the sum but cannot have an even integral first summand. -/
theorem nonintegral_simplex_scaling_parity_obstruction :
    (0 : ℝ) < 2 ∧ (2 : ℝ) < (11 : ℝ) / 10 + (11 : ℝ) / 10 ∧
      ¬ ∃ a b : ℤ,
        (0 : ℝ) ≤ a ∧ (a : ℝ) ≤ (11 : ℝ) / 10 ∧
        (0 : ℝ) ≤ b ∧ (b : ℝ) ≤ (11 : ℝ) / 10 ∧
        a + b = 2 ∧ Even a := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  rintro ⟨a, b, ha0, haup, _hb0, hbup, hsum, heven⟩
  have ha0Z : 0 ≤ a := by exact_mod_cast ha0
  have ha2R : (a : ℝ) < 2 := lt_of_le_of_lt haup (by norm_num)
  have ha2Z : a < 2 := by exact_mod_cast ha2R
  obtain ⟨r, hr⟩ := heven
  have ha : a = 0 := by omega
  have hb : b = 2 := by omega
  norm_num [hb] at hbup

end ToricQuadratic

#print axioms ToricQuadratic.nonintegral_simplex_scaling_parity_obstruction
