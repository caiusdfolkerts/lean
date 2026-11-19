module

public import Papers.GraphicalZonotopes.AppendixPositiveContinuant
public import Papers.GraphicalZonotopes.PositivePolynomialMinima
public import Papers.GraphicalZonotopes.TropicalContinuant

/-!
# Support minima of the positive determinant recurrence

Both components of the positive recurrence have nonnegative coefficients
and are nonzero. Therefore their support minima obey the exact tropical
recurrence, with no cancellation premise left implicit.
-/

@[expose] public section
noncomputable section

namespace GraphicalZonotopes.PathDeterminant

open PositivePolynomial

variable {σ : Type*}

/-- Positivity and nonzeroness are propagated together at every prefix. -/
theorem positivePair_good (t : ℕ → MvPolynomial σ ℝ)
    (ht : ∀ j, Nonnegative (t j)) (ht0 : ∀ j, t j ≠ 0) (k : ℕ) :
    (Nonnegative (positivePair t k).1 ∧ (positivePair t k).1 ≠ 0) ∧
      (Nonnegative (positivePair t k).2 ∧ (positivePair t k).2 ≠ 0) := by
  induction k with
  | zero => exact ⟨⟨nonnegative_one, one_ne_zero⟩, ⟨nonnegative_one, one_ne_zero⟩⟩
  | succ k ih =>
      have hleft := nonnegative_mul (ht (k + 2)) ih.1.1
      have hright := nonnegative_mul (ht k) ih.2.1
      have hlast := nonnegative_mul (ht (k + 1)) ih.1.1
      have he : Nonnegative (positivePair t (k + 1)).2 := by
        rw [positivePair_snd_succ]
        exact nonnegative_add hleft hright
      have he0 : (positivePair t (k + 1)).2 ≠ 0 := by
        rw [positivePair_snd_succ]
        exact add_ne_zero_of_nonnegative hleft hright (mul_ne_zero (ht0 (k + 2)) ih.1.2)
      have hd : Nonnegative (positivePair t (k + 1)).1 := by
        rw [positivePair_fst_succ]
        exact nonnegative_add he hlast
      have hd0 : (positivePair t (k + 1)).1 ≠ 0 := by
        rw [positivePair_fst_succ]
        exact add_ne_zero_of_nonnegative he hlast he0
      exact ⟨⟨hd, hd0⟩, ⟨he, he0⟩⟩

/-- For arbitrary real weights, the two support minima satisfy exactly the
positive pair's tropical recurrence. The variables can repeat or be replaced
by any nonzero polynomial with nonnegative coefficients. -/
theorem positivePair_minimum (t : ℕ → MvPolynomial σ ℝ) (w : σ → ℝ)
    (ht : ∀ j, Nonnegative (t j)) (ht0 : ∀ j, t j ≠ 0) (m : ℕ) :
    (minimum w (positivePair t m).1, minimum w (positivePair t m).2) =
      TropicalContinuant.pair (fun j => minimum w (t j)) m := by
  refine TropicalContinuant.pair_eq_of_recurrences
    (fun j => minimum w (t j))
    (fun k => minimum w (positivePair t k).1)
    (fun k => minimum w (positivePair t k).2) ?_ ?_ ?_ ?_ m
  · simp
  · simp
  · intro k
    have h := positivePair_good t ht ht0 k
    rw [positivePair_snd_succ,
      minimum_add w (nonnegative_mul (ht (k + 2)) h.1.1)
        (nonnegative_mul (ht k) h.2.1)
        (mul_ne_zero (ht0 (k + 2)) h.1.2) (mul_ne_zero (ht0 k) h.2.2),
      minimum_mul w (ht (k + 2)) h.1.1 (ht0 (k + 2)) h.1.2,
      minimum_mul w (ht k) h.2.1 (ht0 k) h.2.2]
  · intro k
    have h := positivePair_good t ht ht0 k
    have hnext := positivePair_good t ht ht0 (k + 1)
    rw [positivePair_fst_succ,
      minimum_add w hnext.2.1 (nonnegative_mul (ht (k + 1)) h.1.1)
        hnext.2.2 (mul_ne_zero (ht0 (k + 1)) h.1.2),
      minimum_mul w (ht (k + 1)) h.1.1 (ht0 (k + 1)) h.1.2]

/-- Extend finitely many coordinate weights periodically. Every index used
by the determinant prefix lies in the original range. -/
def extendedWeights (m : ℕ) (w : Fin (m + 2) → ℝ) (j : ℕ) : ℝ :=
  w ⟨j % (m + 2), Nat.mod_lt _ (by omega)⟩

@[simp] theorem extendedWeights_fin (m : ℕ) (w : Fin (m + 2) → ℝ)
    (j : Fin (m + 2)) : extendedWeights m w j.val = w j := by
  unfold extendedWeights
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt j.isLt)

theorem variableSequence_nonnegative (m j : ℕ) :
    Nonnegative (variableSequence ℝ m j) :=
  nonnegative_X _

theorem variableSequence_ne_zero (m j : ℕ) : variableSequence ℝ m j ≠ 0 :=
  MvPolynomial.X_ne_zero _

@[simp] theorem minimum_variableSequence (m : ℕ) (w : Fin (m + 2) → ℝ) (j : ℕ) :
    minimum w (variableSequence ℝ m j) = extendedWeights m w j := by
  exact minimum_X w _

/-- Nonnegative coefficients are proved for the actual determinant. -/
theorem polynomial_nonnegative (m : ℕ) : Nonnegative (polynomial ℝ m) := by
  rw [← positivePair_polynomial]
  exact (positivePair_good (variableSequence ℝ m)
    (variableSequence_nonnegative m) (variableSequence_ne_zero m) m).1.1

/-- Every real linear support minimum of the literal determinant is the
first component of the tropical recurrence. -/
theorem minimum_polynomial (m : ℕ) (w : Fin (m + 2) → ℝ) :
    minimum w (polynomial ℝ m) = TropicalContinuant.first (extendedWeights m w) m := by
  have h := positivePair_minimum (variableSequence ℝ m) w
    (variableSequence_nonnegative m) (variableSequence_ne_zero m) m
  have hf := congrArg Prod.fst h
  change minimum w (positivePair (variableSequence ℝ m) m).1 =
    TropicalContinuant.first (fun j => minimum w (variableSequence ℝ m j)) m at hf
  rw [positivePair_polynomial] at hf
  simpa only [minimum_variableSequence] using hf

/-- The explicit triple/quadruple minimum formula for the determinant. -/
theorem minimum_polynomial_eq_closedFormula (m : ℕ) (w : Fin (m + 2) → ℝ) :
    minimum w (polynomial ℝ m) = TropicalContinuant.closedFormula (extendedWeights m w) m := by
  rw [minimum_polynomial, TropicalContinuant.first_eq_closedFormula]

end GraphicalZonotopes.PathDeterminant
