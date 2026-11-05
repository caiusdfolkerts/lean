module

public import PaperVerification.FermionGradedHilbert
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.Algebra.Polynomial.BigOperators

/-!
# The Hilbert polynomial of a finite internally graded vector space

The grading has only finitely many nonzero pieces. Their individual bases
assemble into an actual basis of the vector space, so evaluating the Hilbert
polynomial at one gives its full vector-space dimension.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.GradedHilbert

open scoped BigOperators
open Module

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
variable (G : TauCeti.InternalGrading K M ℕ) [Module.Finite K M]

abbrev NonzeroDegree := {e : ℕ // G.piece e ≠ ⊥}

instance nonzeroDegreeFintype : Fintype (NonzeroDegree G) :=
  G.finite_piece_ne_bot.fintype

/-- This is a finite polynomial because the actual grading of a finite
module has finite support. -/
def hilbertPolynomial : Polynomial ℤ :=
  ∑ e : NonzeroDegree G,
    Polynomial.monomial e.val (Module.finrank K (G.piece e.val) : ℤ)

/-- The dimension sum is proved from a collected basis of the actual pieces. -/
theorem finrank_eq_sum_nonzero_pieces :
    Module.finrank K M = ∑ e : NonzeroDegree G, Module.finrank K (G.piece e.val) := by
  let h : DirectSum.IsInternal (fun e : NonzeroDegree G ↦ G.piece e.val) :=
    DirectSum.isInternal_ne_bot_iff.mpr G.isInternal
  let B := h.collectedBasis (fun e : NonzeroDegree G ↦ Module.finBasis K (G.piece e.val))
  rw [Module.finrank_eq_card_basis B]
  simp only [Fintype.card_sigma, Fintype.card_fin]

@[simp] theorem hilbertPolynomial_coeff (e : ℕ) :
    (hilbertPolynomial G).coeff e = (Module.finrank K (G.piece e) : ℤ) := by
  classical
  rw [hilbertPolynomial, Polynomial.finsetSum_coeff]
  by_cases he : G.piece e = ⊥
  · rw [he, finrank_bot, Nat.cast_zero]
    apply Finset.sum_eq_zero
    intro i _
    have hi : i.val ≠ e := by
      intro h
      apply i.property
      simpa only [h] using he
    simp only [Polynomial.coeff_monomial, Finsupp.single_apply, if_neg hi]
  · let i : NonzeroDegree G := ⟨e, he⟩
    rw [Finset.sum_eq_single i]
    · simp only [i, Polynomial.coeff_monomial, Finsupp.single_apply, ite_true]
    · intro j _ hji
      have hj : j.val ≠ e := fun h ↦ hji (Subtype.ext h)
      simp only [Polynomial.coeff_monomial, Finsupp.single_apply, if_neg hj]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim

/-- The finite Hilbert polynomial represents the entire formal power series,
not a truncated range of degrees. -/
theorem hilbertPolynomial_coe :
    (hilbertPolynomial G : PowerSeries ℤ) = series G := by
  ext e
  simp only [Polynomial.coeff_coe, hilbertPolynomial_coeff, coeff_series]

@[simp] theorem hilbertPolynomial_eval_one :
    (hilbertPolynomial G).eval 1 = (Module.finrank K M : ℤ) := by
  rw [hilbertPolynomial, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_monomial, one_pow, mul_one]
  rw [← Nat.cast_sum, finrank_eq_sum_nonzero_pieces G]

end PaperVerification.GradedHilbert
