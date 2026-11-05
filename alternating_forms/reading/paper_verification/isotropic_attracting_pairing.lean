module

public import PaperVerification.IsotropicAttractingIdeal

/-!
# Agreement with the original alternating-form coefficients

The attracting equations use full skew matrices.  The original Plücker
charts use the coefficients on strictly increasing pairs.  This file
proves their equality over every commutative ring, retaining the signs and
without dividing the full matrix sum by two.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.IsotropicAttractingCoordinates

open MvPolynomial
open scoped BigOperators

variable {R A : Type*} [CommRing R] [CommRing A] {n s : ℕ}

theorem map_formMatrix (φ : R →+* A) (c : ℕ) (i j : Fin n) :
    φ (formMatrix c i j) = formMatrix c i j := by
  unfold formMatrix
  split_ifs <;> simp

theorem sum_strictPairs (f : Fin n × Fin n → R) :
    (∑ q : {q : Fin n × Fin n // q.1 < q.2}, f q.val) =
      ∑ i : Fin n, ∑ j : Fin n, if i < j then f (i,j) else 0 := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter (fun q : Fin n × Fin n => q.1 < q.2))
    (by simp)]
  rw [Finset.sum_filter]
  exact Fintype.sum_prod_type _

/-- The full skew-matrix pairing is exactly the original increasing-pair
coefficient formula. -/
theorem formMatrix_pairing_eq (c : ℕ) (u v : Fin n → R) :
    (∑ i : Fin n, ∑ j : Fin n, formMatrix c i j * u i * v j) =
      ∑ q : {q : Fin n × Fin n // q.1 < q.2},
        formMatrix c q.val.1 q.val.2 *
          (u q.val.1 * v q.val.2 - u q.val.2 * v q.val.1) := by
  classical
  have hsplit (i j : Fin n) : formMatrix c i j * u i * v j =
      (if i < j then formMatrix c i j * u i * v j else 0) +
        (if j < i then formMatrix c i j * u i * v j else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt_of_gt h]
    · subst j
      simp
    · simp [h, not_lt_of_gt h]
  calc
    _ = (∑ i : Fin n, ∑ j : Fin n,
        if i < j then formMatrix c i j * u i * v j else 0) +
      ∑ i : Fin n, ∑ j : Fin n,
        if j < i then formMatrix c i j * u i * v j else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      exact hsplit i j
    _ = (∑ i : Fin n, ∑ j : Fin n,
        if i < j then formMatrix c i j * u i * v j else 0) +
      ∑ i : Fin n, ∑ j : Fin n,
        if i < j then formMatrix c j i * u j * v i else 0 := by
      congr 1
      exact Finset.sum_comm
    _ = ∑ i : Fin n, ∑ j : Fin n, if i < j then
        formMatrix c i j * (u i * v j - u j * v i) else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs
      · rw [formMatrix_swap]
        ring
      · ring
    _ = _ := (sum_strictPairs (fun q : Fin n × Fin n =>
      formMatrix c q.1 q.2 * (u q.1 * v q.2 - u q.2 * v q.1))).symm

/-- The exact Plücker-chart convention for the same canonical equations. -/
theorem equation_eq_increasing_pair_sum (p : Fin s ↪ Fin n) (c : ℕ) (i j : Fin s) :
    equation (R := R) p c i j =
      ∑ q : {q : Fin n × Fin n // q.1 < q.2},
        C (formMatrix (R := R) c q.val.1 q.val.2) *
          (row p i q.val.1 * row p j q.val.2 - row p i q.val.2 * row p j q.val.1) := by
  simp only [equation, map_formMatrix]
  exact formMatrix_pairing_eq c (row p i) (row p j)

end PaperVerification.IsotropicAttractingCoordinates
