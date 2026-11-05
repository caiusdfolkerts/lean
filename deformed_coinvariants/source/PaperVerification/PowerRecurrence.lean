module

public import PaperVerification.PowerOperators
public import PaperVerification.FermionMomentRecurrence

/-!
# Exact finite presentation of a weighted differential tail

The polynomial remainder formula is inserted before applying the coefficient
and Euler operators. Consequently the coefficient polynomials multiply on the
right of the reversed operators, exactly as required by Section 2.1.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial
open scoped BigOperators

namespace PaperVerification.PowerOperators

variable {K : Type*} [CommRing K] {n : ℕ}
local notation "P" => MvPolynomial (Fin n) K

/-- The universal remainder coefficient, a genuine polynomial in the coordinates. -/
def tailCoefficient (k : ℕ) (j : Fin n) : P :=
  ((Polynomial.X ^ k) %ₘ Fermion.parameterPolynomial
    (fun i : Fin n => (MvPolynomial.X i : P))).coeff j

theorem power_tail_recurrence (m k : ℕ) (i : Fin n) :
    (X i : P) ^ (m + k) =
      ∑ j : Fin n, tailCoefficient (K := K) k j * X i ^ (m + (j : ℕ)) := by
  rw [pow_add, Fermion.powers_as_remainder (fun i : Fin n => (X i : P)) k i]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [tailCoefficient, pow_add]
  ring

/-- The coordinate operator applied after multiplication. -/
def postEuler (c lam : K) (i : Fin n) : P →ₗ[K] P :=
  c • LinearMap.id + lam • euler i

@[simp] theorem postEuler_apply (c lam : K) (i : Fin n) (p : P) :
    postEuler c lam i p = c • p + lam • euler i p := rfl

theorem reversed_eq_sum_postEuler (c : Fin n → K) (lam : K) (k : ℕ) (p : P) :
    reversed c lam k p = ∑ i, postEuler (c i) lam i (X i ^ k * p) := by
  simp only [reversed_apply, component_eq_reversed, postEuler_apply]

/-- Every later tail operator is a sum of the first `n` operators followed by
multiplication by the displayed remainder coefficients. -/
theorem reversed_tail_recurrence (c : Fin n → K) (lam : K) (m k : ℕ) (p : P) :
    reversed c lam (m + k) p =
      ∑ j : Fin n, reversed c lam (m + (j : ℕ))
        (tailCoefficient (K := K) k j * p) := by
  simp only [reversed_eq_sum_postEuler]
  simp_rw [power_tail_recurrence m k, Finset.sum_mul, map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ring

/-- The image span of the literal first `n` operators in the tail. -/
def firstTailHit (c : Fin n → K) (lam : K) (m : ℕ) : Submodule K P :=
  Submodule.span K {p | ∃ j : Fin n, ∃ q, p = reversed c lam (m + (j : ℕ)) q}

theorem tailHit_eq_firstTailHit (c : Fin n → K) (lam : K) (m : ℕ) :
    tailHit c lam m = firstTailHit c lam m := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro p ⟨k, hk, q, rfl⟩
    obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [reversed_tail_recurrence]
    apply Submodule.sum_mem
    intro j _
    exact Submodule.subset_span ⟨j, _, rfl⟩
  · apply Submodule.span_le.mpr
    rintro p ⟨j, q, rfl⟩
    exact Submodule.subset_span ⟨m + (j : ℕ), Nat.le_add_right _ _, q, rfl⟩

end PaperVerification.PowerOperators
