module

public import PaperVerification.PowerBasisTheorem
public import PaperVerification.PowerConjugation
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The Artin basis for the original weighted power operators

The quotient is transported by the proved diagonal conjugation. Each
transported basis vector is rescaled back to the literal monomial class;
the result uses precisely the extra low-exponent conditions in (2.3).
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial Module
open scoped BigOperators

namespace PaperVerification.PowerOperators

variable {K : Type*} [Field K] {n : ℕ}

def diagonalQuotientEquiv (c : Fin n → K) (lam : K) (m : ℕ)
    (h : ∀ i, ∀ a : ℕ, c i + lam * (a : K) ≠ 0) :
    (MvPolynomial (Fin n) K ⧸ originalTailHit c lam m) ≃ₗ[K]
      (MvPolynomial (Fin n) K ⧸ tailHit c lam m) :=
  Submodule.Quotient.equiv _ _ (diagonalEquiv c lam h)
    (diagonalEquiv_map_originalTailHit c lam h m)

@[simp] theorem diagonalQuotientEquiv_mkQ
    (c : Fin n → K) (lam : K) (m : ℕ)
    (h : ∀ i, ∀ a : ℕ, c i + lam * (a : K) ≠ 0)
    (p : MvPolynomial (Fin n) K) :
    diagonalQuotientEquiv c lam m h ((originalTailHit c lam m).mkQ p) =
      (tailHit c lam m).mkQ (diagonalEquiv c lam h p) := rfl

def originalArtinBasis
    (c : Fin n → K) (lam : K) (m : ℕ) (hm : 0 < m)
    (hnr : Nonresonant c lam m)
    (hlow : ∀ i, ∀ a : ℕ, a < m → c i + lam * (a : K) ≠ 0) :
    Basis (ArtinIndex n m) K (MvPolynomial (Fin n) K ⧸ originalTailHit c lam m) :=
  ((paper_theorem_2_2_basis c lam m hm hnr).map
    (diagonalQuotientEquiv c lam m (coordinate_factor_ne_zero hnr hlow)).symm).isUnitSMul
      (w := fun a => diagonalWeight c lam a.val)
      (fun a => isUnit_iff_ne_zero.mpr (diagonalWeight_ne_zero hnr hlow a.val))

@[simp] theorem originalArtinBasis_apply
    (c : Fin n → K) (lam : K) (m : ℕ) (hm : 0 < m)
    (hnr : Nonresonant c lam m)
    (hlow : ∀ i, ∀ a : ℕ, a < m → c i + lam * (a : K) ≠ 0)
    (a : ArtinIndex n m) :
    originalArtinBasis c lam m hm hnr hlow a =
      (originalTailHit c lam m).mkQ (monomial a.val 1) := by
  let e := diagonalQuotientEquiv c lam m (coordinate_factor_ne_zero hnr hlow)
  apply e.injective
  simp only [e, originalArtinBasis, Basis.isUnitSMul_apply, Basis.map_apply,
    map_smul, LinearEquiv.apply_symm_apply, paper_theorem_2_2_basis_apply]
  change diagonalWeight c lam a.val • (tailHit c lam m).mkQ (monomial a.val 1) =
    diagonalQuotientEquiv c lam m _ ((originalTailHit c lam m).mkQ (monomial a.val 1))
  rw [diagonalQuotientEquiv_mkQ, diagonalEquiv_monomial, map_smul]

theorem paper_theorem_2_2_original_monomial_basis
    (c : Fin n → K) (lam : K) (m : ℕ) (hm : 0 < m)
    (hnr : Nonresonant c lam m)
    (hlow : ∀ i, ∀ a : ℕ, a < m → c i + lam * (a : K) ≠ 0) :
    ∃ B : Basis (ArtinIndex n m) K
        (MvPolynomial (Fin n) K ⧸ originalTailHit c lam m),
      ∀ a, B a = (originalTailHit c lam m).mkQ (monomial a.val 1) :=
  ⟨originalArtinBasis c lam m hm hnr hlow,
    originalArtinBasis_apply c lam m hm hnr hlow⟩

/-- The exact sufficiency and monomial-basis clause of Theorem 1.1, over
every characteristic-zero coefficient field. Its equivariant assertion and
the necessity for `n ≥ 2` are separate claims. -/
theorem paper_theorem_1_1_monomial_basis [CharZero K]
    (α : K) (hα : α ∉ exceptionalSet K n) :
    ∃ B : Basis (ArtinIndex n 1) K
        (MvPolynomial (Fin n) K ⧸ originalTailHit (fun _ => (1 : K)) α 1),
      ∀ a, B a = (originalTailHit (fun _ => (1 : K)) α 1).mkQ (monomial a.val 1) := by
  apply paper_theorem_2_2_original_monomial_basis _ _ _ Nat.zero_lt_one
  · apply (nonresonant_one_iff α).mpr
    simpa only [Fintype.card_fin] using hα
  · intro i a ha
    have ha0 : a = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ ha)
    simp only [ha0, Nat.cast_zero, mul_zero, add_zero, ne_eq, one_ne_zero, not_false_eq_true]

end PaperVerification.PowerOperators
