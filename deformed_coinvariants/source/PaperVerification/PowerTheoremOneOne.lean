module

public import PaperVerification.PowerExceptionalArtin

/-!
# All clauses of Theorem 1.1

The theorem uses the original operators, the actual sum of all positive-index
images, the literal elementary-symmetric ideal and the full symmetric-group
action. The monomial vectors are the stated Artin monomials. The final clause
is the sharp necessity assertion for every `n ≥ 2`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial Module

namespace PaperVerification.PowerOperators

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

theorem paper_theorem_1_1 (α : K) :
    (α ∉ exceptionalSet K n →
      (∃ B : Basis (ArtinIndex n 1) K
          (MvPolynomial (Fin n) K ⧸ originalTailHit (fun _ => (1 : K)) α 1),
        ∀ a, B a = (originalTailHit (fun _ => (1 : K)) α 1).mkQ (monomial a.val 1)) ∧
      PaperVerification.GradedRepresentationEquivalent
        (originalCoinvariantRepresentation α)
        (ordinaryCoinvariantRepresentation (K := K) (n := n))
        (originalTailQuotientDegree (fun _ : Fin n => (1 : K)) α 1)
        (ordinaryCoinvariantDegree K n)) ∧
    (2 ≤ n →
      (artinSpan K n 1).map
        (originalTailHit (fun _ : Fin n => (1 : K)) α 1).mkQ = ⊤ →
      α ∉ exceptionalSet K n) :=
  ⟨paper_theorem_1_1_sufficiency α,
    fun hn => paper_theorem_1_1_artin_necessity hn α⟩

end PaperVerification.PowerOperators
