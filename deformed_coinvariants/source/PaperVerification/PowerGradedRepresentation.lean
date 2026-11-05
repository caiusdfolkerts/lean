module

public import PaperVerification.PowerEquivariantLowerBound
public import PaperVerification.PowerComparatorLength
public import PaperVerification.PowerBasisTheorem
public import PaperVerification.RepresentationHomComparison
public import PaperVerification.GradedDimensionEquality

/-!
# The full degreewise representation comparison in Theorem 2.2

The original-field Hom lower bounds first imply ordinary dimension lower
bounds in every degree. The two finite quotient spaces have the same total
dimension, so these inequalities are all equalities. Semisimple reconstruction
then gives actual equivalences of the two representations in every degree.
The invertibility of the group order is derived from nonresonance.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial Representation

namespace PaperVerification.PowerOperators

variable {K : Type*} [Field K] {n : ℕ}

theorem complete_degree_finrank_le_tail
    (c : Fin n → K) (lam : K) (m d : ℕ) (hm : 0 < m) (hnr : Nonresonant c lam m)
    (G : Subgroup (Equiv.Perm (Fin n)))
    (hfix : ∀ g : G, ∀ i, c ((g : Equiv.Perm (Fin n)) i) = c i) :
    Module.finrank K (ordinaryQuotientDegree (completeHomogeneousFamily K n m) d) ≤
      Module.finrank K (tailQuotientDegree c lam m d) := by
  apply RepresentationHomComparison.finrank_le_of_coordinate_hom_tests
    (completeHomogeneousDegreeRepresentation G m d)
    (tailQuotientDegreeRepresentation G c lam m hfix d)
  intro r τ
  exact complete_intertwiner_finrank_le_tail c lam m d hm hnr G hfix τ

theorem complete_degree_finrank_eq_tail
    (c : Fin n → K) (lam : K) (m d : ℕ) (hm : 0 < m) (hnr : Nonresonant c lam m)
    (G : Subgroup (Equiv.Perm (Fin n)))
    (hfix : ∀ g : G, ∀ i, c ((g : Equiv.Perm (Fin n)) i) = c i) :
    Module.finrank K (ordinaryQuotientDegree (completeHomogeneousFamily K n m) d) =
      Module.finrank K (tailQuotientDegree c lam m d) := by
  letI := completeHomogeneous_quotient_finite (K := K) (n := n) m hm
  letI := tailQuotient_finite c lam m hm hnr
  have h := GradedHilbert.piece_finrank_eq_of_piece_finrank_le_of_finrank_eq
    (completeHomogeneousGrading K n m) (tailQuotientGrading c lam m)
    (fun e => by
      rw [completeHomogeneousGrading_piece,tailQuotientGrading_piece]
      exact complete_degree_finrank_le_tail c lam m e hm hnr G hfix)
    (by rw [completeHomogeneous_quotient_finrank m hm,tailQuotient_finrank c lam m hm hnr]) d
  rw [completeHomogeneousGrading_piece,tailQuotientGrading_piece] at h
  exact h

/-- Every degree is compared over the original field and with the actual
polynomial permutation actions. No finite degree range or irreducible model
is imposed in this conclusion. -/
theorem paper_theorem_2_2_degree_representation
    (c : Fin n → K) (lam : K) (m d : ℕ) (hm : 0 < m) (hnr : Nonresonant c lam m)
    (G : Subgroup (Equiv.Perm (Fin n)))
    (hfix : ∀ g : G, ∀ i, c ((g : Equiv.Perm (Fin n)) i) = c i) :
    Nonempty ((completeHomogeneousDegreeRepresentation G m d).Equiv
      (tailQuotientDegreeRepresentation G c lam m hfix d)) := by
  letI : NeZero (Nat.card G : K) := ⟨(hnr.isUnit_stabilizer_card G hfix).ne_zero⟩
  apply RepresentationHomComparison.nonempty_equiv_of_coordinate_hom_le_of_finrank_eq
  · intro r τ
    exact complete_intertwiner_finrank_le_tail c lam m d hm hnr G hfix τ
  · exact complete_degree_finrank_eq_tail c lam m d hm hnr G hfix

end PaperVerification.PowerOperators
