module

public import PaperVerification.PowerArtinBasis
public import PaperVerification.PowerDegreeQuotient
public import PaperVerification.GradedDimensionComparison
public import PaperVerification.FermionOrdinaryLength

/-!
# The full Artin basis of the reversed power-tail quotient

The upper bound is the coordinate induction. The lower bound is obtained by
comparing every actual homogeneous quotient piece with the independent-
coefficient ordinary fiber, whose complete-intersection length is proved.
All degrees are included through the finite support of the quotient grading.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial Module
open scoped BigOperators

namespace PaperVerification.PowerOperators

variable {K : Type*} [Field K] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

def tailQuotientGrading (c : Fin n → K) (lam : K) (m : ℕ) :
    TauCeti.InternalGrading K (MvPolynomial (Fin n) K ⧸ tailHit c lam m) ℕ := by
  let G : TauCeti.InternalGrading K (MvPolynomial (Fin n) K) ℕ :=
    .ofDecomposition (homogeneousSubmodule (Fin n) K)
  have hU : DirectSum.SetLike.IsHomogeneous G.piece (tailHit c lam m) := by
    rw [TauCeti.InternalGrading.isHomogeneous_ofDecomposition_piece_iff]
    intro d p hp
    have he : (DirectSum.decompose (homogeneousSubmodule (Fin n) K) p d :
        MvPolynomial (Fin n) K) = homogeneousComponent d p :=
      decomposition.decompose'_apply p d
    rw [he]
    exact homogeneousComponent_mem_tailHit c lam m d hp
  exact G.quotient (tailHit c lam m) hU

@[simp] theorem tailQuotientGrading_piece
    (c : Fin n → K) (lam : K) (m d : ℕ) :
    (tailQuotientGrading c lam m).piece d = tailQuotientDegree c lam m d := by
  simp only [tailQuotientGrading, TauCeti.InternalGrading.quotient_piece,
    TauCeti.InternalGrading.ofDecomposition_piece, LinearMap.restrictScalars_self,
    tailQuotientDegree]

theorem generic_tailQuotient_finrank (m : ℕ) (hm : 0 < m) :
    Module.finrank (GenericCoefficientField K n)
      (MvPolynomial (Fin n) (GenericCoefficientField K n) ⧸
        tailHit (genericCoefficient K n) 0 m) =
      ∏ i : Fin n, (m+i.val) := by
  rw [tailHit_zero_eq_ordinaryPowerIdeal, ordinaryPowerIdeal_eq_powerMomentIdeal]
  rw [(Submodule.Quotient.restrictScalarsEquiv (GenericCoefficientField K n)
    (Fermion.powerMomentIdeal (fun _ : Fin n => 1) (genericCoefficient K n) m)).finrank_eq]
  simpa only [Finset.prod_const_one, one_mul] using
    Fermion.powerMoment_quotient_finrank_product (fun _ : Fin n => 1)
      (genericCoefficient K n) m (fun _ => Nat.zero_lt_one) hm
      (genericCoefficient_subset_sum_unit K)

/-- The lower bound uses every homogeneous degree and the complete ordinary
length, over the same characteristic as the original coefficient field. -/
theorem tailQuotient_finrank_ge
    (c : Fin n → K) (lam : K) (m : ℕ) (hm : 0 < m)
    (hnr : Nonresonant c lam m) :
    (∏ i : Fin n, (m+i.val)) ≤
      Module.finrank K (MvPolynomial (Fin n) K ⧸ tailHit c lam m) := by
  letI := tailQuotient_finite c lam m hm hnr
  letI := tailQuotient_finite (genericCoefficient K n) 0 m hm
    (genericCoefficient_nonresonant K m)
  rw [← generic_tailQuotient_finrank (K := K) (n := n) m hm]
  apply GradedHilbert.finrank_le_of_piece_finrank_le
    (tailQuotientGrading (genericCoefficient K n) 0 m)
    (tailQuotientGrading c lam m)
  intro d
  rw [tailQuotientGrading_piece, tailQuotientGrading_piece]
  exact tailQuotientDegree_finrank_ge_generic_zero c lam m d hm

theorem tailQuotient_finrank
    (c : Fin n → K) (lam : K) (m : ℕ) (hm : 0 < m)
    (hnr : Nonresonant c lam m) :
    Module.finrank K (MvPolynomial (Fin n) K ⧸ tailHit c lam m) =
      ∏ i : Fin n, (m+i.val) :=
  le_antisymm (tailQuotient_finrank_le c lam m hm hnr)
    (tailQuotient_finrank_ge c lam m hm hnr)

/-- The exact Artin basis assertion in Theorem 2.2. The only parameter
hypothesis is the full, unbounded nonresonance condition (2.1). -/
def paper_theorem_2_2_basis
    (c : Fin n → K) (lam : K) (m : ℕ) (hm : 0 < m)
    (hnr : Nonresonant c lam m) :
    Basis (ArtinIndex n m) K (MvPolynomial (Fin n) K ⧸ tailHit c lam m) :=
  artinQuotientBasisOfLowerBound c lam m hm hnr
    (tailQuotient_finrank_ge c lam m hm hnr)

@[simp] theorem paper_theorem_2_2_basis_apply
    (c : Fin n → K) (lam : K) (m : ℕ) (hm : 0 < m)
    (hnr : Nonresonant c lam m) (a : ArtinIndex n m) :
    paper_theorem_2_2_basis c lam m hm hnr a =
      (tailHit c lam m).mkQ (monomial a.val 1) :=
  artinQuotientBasisOfLowerBound_apply c lam m hm hnr _ a

/-- A proposition-valued statement records both basis existence and its
literal vectors, so the formal claim cannot hide an unrelated basis. -/
theorem paper_theorem_2_2_monomial_basis
    (c : Fin n → K) (lam : K) (m : ℕ) (hm : 0 < m)
    (hnr : Nonresonant c lam m) :
    ∃ B : Basis (ArtinIndex n m) K (MvPolynomial (Fin n) K ⧸ tailHit c lam m),
      ∀ a, B a = (tailHit c lam m).mkQ (monomial a.val 1) :=
  ⟨paper_theorem_2_2_basis c lam m hm hnr,
    paper_theorem_2_2_basis_apply c lam m hm hnr⟩

end PaperVerification.PowerOperators
