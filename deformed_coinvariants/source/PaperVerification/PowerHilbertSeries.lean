module

public import PaperVerification.PowerBasisTheorem
public import PaperVerification.GradedComponentBasis
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# The exact product Hilbert series

The series is defined using the dimensions of the actual homogeneous
quotient pieces. Its product formula follows from the proved homogeneous
Artin basis and the explicit product-of-intervals indexing equivalence.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial Module
open scoped BigOperators

namespace PaperVerification.PowerOperators

/-- The paper's polynomial `[j]q = 1 + q + ... + q^(j-1)`. -/
def qIntegerPolynomial (j : ℕ) : Polynomial ℤ :=
  ∑ a ∈ Finset.range j, Polynomial.X^a

def artinGeneratingPolynomial (n m : ℕ) : Polynomial ℤ :=
  ∑ a : ArtinIndex n m, Polynomial.X ^ a.val.degree

theorem artinGeneratingPolynomial_product (n m : ℕ) :
    artinGeneratingPolynomial n m =
      ∏ i : Fin n, ∑ j : Fin (m+i.val), (Polynomial.X : Polynomial ℤ)^j.val := by
  classical
  rw [artinGeneratingPolynomial, Fintype.prod_sum,
    ← (artinIndexEquiv n m).symm.sum_comp]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.prod_pow_eq_pow_sum, Finsupp.degree_eq_sum]
  rfl

theorem artinGeneratingPolynomial_coeff (n m d : ℕ) :
    (artinGeneratingPolynomial n m).coeff d =
      (Fintype.card {a : ArtinIndex n m // a.val.degree=d} : ℤ) := by
  classical
  rw [artinGeneratingPolynomial, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_X_pow]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Fintype.card_subtype]
  congr 1
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, eq_comm]

theorem artinGeneratingPolynomial_paper_product (n m : ℕ) :
    artinGeneratingPolynomial n m =
      ∏ j ∈ Finset.Ico m (m+n), qIntegerPolynomial j := by
  rw [artinGeneratingPolynomial_product]
  have he (j : ℕ) : (∑ a : Fin j, (Polynomial.X : Polynomial ℤ)^a.val) =
      qIntegerPolynomial j := Fin.sum_univ_eq_sum_range _ j
  simp_rw [he]
  rw [Fin.prod_univ_eq_prod_range (fun j => qIntegerPolynomial (m+j)) n]
  rw [Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel_left]

variable {K : Type*} [Field K] {n : ℕ}

theorem artinQuotientBasis_homogeneous
    (c : Fin n → K) (lam : K) (m : ℕ) (hm : 0 < m)
    (hnr : Nonresonant c lam m) (a : ArtinIndex n m) :
    paper_theorem_2_2_basis c lam m hm hnr a ∈
      (tailQuotientGrading c lam m).piece a.val.degree := by
  rw [paper_theorem_2_2_basis_apply, tailQuotientGrading_piece]
  exact Submodule.mem_map.mpr
    ⟨monomial a.val 1, isHomogeneous_monomial (1 : K) rfl, rfl⟩

theorem tailQuotientDegree_finrank_eq_artin_card
    (c : Fin n → K) (lam : K) (m : ℕ) (hm : 0 < m)
    (hnr : Nonresonant c lam m) (d : ℕ) :
    Module.finrank K (tailQuotientDegree c lam m d) =
      Fintype.card {a : ArtinIndex n m // a.val.degree=d} := by
  classical
  have h := GradedComponentBasis.finrank_piece (tailQuotientGrading c lam m)
    (paper_theorem_2_2_basis c lam m hm hnr) (fun a => a.val.degree)
    (artinQuotientBasis_homogeneous c lam m hm hnr) d
  rw [tailQuotientGrading_piece] at h
  simpa only [Nat.card_eq_fintype_card] using h

theorem tail_hilbert_series_eq_artin_polynomial
    (c : Fin n → K) (lam : K) (m : ℕ) (hm : 0 < m)
    (hnr : Nonresonant c lam m) :
    GradedHilbert.series (tailQuotientGrading c lam m) =
      (artinGeneratingPolynomial n m : PowerSeries ℤ) := by
  ext d
  rw [GradedHilbert.coeff_series, tailQuotientGrading_piece,
    tailQuotientDegree_finrank_eq_artin_card c lam m hm hnr,
    Polynomial.coeff_coe, artinGeneratingPolynomial_coeff]

/-- The complete Hilbert-series clause of Theorem 2.2. The displayed factor
is `[m+i]q`; the zero-based indexing is exactly the paper's range
`m, ..., m+n-1`. -/
theorem paper_theorem_2_2_hilbert_series
    (c : Fin n → K) (lam : K) (m : ℕ) (hm : 0 < m)
    (hnr : Nonresonant c lam m) :
    GradedHilbert.series (tailQuotientGrading c lam m) =
      ∏ i : Fin n, ∑ j : Fin (m+i.val), (PowerSeries.X : PowerSeries ℤ)^j.val := by
  rw [tail_hilbert_series_eq_artin_polynomial c lam m hm hnr,
    artinGeneratingPolynomial_product]
  change (Polynomial.coeToPowerSeries.ringHom : Polynomial ℤ →+* PowerSeries ℤ)
    (∏ i : Fin n, ∑ j : Fin (m+i.val), (Polynomial.X : Polynomial ℤ)^j.val) = _
  simp only [map_prod, map_sum, map_pow, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_X]

/-- The same all-degree Hilbert identity with the paper's literal index range
`j = m, ..., m+n-1`, as an equality to a finite polynomial. -/
theorem paper_theorem_2_2_hilbert_polynomial
    (c : Fin n → K) (lam : K) (m : ℕ) (hm : 0 < m)
    (hnr : Nonresonant c lam m) :
    GradedHilbert.series (tailQuotientGrading c lam m) =
      ((∏ j ∈ Finset.Ico m (m+n), qIntegerPolynomial j : Polynomial ℤ) :
        PowerSeries ℤ) := by
  rw [tail_hilbert_series_eq_artin_polynomial c lam m hm hnr,
    artinGeneratingPolynomial_paper_product]

end PaperVerification.PowerOperators
