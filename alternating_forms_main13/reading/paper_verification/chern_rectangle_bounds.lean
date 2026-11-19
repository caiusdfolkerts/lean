module

public import PaperVerification.RectangularReflection
public import PaperVerification.AlternatingFormsChernHomogeneity
public import Mathlib.RingTheory.MvPolynomial.Basic
public import TauCeti.RingTheory.MvPolynomial.RestrictTotalDegree
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv

/-!
# The finite-dimensional rectangle used for the Chern pairing

A coefficient polynomial of ordinary total degree at most `c` becomes, under
elementary substitution, a symmetric root polynomial whose degree in every
individual root is at most `c`. Its source has dimension `choose (c+s) s`.
This uses the actual monomial basis, with the usual slack-coordinate bijection
between degree-at-most-`c` monomials in `s` variables and degree-`c` monomials
in `s+1` variables.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification

open MvPolynomial Finset
open RectangularReflection
open scoped BigOperators

/-- Substitution of polynomials having degree at most one in a chosen root
turns ordinary total degree into an upper bound for that root degree. -/
theorem degreeOf_aeval_le_totalDegree
    {R σ τ : Type*} [CommSemiring R]
    (f : σ → MvPolynomial τ R) (j : τ) (hf : ∀ i, (f i).degreeOf j ≤ 1)
    (P : MvPolynomial σ R) : (aeval f P).degreeOf j ≤ P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum, map_sum]
  refine (degreeOf_sum_le j _ _).trans (Finset.sup_le fun d hd => ?_)
  rw [aeval_monomial, algebraMap_eq]
  refine (degreeOf_C_mul_le _ j _).trans ((degreeOf_prod_le j _ _).trans ?_)
  calc
    ∑ i ∈ d.support, ((f i)^d i).degreeOf j ≤ ∑ i ∈ d.support, d i := by
      apply Finset.sum_le_sum
      intro i _
      exact (degreeOf_pow_le j (f i) (d i)).trans
        (by simpa only [mul_one] using Nat.mul_le_mul_left (d i) (hf i))
    _ ≤ P.totalDegree := le_totalDegree hd

namespace AlternatingForms

variable {s c : ℕ}

/-- Every elementary symmetric coordinate is multiaffine in the root variables. -/
theorem degreeOf_elementary_coordinate (i j : Fin s) :
    (esymm (Fin s) ℚ (i.val+1)).degreeOf j = 1 := by
  rw [degreeOf_def, degrees_esymm (σ := Fin s) (R := ℚ) (by omega) (by simpa using i.isLt)]
  simp

/-- A low ordinary degree in Chern coordinates gives the required root box. -/
theorem elementarySubstitution_bounded_of_totalDegree
    (P : MvPolynomial (Fin s) ℚ) (hP : P.totalDegree ≤ c) :
    BoundedBy (uniformExponent c) (elementarySubstitution s P) := by
  intro d hd j
  change d j ≤ c
  refine (le_degreeOf_of_mem_support j hd).trans ((degreeOf_aeval_le_totalDegree
    (fun i : Fin s => esymm (Fin s) ℚ (i.val+1)) j ?_ P).trans hP)
  intro i
  rw [degreeOf_elementary_coordinate]

end AlternatingForms

/-- Adding the slack exponent turns a bounded-degree monomial into an
exact-degree monomial in one extra variable. -/
def degreeAtMostEquivDegree (s c : ℕ) :
    {d : Fin s →₀ ℕ // d.degree ≤ c} ≃
      {d : Fin (s+1) →₀ ℕ // d.degree = c} where
  toFun d := ⟨Finsupp.equivFunOnFinite.symm (Fin.cons (c-d.1.degree) d.1), by
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_succ]
    change c-d.1.degree + ∑ i : Fin s, d.1 i = c
    rw [← Finsupp.degree_eq_sum]
    exact Nat.sub_add_cancel d.2⟩
  invFun d := ⟨Finsupp.equivFunOnFinite.symm (fun i : Fin s => d.1 i.succ), by
    have h := d.2
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_succ] at h
    rw [Finsupp.degree_eq_sum]
    change (∑ i : Fin s, d.1 i.succ) ≤ c
    omega⟩
  left_inv d := by
    apply Subtype.ext
    ext i
    rfl
  right_inv d := by
    apply Subtype.ext
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · have h := d.2
      rw [Finsupp.degree_eq_sum, Fin.sum_univ_succ] at h
      change c - (Finsupp.equivFunOnFinite.symm
        (fun j : Fin s => d.1 j.succ)).degree = d.1 0
      rw [Finsupp.degree_eq_sum]
      change c - (∑ j : Fin s, d.1 j.succ) = d.1 0
      omega
    · rfl

/-- Count actual exponent vectors of one fixed total degree. -/
theorem card_degree_eq_multichoose (s c : ℕ) :
    Nat.card {d : Fin s →₀ ℕ // d.degree = c} = s.multichoose c := by
  classical
  let e : {d : Fin s →₀ ℕ // d.degree = c} ≃
      (Finset.univ.finsuppAntidiag c : Finset (Fin s →₀ ℕ)) :=
    Equiv.subtypeEquiv (Equiv.refl _) fun d => by
      simp [Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum]
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe,
    Finset.card_finsuppAntidiag_nat_eq_multichoose]
  simp

/-- Dimension of the genuine ordinary-total-degree submodule. -/
theorem finrank_restrictTotalDegree (s c : ℕ) :
    Module.finrank ℚ (restrictTotalDegree (Fin s) ℚ c) = (c+s).choose s := by
  rw [Module.finrank_eq_nat_card_basis (basisRestrictTotalDegree (Fin s) ℚ c),
    Nat.card_congr (degreeAtMostEquivDegree s c), card_degree_eq_multichoose,
    Nat.multichoose_eq]
  have h : s+1+c-1=c+s := by omega
  rw [h, Nat.choose_symm_add]

end PaperVerification
