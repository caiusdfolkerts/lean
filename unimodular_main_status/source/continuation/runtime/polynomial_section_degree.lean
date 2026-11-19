module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # The actual degree of a polynomial in degree-one section variables

A homogeneous coefficient of K[T] is exactly the evaluation of the matching
homogeneous component of the source polynomial. This is the algebraic step
which extracts homogeneous preimages from ordinary surjectivity.
-/

@[expose] public section
noncomputable section
universe u v
open scoped Classical BigOperators
namespace Unimodular.GraphicSectionRing.ActualSections

section PolynomialCoefficients

variable {k K : Type u} [CommRing k] [CommRing K] {ι : Type v}
  (f : k →+* K) (v : ι → K)

/-- The literal homogeneous evaluation in K[T]. -/
def degreeOnePolynomialEvaluation :
    MvPolynomial ι k →+* AddMonoidAlgebra K ℕ :=
  MvPolynomial.eval₂Hom (AddMonoidAlgebra.singleZeroRingHom.comp f)
    (fun i => AddMonoidAlgebra.single 1 (v i))

theorem degreeOnePolynomialEvaluation_monomial (d : ι →₀ ℕ) (a : k) :
    degreeOnePolynomialEvaluation f v (MvPolynomial.monomial d a) =
      AddMonoidAlgebra.single d.degree
        (MvPolynomial.eval₂Hom f v (MvPolynomial.monomial d a)) := by
  rw [degreeOnePolynomialEvaluation, MvPolynomial.eval₂Hom_monomial,
    MvPolynomial.eval₂Hom_monomial]
  change AddMonoidAlgebra.single 0 (f a) *
      d.prod (fun i n => (AddMonoidAlgebra.single 1 (v i)) ^ n) = _
  simp only [AddMonoidAlgebra.single_pow, nsmul_eq_mul, mul_one, Finsupp.prod]
  rw [AddMonoidAlgebra.prod_single, AddMonoidAlgebra.single_mul_single, zero_add]
  rfl

/-- Extracting degree N after homogeneous evaluation is exactly evaluating
the degree-N component of the original polynomial. -/
theorem degreeOnePolynomialEvaluation_coefficient (p : MvPolynomial ι k) (N : ℕ) :
    (degreeOnePolynomialEvaluation f v p).coeff N =
      MvPolynomial.eval₂Hom f v (MvPolynomial.homogeneousComponent N p) := by
  nth_rw 1 [p.as_sum]
  rw [map_sum, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    MvPolynomial.homogeneousComponent_apply, map_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  rw [degreeOnePolynomialEvaluation_monomial, AddMonoidAlgebra.coeff_single_apply]

end PolynomialCoefficients

end Unimodular.GraphicSectionRing.ActualSections
#print axioms Unimodular.GraphicSectionRing.ActualSections.degreeOnePolynomialEvaluation_coefficient
end
