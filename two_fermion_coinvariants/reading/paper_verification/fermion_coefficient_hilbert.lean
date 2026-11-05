module

public import PaperVerification.FermionCoefficientGrading
public import PaperVerification.FermionColorMultiplicityEnumeration
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-! The coefficient polynomial counts the actual original homogeneous
images in the colon quotient.  -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators TensorProduct

namespace PaperVerification.Fermion.TypeA

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

theorem coefficientBoxPolynomial (m : MultiplicityVector n) (hm : Admissible m) :
    (∑ a : StrictWordPolynomialIndex (fun _ : Fin n ↦ 1) (canonicalWord m),
      (Polynomial.X : Polynomial F)^coefficientBoxDegree m a)=
      ColorPaths.multiplicityBoxPolynomial (Polynomial.X : Polynomial F) m := by
  have h := ColorPaths.strictWord_q_sum (Polynomial.X : Polynomial F) (canonicalWord m)
  simpa only [coefficientBoxDegree,Finsupp.degree_eq_sum,
    strictWord_iff_admissible,canonicalWord_multiplicity,hm,if_true,
    ColorPaths.word_bounds_eq_arrival,ColorPaths.multiplicityBoxPolynomial] using h

/-- The coefficient of the box polynomial is the dimension of the actual
homogeneous image in the original coefficient quotient. -/
theorem coefficientPolynomialPiece_finrank (hn : 0<n)
    (m : MultiplicityVector n) (hm : Admissible m) (k : ℕ) :
    (Module.finrank F (coefficientPolynomialPiece (F := F) m k) : F)=
      (ColorPaths.multiplicityBoxPolynomial (Polynomial.X : Polynomial F) m).coeff k := by
  rw [Module.finrank_eq_card_basis (coefficientPolynomialPieceBasis hn m k),
    ←coefficientBoxPolynomial m hm,Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_X_pow]
  have hcard : (Fintype.card
      {a : StrictWordPolynomialIndex (fun _ : Fin n ↦ 1) (canonicalWord m) //
        coefficientBoxDegree m a=k} : F)=
      ∑ a : StrictWordPolynomialIndex (fun _ : Fin n ↦ 1) (canonicalWord m),
        if coefficientBoxDegree m a=k then (1 : F) else 0 := by
    rw [Fintype.card_subtype,←Finset.sum_filter]
    simp only [Finset.sum_const,nsmul_one]
  exact hcard.trans (Finset.sum_congr rfl (fun a _ ↦ by simp only [eq_comm]))

end PaperVerification.Fermion.TypeA
