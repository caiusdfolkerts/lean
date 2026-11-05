module

public import PaperVerification.FermionColorPolynomialAction
public import PaperVerification.FermionColorRational
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Rationality and complete reducibility in each actual polynomial degree

Matrix coefficients of the genuine degree-piece action are extended to
linear functionals on the original quotient and evaluated on its literal
monomial representatives. Polynomiality is proved before applying the
pinned rational-representation complete-reducibility theorem.

-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators TensorProduct

namespace PaperVerification.Fermion.TypeA

open Exterior
variable {n : ℕ}

local instance colorPolynomialRationalOddOrder : LinearOrder (OddIndex n) :=
  LinearOrder.lift' modeRank modeRank_injective

/-- Each actual degree-piece representation has polynomial matrix entries.
Extension of coordinate functionals is ordinary linear algebra, independent
of the desired representation decomposition. -/
theorem polynomialPieceColorRepresentation_polynomial (hn : 0<n) (k : ℕ) :
    TauCeti.IsPolynomialRep (polynomialPieceColorRepresentation (F := ℂ) hn k) := by
  let B := polynomialPieceBasis (F := ℂ) hn k
  apply (TauCeti.isPolynomialRep_iff_forall_mem_polynomialFunctions B).mpr
  intro i j
  obtain ⟨ell,hell⟩ := (B.coord i).exists_extend
  let q := (strictIdeal (fun _ : Fin n ↦ (1 : ℂ))
    (fun t : Fin n ↦ MvPolynomial.X t)).ringCon.mkₐ ℂ
  have h := ColorAction.boxMonomial_matrixCoefficient_polynomial
    j.val.val.1.1 j.val.val.1.2 j.val.val.2 (ell.comp q.toLinearMap)
  convert h using 1
  funext g
  rw [LinearMap.toMatrix_apply]
  change (B.coord i) (polynomialPieceColorRepresentation hn k g (B j))=_
  rw [←hell]
  change ell (ColorAction.quotientEquiv g (fun t : Fin n ↦ MvPolynomial.X t)
    ((polynomialPieceBasis (F := ℂ) hn k j : polynomialPiece (F := ℂ) hn k) :
      StrictQuotient (data (F := ℂ) hn).beta (data (F := ℂ) hn).phi))=_
  rw [polynomialPieceBasis_coe,strictPaperBasis_apply]
  change ell (ColorAction.quotientEquiv g (fun t : Fin n ↦ MvPolynomial.X t)
    (q (boxMonomial j.val.val.1.1 j.val.val.1.2 j.val.val.2)))=_
  rw [ColorAction.quotientEquiv_mk]
  rfl

/-- Complete reducibility applies in every actual polynomial degree, as used
in Section8.2, without a semisimplicity or rationality hypothesis. -/
theorem polynomialPieceColorRepresentation_semisimple (hn : 0<n) (k : ℕ) :
    (polynomialPieceColorRepresentation (F := ℂ) hn k).IsSemisimpleRepresentation :=
  (polynomialPieceColorRepresentation_polynomial hn k).isRationalRep.isSemisimpleRepresentation

end PaperVerification.Fermion.TypeA
