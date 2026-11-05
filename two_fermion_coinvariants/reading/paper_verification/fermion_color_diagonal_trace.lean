module

public import PaperVerification.FermionColorAction
public import PaperVerification.FermionTypeAMultiplicity
public import PaperVerification.FermionStrictRank
public import Mathlib.LinearAlgebra.Trace

/-!
# The actual diagonal color action on the literal strict basis

This file computes the trace of the genuine quotient action. Its
basis vectors are the original ordered monomials, and its eigenvalues
are the actual powers of the two diagonal entries. The weighted-box and
multiplicity regrouping is a separate subsequent step.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators

namespace PaperVerification.Fermion.ColorAction

variable {R : Type*} [CommRing R] {n : ℕ}

theorem ambient_theta_list (A : ColorMatrix R) (h10 : A 1 0=0)
    (l : List (Fin n)) :
    ambient A (l.map (theta R n)).prod =
      (MvPolynomial.C (A 0 0) : PolynomialRing R n)^l.length •
        (l.map (theta R n)).prod := by
  induction l with
  | nil => simp only [List.map_nil,List.prod_nil,List.length_nil,pow_zero,one_smul,map_one]
  | cons i l ih =>
      simp only [List.map_cons,List.prod_cons,List.length_cons,map_mul,
        ambient_theta,h10,map_zero,zero_smul,add_zero,ih,smul_mul_smul_comm,pow_succ']

theorem ambient_xi_list (A : ColorMatrix R) (h01 : A 0 1=0)
    (l : List (Fin n)) :
    ambient A (l.map (xi R n)).prod =
      (MvPolynomial.C (A 1 1) : PolynomialRing R n)^l.length •
        (l.map (xi R n)).prod := by
  induction l with
  | nil => simp only [List.map_nil,List.prod_nil,List.length_nil,pow_zero,one_smul,map_one]
  | cons i l ih =>
      simp only [List.map_cons,List.prod_cons,List.length_cons,map_mul,
        ambient_xi,h01,map_zero,zero_smul,zero_add,ih,smul_mul_smul_comm,pow_succ']

/-- Eigenvectors are the actual polynomial/exterior monomials in the ambient
algebra, before passing to any quotient or choosing a quotient basis. -/
theorem ambient_boxMonomial_diagonal (A : ColorMatrix R)
    (h01 : A 0 1=0) (h10 : A 1 0=0)
    (T S : Finset (Fin n)) (e : Fin n → ℕ) :
    ambient A (boxMonomial (K := R) T S e)=
      (A 0 0^T.card*A 1 1^S.card) • boxMonomial (K := R) T S e := by
  have hpoly : ambient A (boxMonomial (K := R) T S e)=
      (MvPolynomial.C (A 0 0^T.card*A 1 1^S.card) : PolynomialRing R n) •
        boxMonomial (K := R) T S e := by
    rw [boxMonomial,map_smul,map_mul,ambient_theta_list A h10,
      ambient_xi_list A h01,smul_mul_smul_comm]
    simp only [Finset.length_sort,←map_pow,←map_mul]
    exact smul_comm _ _ _
  rw [hpoly]
  exact IsScalarTower.algebraMap_smul (PolynomialRing R n) _ _

end PaperVerification.Fermion.ColorAction

namespace PaperVerification.Fermion.TypeA

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

/-- The diagonal color character of one literal box monomial. -/
def diagonalMonomialWeight (u v : F) (hn : 0<n) (z : StrictIndex (data (F := F) hn)) : F :=
  u^z.val.1.1.card*v^z.val.1.2.card

theorem quotientEquiv_strictPaperBasis_diagonal (hn : 0<n)
    (g : Matrix.GeneralLinearGroup (Fin 2) F) (h01 : g.val 0 1=0) (h10 : g.val 1 0=0)
    (z : StrictIndex (data (F := F) hn)) :
    ColorAction.quotientEquiv g (fun i : Fin n ↦ MvPolynomial.X i)
        (strictPaperBasis (data hn) z)=
      diagonalMonomialWeight (g.val 0 0) (g.val 1 1) hn z • strictPaperBasis (data hn) z := by
  rw [strictPaperBasis_apply,strictClasses]
  change ColorAction.quotientEquiv g (fun i : Fin n ↦ MvPolynomial.X i)
    ((strictIdeal (fun _ ↦ (1 : F)) (fun i : Fin n ↦ MvPolynomial.X i)).ringCon.mkₐ F
      (boxMonomial z.val.1.1 z.val.1.2 z.val.2)) = _
  rw [ColorAction.quotientEquiv_mk,ColorAction.ambient_boxMonomial_diagonal _ h01 h10,
    map_smul]
  rfl

/-- Trace is taken on the actual quotient action. No action is defined by
transporting a diagonal matrix through the desired basis. -/
theorem diagonal_trace_eq_box_sum (hn : 0<n)
    (g : Matrix.GeneralLinearGroup (Fin 2) F) (h01 : g.val 0 1=0) (h10 : g.val 1 0=0) :
    LinearMap.trace F (StrictQuotient (fun _ ↦ (1 : F)) (fun i : Fin n ↦ MvPolynomial.X i))
      (ColorAction.quotientEquiv g (fun i : Fin n ↦ MvPolynomial.X i)).toLinearMap =
        ∑ z : StrictIndex (data (F := F) hn),
          diagonalMonomialWeight (g.val 0 0) (g.val 1 1) hn z := by
  let b : Module.Basis (StrictIndex (data (F := F) hn)) F
      (StrictQuotient (fun _ ↦ (1 : F)) (fun i : Fin n ↦ MvPolynomial.X i)) :=
    strictPaperBasis (data hn)
  have heigen (z : StrictIndex (data (F := F) hn)) :
      ColorAction.quotientEquiv g (fun i : Fin n ↦ MvPolynomial.X i) (b z) =
        diagonalMonomialWeight (g.val 0 0) (g.val 1 1) hn z • b z :=
    quotientEquiv_strictPaperBasis_diagonal hn g h01 h10 z
  rw [LinearMap.trace_eq_matrix_trace F b,Matrix.trace]
  apply Finset.sum_congr rfl
  intro z hz
  rw [Matrix.diag_apply,LinearMap.toMatrix_apply]
  change b.repr
    (ColorAction.quotientEquiv g (fun i : Fin n ↦ MvPolynomial.X i) (b z)) z = _
  rw [heigen]
  simp only [map_smul,Module.Basis.repr_self,Finsupp.smul_apply,
    Finsupp.single_eq_same,smul_eq_mul,mul_one]

end PaperVerification.Fermion.TypeA
