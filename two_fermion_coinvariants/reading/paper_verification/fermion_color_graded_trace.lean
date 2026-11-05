module

public import PaperVerification.FermionColorDiagonalTrace
public import PaperVerification.FermionColorMultiplicityEnumeration
public import PaperVerification.FermionStrictAssociatedGraded

/-!
# Polynomial-degree traces of the actual color action

The degree piece is the image of the independently defined homogeneous
polynomial/exterior space. Its basis is obtained by homogeneous projection
of the actual quotient kernel. Thus the trace below is a trace on the
original quotient's degree piece, not a grading transported from a formula.

-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators

namespace PaperVerification.Fermion.TypeA

open Exterior

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

local instance colorGradedTraceOddOrder : LinearOrder (OddIndex n) :=
  LinearOrder.lift' modeRank modeRank_injective

/-- Ordinary polynomial degree; both exterior families have degree zero. -/
def polynomialDegree (z : SuperMonomialIndex n) : ℕ := ∑ i,z.1 i

def boxPolynomialDegree (hn : 0<n) (z : StrictIndex (data (F := F) hn)) : ℕ :=
  ∑ i,z.val.2 i

theorem strictSuperWeight_data (hn : 0<n) :
    strictSuperWeight (data (F := F) hn)=polynomialDegree := by
  funext z
  simp only [strictSuperWeight_apply,data,coveringWeight,Finset.prod_const_one,
    Finsupp.weight_eq_sum,smul_eq_mul,mul_one,polynomialDegree]

/-- This is the actual image of degree-k polynomials tensored with the
entire original exterior algebra. -/
def polynomialPiece (hn : 0<n) (k : ℕ) :
    Submodule F (StrictQuotient (data (F := F) hn).beta (data (F := F) hn).phi) :=
  (BasisFiltered.homogeneousPiece (superMonomialBasis (K := F)) polynomialDegree k).map
    ((strictIdeal (data (F := F) hn).beta (data (F := F) hn).phi).ringCon.mkₐ F).toLinearMap

theorem polynomial_kernel_component (hn : 0<n) (k : ℕ) (x : SuperRing F n)
    (hx : x∈(((strictIdeal (data (F := F) hn).beta (data (F := F) hn).phi).ringCon.mkₐ F).toLinearMap).ker) :
    BasisFiltered.component (superMonomialBasis (K := F)) polynomialDegree k x ∈
      (((strictIdeal (data (F := F) hn).beta (data (F := F) hn).phi).ringCon.mkₐ F).toLinearMap).ker := by
  have hphi :
      (fun i : Fin n ↦ (MvPolynomial.X i : PolynomialRing F n)^(data (F := F) hn).r i)=
        (data (F := F) hn).phi := by
    funext i
    change (MvPolynomial.X i : PolynomialRing F n)^1=MvPolynomial.X i
    exact pow_one _
  have hx' : x∈(((strictIdeal (data (F := F) hn).beta
      (fun i ↦ MvPolynomial.X i^(data (F := F) hn).r i)).ringCon.mkₐ F).toLinearMap).ker := by
    rw [hphi]
    exact hx
  have h := strictPower_kernel_component (data (F := F) hn) k x hx'
  rw [strictSuperWeight_data,hphi] at h
  exact h

theorem boxMonomial_polynomial_homogeneous (hn : 0<n)
    (z : StrictIndex (data (F := F) hn)) :
    BasisFiltered.Homogeneous (superMonomialBasis (K := F)) polynomialDegree
      (boxPolynomialDegree (F := F) hn z) (boxMonomial z.val.1.1 z.val.1.2 z.val.2) := by
  rw [boxMonomial_eq_tensor]
  simpa only [superMonomialBasis_apply,polynomialDegree,boxPolynomialDegree,
    Finsupp.coe_equivFunOnFinite_symm] using
      (BasisFiltered.homogeneous_basis (superMonomialBasis (K := F)) polynomialDegree
        (Finsupp.equivFunOnFinite.symm z.val.2,z.val.1.1.disjSum z.val.1.2))

abbrev PolynomialBoxIndex (hn : 0<n) (k : ℕ) :=
  {z : StrictIndex (data (F := F) hn) // boxPolynomialDegree (F := F) hn z=k}

/-- Every degree piece has exactly the literal basis vectors of that degree. -/
def polynomialPieceBasis (hn : 0<n) (k : ℕ) :
    Module.Basis (PolynomialBoxIndex (F := F) hn k) F (polynomialPiece (F := F) hn k) :=
  BasisFiltered.quotientPieceBasis (superMonomialBasis (K := F)) polynomialDegree
    ((strictIdeal (data (F := F) hn).beta (data (F := F) hn).phi).ringCon.mkₐ F).toLinearMap
    (strictPaperBasis (data (F := F) hn))
    (fun z ↦ boxMonomial z.val.1.1 z.val.1.2 z.val.2)
    (boxPolynomialDegree (F := F) hn) (boxMonomial_polynomial_homogeneous (F := F) hn)
    (fun z ↦ by rw [strictPaperBasis_apply]; rfl)
    (polynomial_kernel_component (F := F) hn) k

@[simp] theorem polynomialPieceBasis_coe (hn : 0<n) (k : ℕ)
    (z : PolynomialBoxIndex (F := F) hn k) :
    (polynomialPieceBasis (F := F) hn k z : StrictQuotient (data (F := F) hn).beta (data (F := F) hn).phi)=
      strictPaperBasis (data (F := F) hn) z.val :=
  BasisFiltered.quotientPieceBasis_coe _ _ _ _ _ _ _ _ _ _ _

theorem diagonal_preserves_polynomialPiece (hn : 0<n) (k : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin 2) F) (h01 : g.val 0 1=0) (h10 : g.val 1 0=0)
    (x : StrictQuotient (data (F := F) hn).beta (data (F := F) hn).phi)
    (hx : x∈polynomialPiece (F := F) hn k) :
    ColorAction.quotientEquiv g (fun i : Fin n ↦ MvPolynomial.X i) x ∈
      polynomialPiece (F := F) hn k := by
  let b := polynomialPieceBasis (F := F) hn k
  have he : (∑ z : PolynomialBoxIndex (F := F) hn k,
      b.repr ⟨x,hx⟩ z • strictPaperBasis (data (F := F) hn) z.val)=x := by
    simpa only [map_sum,map_smul,Submodule.subtype_apply,polynomialPieceBasis_coe,b] using
      congrArg (polynomialPiece (F := F) hn k).subtype (b.sum_repr ⟨x,hx⟩)
  rw [←he,map_sum]
  apply Submodule.sum_mem
  intro z hz
  rw [map_smul,quotientEquiv_strictPaperBasis_diagonal hn g h01 h10]
  apply Submodule.smul_mem
  apply Submodule.smul_mem
  rw [←polynomialPieceBasis_coe (F := F) hn k z]
  exact (polynomialPieceBasis (F := F) hn k z).property

/-- Restriction of the genuine quotient action to its actual degree piece. -/
def diagonalPolynomialPieceMap (hn : 0<n) (k : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin 2) F) (h01 : g.val 0 1=0) (h10 : g.val 1 0=0) :
    polynomialPiece (F := F) hn k →ₗ[F] polynomialPiece (F := F) hn k :=
  (ColorAction.quotientEquiv g (fun i : Fin n ↦ MvPolynomial.X i)).toLinearMap.restrict
    (diagonal_preserves_polynomialPiece (F := F) hn k g h01 h10)

theorem diagonalPolynomialPieceMap_basis (hn : 0<n) (k : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin 2) F) (h01 : g.val 0 1=0) (h10 : g.val 1 0=0)
    (z : PolynomialBoxIndex (F := F) hn k) :
    diagonalPolynomialPieceMap (F := F) hn k g h01 h10 (polynomialPieceBasis (F := F) hn k z)=
      diagonalMonomialWeight (g.val 0 0) (g.val 1 1) hn z.val •
        polynomialPieceBasis (F := F) hn k z := by
  apply Subtype.ext
  change ColorAction.quotientEquiv g (fun i : Fin n ↦ MvPolynomial.X i)
      ((polynomialPieceBasis (F := F) hn k z : polynomialPiece (F := F) hn k) :
        StrictQuotient (data (F := F) hn).beta (data (F := F) hn).phi)=
    diagonalMonomialWeight (g.val 0 0) (g.val 1 1) hn z.val •
      ((polynomialPieceBasis (F := F) hn k z : polynomialPiece (F := F) hn k) :
        StrictQuotient (data (F := F) hn).beta (data (F := F) hn).phi)
  simp only [polynomialPieceBasis_coe]
  exact quotientEquiv_strictPaperBasis_diagonal hn g h01 h10 z.val

/-- Each coefficient of the graded character is the trace on the actual
homogeneous quotient space, with the exact full set of degree-k boxes. -/
theorem diagonal_polynomial_trace_eq_box_sum (hn : 0<n) (k : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin 2) F) (h01 : g.val 0 1=0) (h10 : g.val 1 0=0) :
    LinearMap.trace F (polynomialPiece (F := F) hn k) (diagonalPolynomialPieceMap (F := F) hn k g h01 h10)=
      ∑ z : PolynomialBoxIndex (F := F) hn k,
        diagonalMonomialWeight (g.val 0 0) (g.val 1 1) hn z.val := by
  rw [LinearMap.trace_eq_matrix_trace F (polynomialPieceBasis (F := F) hn k),Matrix.trace]
  apply Finset.sum_congr rfl
  intro z hz
  rw [Matrix.diag_apply,LinearMap.toMatrix_apply,
    diagonalPolynomialPieceMap_basis (F := F) hn k g h01 h10]
  let b := polynomialPieceBasis (F := F) hn k
  let c : F := diagonalMonomialWeight (g.val 0 0) (g.val 1 1) hn z.val
  change (b.repr (c • b z)) z=c
  have hs := LinearEquiv.map_smul b.repr c (b z)
  have he := congrArg (fun x : PolynomialBoxIndex (F := F) hn k →₀ F ↦ x z) hs
  simpa only [Module.Basis.repr_self,Finsupp.smul_apply,
    Finsupp.single_eq_same,smul_eq_mul,mul_one] using he

/-- The finite polynomial whose coefficients will be proved to be the
actual degree-piece traces. The verification is coefficientwise for every k. -/
def diagonalCharacterPolynomial (hn : 0<n) (u v : F) : Polynomial F :=
  ∑ z : StrictIndex (data (F := F) hn),
    Polynomial.C (diagonalMonomialWeight u v hn z)*
      Polynomial.X^boxPolynomialDegree (F := F) hn z

theorem diagonalCharacterPolynomial_coeff (hn : 0<n) (k : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin 2) F) (h01 : g.val 0 1=0) (h10 : g.val 1 0=0) :
    (diagonalCharacterPolynomial (F := F) hn (g.val 0 0) (g.val 1 1)).coeff k=
      LinearMap.trace F (polynomialPiece (F := F) hn k) (diagonalPolynomialPieceMap (F := F) hn k g h01 h10) := by
  rw [diagonal_polynomial_trace_eq_box_sum]
  simp only [diagonalCharacterPolynomial,Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul_X_pow]
  rw [←Finset.sum_subtype
    (Finset.univ.filter (fun z : StrictIndex (data (F := F) hn) ↦ boxPolynomialDegree (F := F) hn z=k))
    (by intro z; simp only [Finset.mem_filter,Finset.mem_univ,true_and])
    (diagonalMonomialWeight (g.val 0 0) (g.val 1 1) hn)]
  simp only [Finset.sum_filter,eq_comm]

/-- Exactly the multiplicity-vector polynomial printed in equation (22). -/
theorem diagonalCharacterPolynomial_eq_multiplicities (hn : 0<n) (u v : F) :
    diagonalCharacterPolynomial (F := F) hn u v=
      ∑ m : MultiplicityVector n,if Admissible m then
        ColorPaths.multiplicityBoxPolynomial (Polynomial.X : Polynomial F) m*
          (Polynomial.C u+Polynomial.C v)^ColorPaths.singleCount m*
          (Polynomial.C u*Polynomial.C v)^ColorPaths.doubleCount m else 0 := by
  rw [←strict_paper_q_color_sum (F := F) hn]
  apply Finset.sum_congr rfl
  intro z hz
  simp only [diagonalMonomialWeight,boxPolynomialDegree,map_mul,map_pow]
  ring

/-- Equation (22) as equality with traces of the original GL2 action on
every original polynomial-degree quotient space. -/
theorem equation_22_diagonal_trace (hn : 0<n) (k : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin 2) F) (h01 : g.val 0 1=0) (h10 : g.val 1 0=0) :
    LinearMap.trace F (polynomialPiece (F := F) hn k) (diagonalPolynomialPieceMap (F := F) hn k g h01 h10)=
      (∑ m : MultiplicityVector n,if Admissible m then
        ColorPaths.multiplicityBoxPolynomial (Polynomial.X : Polynomial F) m*
          (Polynomial.C (g.val 0 0)+Polynomial.C (g.val 1 1))^ColorPaths.singleCount m*
          (Polynomial.C (g.val 0 0)*Polynomial.C (g.val 1 1))^ColorPaths.doubleCount m else 0).coeff k := by
  rw [←diagonalCharacterPolynomial_coeff (F := F) hn k g h01 h10,
    diagonalCharacterPolynomial_eq_multiplicities]

end PaperVerification.Fermion.TypeA
