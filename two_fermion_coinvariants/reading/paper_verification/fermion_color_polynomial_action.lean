module

public import PaperVerification.FermionColorGradedTrace
public import Mathlib.RepresentationTheory.Character

/-!
# The full GL2 action on every actual polynomial-degree piece

All color changes preserve polynomial degree before taking the quotient.
The degree pieces are the independently defined homogeneous images, and
restriction of the genuine quotient action gives their representations.
Every coefficient of the graded character is a trace of this genuine full
group representation. Rationality and semisimplicity are developed separately.

-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators TensorProduct

namespace PaperVerification.Fermion.TypeA

open Exterior
variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

/-- The original total quotient carries the actual color action over every
characteristic-zero coefficient field. This definition does not use a
choice of basis, a trace formula, or a representation decomposition. -/
def quotientColorRepresentation :
    Representation F (Matrix.GeneralLinearGroup (Fin 2) F)
      (StrictQuotient (fun _ : Fin n ↦ (1 : F)) (fun i ↦ MvPolynomial.X i)) where
  toFun g := (ColorAction.quotientEquiv g (fun i : Fin n ↦ MvPolynomial.X i)).toLinearMap
  map_one' := by
    rw [ColorAction.quotientEquiv_one]
    rfl
  map_mul' g h := by
    rw [ColorAction.quotientEquiv_mul]
    rfl

/-- Finiteness follows from the literal strict basis, with all its original
parameters specialized to type A. -/
theorem quotientColor_finite (hn : 0<n) :
    Module.Finite F
      (StrictQuotient (fun _ : Fin n ↦ (1 : F)) (fun i ↦ MvPolynomial.X i)) :=
  Module.Finite.of_basis (strictPaperBasis (data (F := F) hn))

/-- Equation (23) for the character of the actual total GL2 representation,
with the original permutation ascent and descent statistics. -/
theorem equation_23_character (hn : 0<n)
    (g : Matrix.GeneralLinearGroup (Fin 2) F) (h01 : g.val 0 1=0) (h10 : g.val 1 0=0) :
    Representation.character
      (V := StrictQuotient (fun _ : Fin n ↦ (1 : F)) (fun i ↦ MvPolynomial.X i))
      (quotientColorRepresentation (F := F) (n := n)) g=
      Eulerian.permutationPolynomial n (1+g.val 0 0) (1+g.val 1 1) :=
  diagonal_trace_eq_eulerian hn g h01 h10

local instance colorPolynomialActionOddOrder : LinearOrder (OddIndex n) :=
  LinearOrder.lift' modeRank modeRank_injective

/-- The polynomial exponent is unchanged in every term of the color image. -/
theorem ambient_superMonomial_expansion (A : ColorAction.ColorMatrix F)
    (a : Fin n →₀ ℕ) (T : Finset (OddIndex n)) :
    ColorAction.ambient A (superMonomialBasis (K := F) (a,T))=
      ∑ S : Finset (OddIndex n),
        ((Pi.basisFun F (OddIndex n)).ExteriorAlgebra.repr
          (ExteriorAlgebra.map (ColorAction.linear A)
            ((Pi.basisFun F (OddIndex n)).ExteriorAlgebra T))) S •
              superMonomialBasis (K := F) (a,S) := by
  let E := (Pi.basisFun F (OddIndex n)).ExteriorAlgebra
  rw [superMonomialBasis_apply]
  change MvPolynomial.monomial a (1 : F) ⊗ₜ[F]
      ExteriorAlgebra.map (ColorAction.linear A) (E T)=_
  conv_lhs => rw [←E.sum_repr (ExteriorAlgebra.map (ColorAction.linear A) (E T))]
  simp only [TensorProduct.tmul_sum,TensorProduct.tmul_smul,superMonomialBasis_apply,E]

/-- Polynomial homogeneity is preserved on the ambient algebra, independently
of the quotient normal form or its basis. -/
theorem ambient_preserves_polynomial_homogeneous (A : ColorAction.ColorMatrix F)
    (k : ℕ) (x : SuperRing F n)
    (hx : BasisFiltered.Homogeneous (superMonomialBasis (K := F)) polynomialDegree k x) :
    BasisFiltered.Homogeneous (superMonomialBasis (K := F)) polynomialDegree k
      (ColorAction.ambient A x) := by
  let b := superMonomialBasis (K := F) (n := n)
  let H := BasisFiltered.homogeneousPiece b polynomialDegree k
  let f : SuperRing F n →ₗ[F] SuperRing F n :=
    ((ColorAction.ambient (n := n) A).restrictScalars F).toLinearMap
  change f x∈H
  rw [←b.linearCombination_repr x,Finsupp.linearCombination_apply,Finsupp.sum,map_sum]
  apply Submodule.sum_mem
  intro z hz
  rw [map_smul]
  apply Submodule.smul_mem
  change ColorAction.ambient A (superMonomialBasis z)∈H
  rw [ambient_superMonomial_expansion]
  apply Submodule.sum_mem
  intro S hS
  apply Submodule.smul_mem
  have hd := hx z (Finsupp.mem_support_iff.mp hz)
  change BasisFiltered.Homogeneous (superMonomialBasis (K := F)) polynomialDegree k
    (superMonomialBasis (z.1,S))
  have h := BasisFiltered.homogeneous_basis (superMonomialBasis (K := F))
    polynomialDegree (z.1,S)
  exact (show polynomialDegree (z.1,S)=k from hd) ▸ h

/-- Every GL2 element, not only the diagonal torus, preserves the actual
homogeneous quotient image. -/
theorem color_preserves_polynomialPiece (hn : 0<n) (k : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin 2) F)
    (x : StrictQuotient (data (F := F) hn).beta (data (F := F) hn).phi)
    (hx : x∈polynomialPiece (F := F) hn k) :
    ColorAction.quotientEquiv g (fun i : Fin n ↦ MvPolynomial.X i) x∈
      polynomialPiece (F := F) hn k := by
  change x ∈ (BasisFiltered.homogeneousPiece (superMonomialBasis (K := F))
    polynomialDegree k).map
      ((strictIdeal (data (F := F) hn).beta (data (F := F) hn).phi).ringCon.mkₐ F).toLinearMap at hx
  obtain ⟨y,hy,rfl⟩ := Submodule.mem_map.mp hx
  apply Submodule.mem_map.mpr
  refine ⟨ColorAction.ambient g.val y,
    ambient_preserves_polynomial_homogeneous g.val k y hy,?_⟩
  exact (ColorAction.quotientEquiv_mk g (fun i : Fin n ↦ MvPolynomial.X i) y).symm

/-- Restriction of the full genuine group action to each original degree. -/
def polynomialPieceColorRepresentation (hn : 0<n) (k : ℕ) :
    Representation F (Matrix.GeneralLinearGroup (Fin 2) F) (polynomialPiece (F := F) hn k) where
  toFun g := (ColorAction.quotientEquiv g (fun i : Fin n ↦ MvPolynomial.X i)).toLinearMap.restrict
    (color_preserves_polynomialPiece (F := F) hn k g)
  map_one' := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change ColorAction.quotientEquiv 1 (fun i : Fin n ↦ MvPolynomial.X i)
      (x : StrictQuotient (fun _ : Fin n ↦ (1 : F)) (fun i ↦ MvPolynomial.X i))=
        (x : StrictQuotient (fun _ : Fin n ↦ (1 : F)) (fun i ↦ MvPolynomial.X i))
    rw [ColorAction.quotientEquiv_one]
    rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change ColorAction.quotientEquiv (g*h) (fun i : Fin n ↦ MvPolynomial.X i)
      (x : StrictQuotient (fun _ : Fin n ↦ (1 : F)) (fun i ↦ MvPolynomial.X i))=
      ColorAction.quotientEquiv g (fun i : Fin n ↦ MvPolynomial.X i)
        (ColorAction.quotientEquiv h (fun i : Fin n ↦ MvPolynomial.X i)
          (x : StrictQuotient (fun _ : Fin n ↦ (1 : F)) (fun i ↦ MvPolynomial.X i)))
    rw [ColorAction.quotientEquiv_mul,AlgEquiv.mul_apply]

/-- The map used in the coefficientwise character calculation is literally
this representation evaluated on the diagonal element. -/
theorem polynomialPieceColorRepresentation_diagonal (hn : 0<n) (k : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin 2) F) (h01 : g.val 0 1=0) (h10 : g.val 1 0=0) :
    polynomialPieceColorRepresentation (F := F) hn k g=diagonalPolynomialPieceMap (F := F) hn k g h01 h10 := by
  apply LinearMap.ext
  intro x
  rfl

/-- Finiteness of the actual piece follows from its proved degree-selected
basis; it is not an additional premise of the character formula. -/
instance polynomialPiece_finite (hn : 0<n) (k : ℕ) :
    Module.Finite F (polynomialPiece (F := F) hn k) :=
  Module.Finite.of_basis (polynomialPieceBasis (F := F) hn k)

/-- Equation (22), coefficient by coefficient, for the character of the
actual full GL2 representation on each original polynomial degree. -/
theorem equation_22_character (hn : 0<n) (k : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin 2) F) (h01 : g.val 0 1=0) (h10 : g.val 1 0=0) :
    Representation.character (V := polynomialPiece (F := F) hn k)
      (polynomialPieceColorRepresentation (F := F) hn k) g=
      (∑ m : MultiplicityVector n,if Admissible m then
        ColorPaths.multiplicityBoxPolynomial (Polynomial.X : Polynomial F) m*
          (Polynomial.C (g.val 0 0)+Polynomial.C (g.val 1 1))^ColorPaths.singleCount m*
          (Polynomial.C (g.val 0 0)*Polynomial.C (g.val 1 1))^ColorPaths.doubleCount m else 0).coeff k := by
  rw [Representation.character,polynomialPieceColorRepresentation_diagonal hn k g h01 h10]
  exact equation_22_diagonal_trace hn k g h01 h10

end PaperVerification.Fermion.TypeA
