module

public import PaperVerification.FermionColorDiagonalTrace
public import TauCeti.RepresentationTheory.ClassicalGroups.UnitaryTrick

/-!
# Rationality of the genuine complex color action

Polynomiality is proved on the actual quotient matrix coefficients. On an
ordered exterior word, each generator is sent to a sum with two matrix-entry
coefficients. Induction on the word proves polynomiality after every linear
functional; the literal quotient basis then gives all action matrix entries.
The pinned TauCeti unitarian-trick theorem supplies complete reducibility.

No rationality, semisimplicity, or desired decomposition is assumed.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.Fermion.ColorAction

open TauCeti.Matrix.GeneralLinearGroup

variable {n : ℕ}

abbrev ComplexColorGroup := Matrix.GeneralLinearGroup (Fin 2) ℂ

def complexGenerator : OddIndex n → SuperRing ℂ n := Sum.elim (theta ℂ n) (xi ℂ n)

def complexWord (l : List (OddIndex n)) : SuperRing ℂ n :=
  (l.map complexGenerator).prod

/-- Fixed left multiplication is complex-linear, also in the noncommutative
polynomial/exterior algebra. -/
def complexLeftMultiply (x : SuperRing ℂ n) : SuperRing ℂ n →ₗ[ℂ] SuperRing ℂ n where
  toFun y := x*y
  map_add' y z := mul_add x y z
  map_smul' a y := mul_smul_comm a x y

/-- Multiplication by a fixed polynomial coefficient is complex-linear. -/
def complexPolynomialScale (p : PolynomialRing ℂ n) :
    SuperRing ℂ n →ₗ[ℂ] SuperRing ℂ n where
  toFun y := p • y
  map_add' y z := smul_add p y z
  map_smul' a y := smul_comm p a y

/-- Every linear functional on the image of every literal exterior word is a
polynomial function of the four matrix entries. -/
theorem complexWord_matrixCoefficient_polynomial (l : List (OddIndex n))
    (ell : SuperRing ℂ n →ₗ[ℂ] ℂ) :
    (fun g : ComplexColorGroup ↦ ell (ambient g.val (complexWord l))) ∈
      polynomialFunctions ℂ 2 := by
  induction l generalizing ell with
  | nil =>
      simp only [complexWord,List.map_nil,List.prod_nil,map_one]
      have hconst : algebraMap ℂ (ComplexColorGroup → ℂ) (ell 1) =
          (fun _ : ComplexColorGroup ↦ ell 1) := by
        funext g
        rfl
      rw [← hconst]
      exact (polynomialFunctions ℂ 2).algebraMap_mem (ell 1)
  | cons a l ih =>
      cases a with
      | inl i =>
          have h0 := (polynomialFunctions ℂ 2).mul_mem
            (entry_mem_polynomialFunctions (k := ℂ) 0 0)
            (ih (ell.comp (complexLeftMultiply (theta ℂ n i))))
          have h1 := (polynomialFunctions ℂ 2).mul_mem
            (entry_mem_polynomialFunctions (k := ℂ) 1 0)
            (ih (ell.comp (complexLeftMultiply (xi ℂ n i))))
          convert (polynomialFunctions ℂ 2).add_mem h0 h1 using 1
          funext g
          simp only [complexWord,List.map_cons,List.prod_cons,complexGenerator,Sum.elim_inl,
            map_mul,ambient_theta,MvPolynomial.C_eq_algebraMap,
            IsScalarTower.algebraMap_smul,add_mul,smul_mul_assoc,
            map_add,map_smul,smul_eq_mul,Pi.add_apply,Pi.mul_apply,LinearMap.comp_apply,
            complexLeftMultiply,LinearMap.coe_mk,AddHom.coe_mk]
      | inr i =>
          have h0 := (polynomialFunctions ℂ 2).mul_mem
            (entry_mem_polynomialFunctions (k := ℂ) 0 1)
            (ih (ell.comp (complexLeftMultiply (theta ℂ n i))))
          have h1 := (polynomialFunctions ℂ 2).mul_mem
            (entry_mem_polynomialFunctions (k := ℂ) 1 1)
            (ih (ell.comp (complexLeftMultiply (xi ℂ n i))))
          convert (polynomialFunctions ℂ 2).add_mem h0 h1 using 1
          funext g
          simp only [complexWord,List.map_cons,List.prod_cons,complexGenerator,Sum.elim_inr,
            map_mul,ambient_xi,MvPolynomial.C_eq_algebraMap,
            IsScalarTower.algebraMap_smul,add_mul,smul_mul_assoc,
            map_add,map_smul,smul_eq_mul,Pi.add_apply,Pi.mul_apply,LinearMap.comp_apply,
            complexLeftMultiply,LinearMap.coe_mk,AddHom.coe_mk]

/-- This applies to the paper's actual ordered theta/xi monomials, with their
original polynomial factors. -/
theorem boxMonomial_matrixCoefficient_polynomial
    (T S : Finset (Fin n)) (e : Fin n → ℕ)
    (ell : SuperRing ℂ n →ₗ[ℂ] ℂ) :
    (fun g : ComplexColorGroup ↦ ell (ambient g.val (boxMonomial T S e))) ∈
      polynomialFunctions ℂ 2 := by
  let p : PolynomialRing ℂ n := MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm e) 1
  have hw : complexWord (T.sort.map Sum.inl ++ S.sort.map Sum.inr)=
      (T.sort.map (theta ℂ n)).prod*(S.sort.map (xi ℂ n)).prod := by
    simp only [complexWord,List.map_append,List.prod_append,List.map_map,
      Function.comp_def,complexGenerator,Sum.elim_inl,Sum.elim_inr]
  have h := complexWord_matrixCoefficient_polynomial
    (T.sort.map Sum.inl ++ S.sort.map Sum.inr) (ell.comp (complexPolynomialScale p))
  simpa only [hw,boxMonomial,map_smul,LinearMap.comp_apply,complexPolynomialScale,
    LinearMap.coe_mk,AddHom.coe_mk,p] using h

end PaperVerification.Fermion.ColorAction

namespace PaperVerification.Fermion.TypeA

open TauCeti.Matrix.GeneralLinearGroup

variable {n : ℕ}

abbrev ComplexStrictQuotient (n : ℕ) :=
  StrictQuotient (fun _ : Fin n ↦ (1 : ℂ)) (fun i ↦ MvPolynomial.X i)

/-- The representation underlying the independently defined quotient
algebra action. -/
def complexColorRepresentation : Representation ℂ ColorAction.ComplexColorGroup
    (ComplexStrictQuotient n) where
  toFun g := (ColorAction.quotientEquiv g (fun i : Fin n ↦ MvPolynomial.X i)).toLinearMap
  map_one' := by
    rw [ColorAction.quotientEquiv_one]
    rfl
  map_mul' g h := by
    rw [ColorAction.quotientEquiv_mul]
    rfl

/-- Rationality is derived from the literal quotient basis and the actual
matrix action, without assuming a representation-theoretic splitting. -/
theorem complexColorRepresentation_polynomial (hn : 0<n) :
    TauCeti.IsPolynomialRep (complexColorRepresentation (n := n)) := by
  let B := strictPaperBasis (data (F := ℂ) hn)
  apply (TauCeti.isPolynomialRep_iff_forall_mem_polynomialFunctions B).mpr
  intro i j
  let q := (strictIdeal (fun _ : Fin n ↦ (1 : ℂ))
    (fun k : Fin n ↦ MvPolynomial.X k)).ringCon.mkₐ ℂ
  have h := ColorAction.boxMonomial_matrixCoefficient_polynomial
    j.val.1.1 j.val.1.2 j.val.2 ((B.coord i).comp q.toLinearMap)
  convert h using 1
  funext g
  rw [LinearMap.toMatrix_apply]
  change B.repr (ColorAction.quotientEquiv g (fun k : Fin n ↦ MvPolynomial.X k) (B j)) i=_
  rw [show B j=q (boxMonomial j.val.1.1 j.val.1.2 j.val.2) by
    exact strictPaperBasis_apply (data hn) j]
  rw [ColorAction.quotientEquiv_mk]
  rfl

/-- The full actual complex quotient is a semisimple GL2 representation.
The only hypotheses are the paper's positive number of indices. -/
theorem complexColorRepresentation_semisimple (hn : 0<n) :
    (complexColorRepresentation (n := n)).IsSemisimpleRepresentation :=
  (complexColorRepresentation_polynomial hn).isRationalRep.isSemisimpleRepresentation

end PaperVerification.Fermion.TypeA
