module

public import PaperVerification.FermionSuperMonomialBasics
public import PaperVerification.FermionExteriorWordGrading
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# The physical polynomial and two exterior degrees

The components are defined in the original
polynomial tensor exterior algebra, before taking any quotient or selecting
normal forms. The product law is proved from the actual exterior shuffle
formula. A later homogeneous quotient can therefore use these components
without transporting its grading from the proposed quotient basis.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators TensorProduct

namespace PaperVerification.Fermion

section Ambient

variable {R Γ : Type*} [CommRing R] [AddCommMonoid Γ] [DecidableEq Γ]
  {n : ℕ} [LinearOrder (OddIndex n)]

/-- Polynomial weight and independent exterior multidegree of a genuine
ambient monomial. -/
def polynomialExteriorDegree (w : Fin n → ℕ) (v : OddIndex n → Γ)
    (z : SuperMonomialIndex n) : ℕ×Γ :=
  (Finsupp.weight w z.1,exteriorWordDegree v z.2)

def polynomialExteriorPart (w : Fin n → ℕ) (v : OddIndex n → Γ)
    (g : ℕ×Γ) : Submodule R (SuperRing R n) :=
  basisDegreePart superMonomialBasis (polynomialExteriorDegree w v) g

theorem polynomialExteriorPart_basis (w : Fin n → ℕ) (v : OddIndex n → Γ)
    (z : SuperMonomialIndex n) :
    superMonomialBasis (K := R) z∈
      polynomialExteriorPart w v (polynomialExteriorDegree w v z) :=
  Submodule.subset_span ⟨z,rfl,rfl⟩

theorem polynomialExteriorPart_one (w : Fin n → ℕ) (v : OddIndex n → Γ) :
    (1 : SuperRing R n)∈polynomialExteriorPart w v 0 := by
  have hb : superMonomialBasis (K := R) (n := n) (0,∅)=1 := by
    rw [superMonomialBasis_apply,Module.Basis.exteriorAlgebra_eq_prod_map_sort]
    simp [Algebra.TensorProduct.one_def]
  have hd : polynomialExteriorDegree w v (0,∅)=0 := by
    simp only [polynomialExteriorDegree,map_zero,exteriorWordDegree,Finset.sum_empty]
    rfl
  simpa only [hd,hb] using polynomialExteriorPart_basis (R := R) w v (0,∅)

theorem polynomialExteriorPart_basis_mul (w : Fin n → ℕ) (v : OddIndex n → Γ)
    (x y : SuperMonomialIndex n) :
    superMonomialBasis (K := R) x*superMonomialBasis y∈
      polynomialExteriorPart w v
        (polynomialExteriorDegree w v x+polynomialExteriorDegree w v y) := by
  rcases x with ⟨e,S⟩
  rcases y with ⟨f,T⟩
  rw [superMonomialBasis_apply,superMonomialBasis_apply,
    Algebra.TensorProduct.tmul_mul_tmul,MvPolynomial.monomial_mul,one_mul]
  by_cases h : Disjoint S T
  · let S' : Set.powersetCard (OddIndex n) S.card := ⟨S,rfl⟩
    let T' : Set.powersetCard (OddIndex n) T.card := ⟨T,rfl⟩
    let a : R := ((Set.powersetCard.permOfDisjoint (s := S') (t := T') h).sign : ℤ)
    have hp :
        (Pi.basisFun R (OddIndex n)).ExteriorAlgebra S*
          (Pi.basisFun R (OddIndex n)).ExteriorAlgebra T=
        a • (Pi.basisFun R (OddIndex n)).ExteriorAlgebra (S.disjUnion T h) := by
      simpa only [a,Units.smul_def,Int.cast_smul_eq_zsmul,Set.powersetCard.coe_disjUnion]
        using ExteriorAlgebra.basis_mul_of_disjoint (Pi.basisFun R (OddIndex n)) S' T' h
    rw [hp,TensorProduct.tmul_smul]
    apply Submodule.smul_mem
    have hd : polynomialExteriorDegree w v (e+f,S.disjUnion T h)=
        polynomialExteriorDegree w v (e,S)+polynomialExteriorDegree w v (f,T) := by
      apply Prod.ext
      · exact map_add (Finsupp.weight w) e f
      · exact Finset.sum_disjUnion h
    rw [←hd]
    simpa only [superMonomialBasis_apply] using
      polynomialExteriorPart_basis (R := R) w v (e+f,S.disjUnion T h)
  · rw [ExteriorAlgebra.basis_mul_of_not_disjoint (Pi.basisFun R (OddIndex n))
      (⟨S,rfl⟩ : Set.powersetCard (OddIndex n) S.card)
      (⟨T,rfl⟩ : Set.powersetCard (OddIndex n) T.card) h,
      TensorProduct.tmul_zero]
    exact Submodule.zero_mem _

/-- An actual homogeneous polynomial times an actual exterior word belongs
to the corresponding physical ambient component. -/
theorem polynomialExteriorPart_tmul_word (w : Fin n → ℕ) (v : OddIndex n → Γ)
    (p : PolynomialRing R n) (k : ℕ) (hp : p.IsWeightedHomogeneous w k)
    (T : Finset (OddIndex n)) :
    p ⊗ₜ[R] (Pi.basisFun R (OddIndex n)).ExteriorAlgebra T∈
      polynomialExteriorPart w v (k,exteriorWordDegree v T) := by
  rw [MvPolynomial.as_sum p,TensorProduct.sum_tmul]
  apply Submodule.sum_mem
  intro e he
  have hc : p.coeff e≠0 := MvPolynomial.mem_support_iff.mp he
  have hm : MvPolynomial.monomial e (p.coeff e)=
      p.coeff e • (MvPolynomial.monomial e (1 : R) : PolynomialRing R n) := by
    simp only [MvPolynomial.smul_monomial,smul_eq_mul,mul_one]
  rw [hm,←TensorProduct.smul_tmul']
  apply Submodule.smul_mem
  have hd : polynomialExteriorDegree w v (e,T)=(k,exteriorWordDegree v T) :=
    Prod.ext (hp hc) rfl
  rw [←hd]
  simpa only [superMonomialBasis_apply] using
    polynomialExteriorPart_basis (R := R) w v (e,T)

set_option maxHeartbeats 800000 in
def polynomialExteriorGrading (w : Fin n → ℕ) (v : OddIndex n → Γ) :
    GradedAlgebra (polynomialExteriorPart (R := R) w v) :=
  basisDegreeGradedAlgebra (superMonomialBasis (K := R) (n := n))
    (polynomialExteriorDegree w v)
    (polynomialExteriorPart_one (R := R) w v)
    (polynomialExteriorPart_basis_mul (R := R) w v)

end Ambient

/-- The three coordinates count the actual polynomial degree, theta degree,
and xi degree. This definition involves no quotient or proposed quotient basis. -/
def physicalOddBidegree {n : ℕ} : OddIndex n → ℕ×ℕ :=
  Sum.elim (fun _ ↦ (1,0)) (fun _ ↦ (0,1))

def physicalSuperDegree {n : ℕ} (z : SuperMonomialIndex n) : ℕ×(ℕ×ℕ) :=
  polynomialExteriorDegree (fun _ ↦ 1) physicalOddBidegree z

def physicalSuperPart {R : Type*} [CommRing R] {n : ℕ}
    [LinearOrder (OddIndex n)] (g : ℕ×(ℕ×ℕ)) : Submodule R (SuperRing R n) :=
  polynomialExteriorPart (fun _ ↦ 1) physicalOddBidegree g

def physicalSuperGrading {R : Type*} [CommRing R] {n : ℕ}
    [LinearOrder (OddIndex n)] : GradedAlgebra (physicalSuperPart (R := R) (n := n)) :=
  polynomialExteriorGrading (fun _ ↦ 1) physicalOddBidegree

section ActualPieces

variable {R A I Γ : Type*} [CommRing R] [Ring A] [Algebra R A]
  [AddMonoid Γ] [DecidableEq Γ]

/-- A homogeneous quotient basis restricts to the independently defined
actual degree piece. No grading is defined using the quotient basis. -/
def actualMultigradedPieceBasis (part : Γ → Submodule R A) [GradedAlgebra part]
    (b : Module.Basis I R A) (degree : I → Γ)
    (hb : ∀ i,b i∈part (degree i)) (g : Γ) :
    Module.Basis {i // degree i=g} R (part g) := by
  have hr : Set.range (fun i : {i // degree i=g} ↦ b i.val)=
      b '' {i | degree i=g} := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨i.val,i.property,rfl⟩
    · rintro ⟨i,hi,rfl⟩
      exact ⟨⟨i,hi⟩,rfl⟩
  have hs : Submodule.span R (Set.range (fun i : {i // degree i=g} ↦ b i.val))=part g := by
    rw [hr]
    exact congrFun (basisDegreePart_eq_existing part b degree hb) g
  exact (Module.Basis.span (b.linearIndependent.comp Subtype.val Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ hs)

end ActualPieces

section Dimensions

variable {F A I Γ : Type*} [Field F] [Ring A] [Algebra F A]
  [AddMonoid Γ] [DecidableEq Γ] [Fintype I]

theorem actualMultigradedPiece_finrank (part : Γ → Submodule F A) [GradedAlgebra part]
    (b : Module.Basis I F A) (degree : I → Γ)
    (hb : ∀ i,b i∈part (degree i)) (g : Γ) :
    Module.finrank F (part g)=Fintype.card {i // degree i=g} :=
  Module.finrank_eq_card_basis (actualMultigradedPieceBasis part b degree hb g)

end Dimensions
end PaperVerification.Fermion
