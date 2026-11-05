module

public import PaperVerification.FermionFiniteTensorUniversal
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Card

/-!
# Hilbert polynomials of the actual finite signed tensor grading

A finite homogeneous basis gives bases of the
already defined homogeneous submodules.  Consequently its enumerating
polynomial has the actual homogeneous dimensions as coefficients.  The
signed tensor product changes multiplication, but its underlying vector
space basis is the ordinary tensor basis; this proves multiplicativity for
the independent natural tensor grading.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical TensorProduct BigOperators

namespace PaperVerification.Fermion
namespace NGradedAlgebra

universe u
variable {F : Type u} [Field F]

structure FiniteHomogeneousBasis (A : NGradedAlgebra F) where
  Index : Type u
  [finiteIndex : Fintype Index]
  basis : Module.Basis Index F A.Carrier
  degree : Index → ℕ
  homogeneous : ∀ i,basis i∈A.part (degree i)

attribute [instance] FiniteHomogeneousBasis.finiteIndex

namespace FiniteHomogeneousBasis

variable {A B : NGradedAlgebra F}

theorem degreeSpan_eq_part (b : FiniteHomogeneousBasis A) (k : ℕ) :
    Submodule.span F (Set.range (fun i : {i // b.degree i=k} ↦ b.basis i.val))=
      A.part k := by
  have hr : Set.range (fun i : {i // b.degree i=k} ↦ b.basis i.val)=
      b.basis '' {i | b.degree i=k} := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨i.val,i.property,rfl⟩
    · rintro ⟨i,hi,rfl⟩
      exact ⟨⟨i,hi⟩,rfl⟩
  rw [hr]
  exact congrFun (basisDegreePart_eq_existing A.part b.basis b.degree b.homogeneous) k

/-- The basis is restricted to the actual pre-existing degree piece. -/
def pieceBasis (b : FiniteHomogeneousBasis A) (k : ℕ) :
    Module.Basis {i // b.degree i=k} F (A.part k) :=
  (Module.Basis.span (b.basis.linearIndependent.comp Subtype.val
    Subtype.val_injective)).map
      (LinearEquiv.ofEq _ _ (b.degreeSpan_eq_part k))

theorem finrank_part (b : FiniteHomogeneousBasis A) (k : ℕ) :
    Module.finrank F (A.part k)=Fintype.card {i // b.degree i=k} :=
  Module.finrank_eq_card_basis (b.pieceBasis k)

def hilbertPolynomial (b : FiniteHomogeneousBasis A) : Polynomial ℕ :=
  ∑ i,(Polynomial.X : Polynomial ℕ)^b.degree i

/-- Coefficients count dimensions of the original grading, not of a grading
transported from this finite indexing set. -/
theorem hilbertPolynomial_coeff (b : FiniteHomogeneousBasis A) (k : ℕ) :
    b.hilbertPolynomial.coeff k=Module.finrank F (A.part k) := by
  rw [b.finrank_part]
  simp only [hilbertPolynomial,Polynomial.finsetSum_coeff,Polynomial.coeff_X_pow]
  rw [Fintype.card_subtype]
  simpa only [eq_comm,Nat.cast_id] using
    (Finset.sum_boole (fun i : b.Index ↦ b.degree i=k) Finset.univ :
      (∑ i : b.Index,if b.degree i=k then (1 : ℕ) else 0)=
        (Finset.univ.filter (fun i : b.Index ↦ b.degree i=k)).card)

def scalar : FiniteHomogeneousBasis (NGradedAlgebra.scalar F) where
  Index := PUnit
  finiteIndex := inferInstance
  basis := Module.Basis.singleton PUnit F
  degree := fun _ ↦ 0
  homogeneous := by
    intro i
    change (Module.Basis.singleton PUnit F) i∈
      basisDegreePart (Module.Basis.singleton Unit F) (fun _ ↦ 0) 0
    apply Submodule.subset_span
    refine ⟨(),rfl,?_⟩
    simp

@[simp] theorem scalar_hilbertPolynomial :
    (scalar (F := F)).hilbertPolynomial=1 := by
  change (∑ _ : PUnit.{u+1},(Polynomial.X : Polynomial ℕ)^0)=1
  simp only [pow_zero,Finset.sum_const,Finset.card_univ,Fintype.card_punit,one_nsmul]

def tensor (b : FiniteHomogeneousBasis A) (c : FiniteHomogeneousBasis B) :
    FiniteHomogeneousBasis (NGradedAlgebra.tensor F A B) where
  Index := b.Index×c.Index
  finiteIndex := inferInstance
  basis := gradedTensorBasis A.part B.part b.basis c.basis
  degree := fun ij ↦ b.degree ij.1+c.degree ij.2
  homogeneous := by
    rintro ⟨i,j⟩
    change gradedTensorBasis A.part B.part b.basis c.basis (i,j) ∈
      naturalGradedTensorPart A.part B.part (b.degree i+c.degree j)
    rw [gradedTensorBasis_apply]
    exact naturalGradedTensorPart_tmul_mem A.part B.part
      (b.homogeneous i) (c.homogeneous j)

theorem tensor_hilbertPolynomial (b : FiniteHomogeneousBasis A)
    (c : FiniteHomogeneousBasis B) :
    (tensor b c).hilbertPolynomial=b.hilbertPolynomial*c.hilbertPolynomial := by
  change (∑ ij : b.Index×c.Index,
      (Polynomial.X : Polynomial ℕ)^(b.degree ij.1+c.degree ij.2))=
    (∑ i : b.Index,(Polynomial.X : Polynomial ℕ)^b.degree i)*
      (∑ j : c.Index,(Polynomial.X : Polynomial ℕ)^c.degree j)
  rw [Fintype.sum_prod_type,Fintype.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact pow_add _ _ _

def tensorFin : {n : ℕ} → (A : Fin n → NGradedAlgebra F) →
    (∀ i,FiniteHomogeneousBasis (A i)) →
      FiniteHomogeneousBasis (NGradedAlgebra.tensorFin A)
  | 0,_,_ => scalar
  | n+1,A,b => tensor (b 0)
      (tensorFin (fun i : Fin n ↦ A i.succ) (fun i ↦ b i.succ))

theorem tensorFin_hilbertPolynomial {n : ℕ} (A : Fin n → NGradedAlgebra F)
    (b : ∀ i,FiniteHomogeneousBasis (A i)) :
    (tensorFin A b).hilbertPolynomial=∏ i,(b i).hilbertPolynomial := by
  induction n with
  | zero => simp [tensorFin]
  | succ n ih =>
      change (tensor (b 0)
        (tensorFin (fun i : Fin n ↦ A i.succ) (fun i ↦ b i.succ))).hilbertPolynomial=_
      rw [tensor_hilbertPolynomial,Fin.prod_univ_succ]
      rw [ih]

/-- The product formula concerns the independently defined natural degree
pieces of the genuine signed tensor algebra. -/
theorem tensorFin_finrank_part {n : ℕ} (A : Fin n → NGradedAlgebra F)
    (b : ∀ i,FiniteHomogeneousBasis (A i)) (k : ℕ) :
    Module.finrank F ((NGradedAlgebra.tensorFin A).part k)=
      (∏ i,(b i).hilbertPolynomial).coeff k := by
  rw [←(tensorFin A b).hilbertPolynomial_coeff,tensorFin_hilbertPolynomial]

end FiniteHomogeneousBasis
end NGradedAlgebra
end PaperVerification.Fermion
