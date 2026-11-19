module
public import Mathlib.Combinatorics.Young.YoungDiagram
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Finset.Powerset
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Every elementary-parameter fiber -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Finset MvPolynomial
open scoped BigOperators TensorProduct Polynomial Classical

namespace HigherSpecht

/-- Literal source definition of PolynomialRing. -/
abbrev PolynomialRing (n : ℕ) (R : Type*) [CommRing R] := MvPolynomial (Fin n) R

section PolynomialDefinitions
attribute [local instance] Classical.propDecidable
variable {R : Type*} [CommRing R]

/-- The elementary symmetric polynomial in precisely the variables in Y. -/
def elementaryOn {n : ℕ} (Y : Finset (Fin n)) (d : ℕ) : PolynomialRing n R :=
  ∑ A ∈ Y.powersetCard d, ∏ i ∈ A, X i

/-- Conjugate tail, using zero-based column indices.  The interval
`[n-m,n)` is the printed interval `n-m+1,…,n`. -/
def conjugateTail (n : ℕ) (μ : YoungDiagram) (m : ℕ) : ℕ :=
  ∑ j ∈ Finset.Ico (n - m) n, μ.colLen j

/-- A generator of the untruncated Griffin ideal.  The comparison is made in
the integers so that no natural subtraction can change its mathematical content. -/
def IsElementaryGenerator (n : ℕ) (μ : YoungDiagram)
    (p : PolynomialRing n R) : Prop :=
  ∃ (Y : Finset (Fin n)) (d : ℕ), 0 < d ∧ d ≤ Y.card ∧
    (Y.card : ℤ) - (conjugateTail n μ Y.card : ℤ) < (d : ℤ) ∧
    p = elementaryOn Y d

/-- Literal source definition of untruncatedIdeal. -/
def untruncatedIdeal (R : Type*) [CommRing R] (n : ℕ) (μ : YoungDiagram) :
    Ideal (PolynomialRing n R) := Ideal.span {p | IsElementaryGenerator n μ p}

end PolynomialDefinitions

/-- Literal source definition of springerIdeal. -/
def springerIdeal (R : Type*) [CommRing R] (μ : YoungDiagram) :
    Ideal (PolynomialRing μ.card R) := untruncatedIdeal R μ.card μ

/-- Literal source definition of SpringerRing. -/
abbrev SpringerRing (R : Type*) [CommRing R] (μ : YoungDiagram) :=
  PolynomialRing μ.card R ⧸ springerIdeal R μ

def adjoinOnes (μ : YoungDiagram) (m : ℕ) : YoungDiagram where
  cells := μ.cells ∪ (Finset.range (μ.colLen 0 + m) ×ˢ {0})
  isLowerSet := by
    rintro ⟨a, b⟩ ⟨c, d⟩ ⟨hac, hbd⟩ h
    rcases Finset.mem_union.mp h with h | h
    · exact Finset.mem_union_left _ (μ.isLowerSet ⟨hac, hbd⟩ h)
    · apply Finset.mem_union_right
      simp only [Finset.mem_product, Finset.mem_range, Finset.mem_singleton] at h ⊢
      exact ⟨hac.trans_lt h.1, by omega⟩

def columnPartition (k : ℕ) : YoungDiagram := adjoinOnes ⊥ k

def parameterFiberIdeal (R : Type*) [CommRing R] (n : ℕ) (lam : YoungDiagram)
    (m : ℕ) (a : Fin m → R) : Ideal (PolynomialRing n R) :=
  untruncatedIdeal R n lam ⊔
    Ideal.span (Set.range fun i : Fin m =>
      elementaryOn (Finset.univ : Finset (Fin n)) (i.val + 1) - MvPolynomial.C (a i))

abbrev ParameterFiber (R : Type*) [CommRing R] (n : ℕ) (lam : YoungDiagram)
    (m : ℕ) (a : Fin m → R) :=
  PolynomialRing n R ⧸ parameterFiberIdeal R n lam m a

section RootData
variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]

def parameterPolynomial {m : ℕ} (a : Fin m → R) : Polynomial R :=
  Polynomial.X ^ m + ∑ j : Fin m,
    Polynomial.C ((-1) ^ (m - j.val) * a ⟨m - j.val - 1, by omega⟩) *
      Polynomial.X ^ j.val

abbrev PrescribedRootAssignments (n : ℕ) (r : ι → ℕ) :=
  {f : Fin n → ι // ∀ i, Fintype.card {j : Fin n // f j = i} = r i}

def splitRootMultiplicities (lam : YoungDiagram) (r0 : ℕ) (r : ι → ℕ) : Option ι → ℕ :=
  fun i => i.elim (lam.card + r0) r

def splitRootParameter (r0 : ℕ) (c : ι → R) (r : ι → ℕ) : R[X] :=
  Polynomial.X ^ r0 * ∏ i : ι, (Polynomial.X - Polynomial.C (c i)) ^ r i

end RootData

section CanonicalRoots
variable {L : Type*} [Field L]

def nonzeroRootSet (Q : L[X]) : Finset L := Q.roots.toFinset.erase 0

def canonicalRootMultiplicity (Q : L[X]) : nonzeroRootSet Q → ℕ :=
  fun i => Q.roots.count i.val

end CanonicalRoots

section SplitFiber
variable {n m : ℕ} {ι : Type*} [Fintype ι]

theorem theorem_7_1_parameter_fiber_exists
    (K : Type*) [Field K] (lam : YoungDiagram) (a : Fin m → K)
    (hsize : lam.card + m = n) (r0 : ℕ)
    (c : ι → K) (hc : Function.Injective c) (hcz : ∀ i, c i ≠ 0)
    (r : ι → ℕ) (hr : ∀ i, 0 < r i)
    (hfactor : parameterPolynomial a = splitRootParameter r0 c r) :
    Nonempty (ParameterFiber K n lam m a ≃ₐ[K]
      ∀ _f : PrescribedRootAssignments n (splitRootMultiplicities lam r0 r),
        ⨂[K] i : Option ι,
          SpringerRing K (i.elim (adjoinOnes lam r0) (fun j => columnPartition (r j)))) := by sorry

end SplitFiber

theorem theorem_7_1_algebraicClosure_exists
    (K : Type*) [Field K] {n m : ℕ}
    (lam : YoungDiagram) (a : Fin m → K) (hsize : lam.card + m = n) :
    let L := AlgebraicClosure K
    let Q := parameterPolynomial (fun i => algebraMap K L (a i))
    Nonempty (L ⊗[K] ParameterFiber K n lam m a ≃ₐ[L]
      ∀ _f : PrescribedRootAssignments n
          (splitRootMultiplicities lam (Q.roots.count 0) (canonicalRootMultiplicity Q)),
        ⨂[L] i : Option (nonzeroRootSet Q),
          SpringerRing L (i.elim (adjoinOnes lam (Q.roots.count 0))
            (fun j => columnPartition (canonicalRootMultiplicity Q j)))) := by sorry

theorem theorem_7_1_algebraicClosure_number_of_factors
    (K : Type*) [Field K] {n m : ℕ}
    (lam : YoungDiagram) (a : Fin m → K) (hsize : lam.card + m = n) :
    let Q := parameterPolynomial (fun i => algebraMap K (AlgebraicClosure K) (a i))
    Fintype.card (PrescribedRootAssignments n
        (splitRootMultiplicities lam (Q.roots.count 0) (canonicalRootMultiplicity Q))) =
      n.factorial / ((lam.card + Q.roots.count 0).factorial *
        ∏ i : nonzeroRootSet Q, (canonicalRootMultiplicity Q i).factorial) := by sorry

end HigherSpecht
