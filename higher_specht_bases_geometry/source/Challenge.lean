module
public import Mathlib.Combinatorics.Young.YoungDiagram
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Finset.Powerset
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.RingTheory.Ideal.IsPrimary
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.FieldTheory.Separable

/-! # Primary components and étale fibers -/

@[expose] public section

universe palomarFiberCoeffU
noncomputable section
set_option autoImplicit false
open Finset MvPolynomial
open scoped BigOperators TensorProduct Polynomial

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
def springerIdeal (R : Type palomarFiberCoeffU) [CommRing R] (μ : YoungDiagram) :
    Ideal (PolynomialRing μ.card R) := untruncatedIdeal R μ.card μ

/-- Literal source definition of SpringerRing. -/
abbrev SpringerRing (R : Type palomarFiberCoeffU) [CommRing R] (μ : YoungDiagram) :=
  PolynomialRing μ.card R ⧸ springerIdeal R μ

/-- Stable name for the commutative ideal's two-sidedness in quotient data. -/
theorem untruncatedIdeal_isTwoSided (R : Type palomarFiberCoeffU) [CommRing R]
    (n : ℕ) (lam : YoungDiagram) : (untruncatedIdeal R n lam).IsTwoSided :=
  Ideal.instIsTwoSided_1 (untruncatedIdeal R n lam)

attribute [instance 1200] untruncatedIdeal_isTwoSided

abbrev UntruncatedRing (R : Type palomarFiberCoeffU) [CommRing R] (n : ℕ) (μ : YoungDiagram) :=
  PolynomialRing n R ⧸ untruncatedIdeal R n μ

def elementaryParameterClasses (K : Type*) [CommRing K] (n : ℕ) (lam : YoungDiagram) :
    Fin (n - lam.card) → UntruncatedRing K n lam :=
  fun j => Ideal.Quotient.mk (untruncatedIdeal K n lam)
    (MvPolynomial.esymm (Fin n) K (j.val + 1))

abbrev ElementaryParameterRing (K : Type*) [CommRing K] (n : ℕ) (lam : YoungDiagram) :=
  MvPolynomial (Fin (n - lam.card)) K

noncomputable instance untruncatedParameterAlgebra (K : Type*) [CommRing K]
    (n : ℕ) (lam : YoungDiagram) :
    Algebra (ElementaryParameterRing K n lam) (UntruncatedRing K n lam) :=
  (MvPolynomial.aeval (elementaryParameterClasses K n lam)).toRingHom.toAlgebra

def parameterFiberIdeal (R : Type palomarFiberCoeffU) [CommRing R] (n : ℕ) (lam : YoungDiagram)
    (m : ℕ) (a : Fin m → R) : Ideal (PolynomialRing n R) :=
  untruncatedIdeal R n lam ⊔
    Ideal.span (Set.range fun i : Fin m =>
      elementaryOn (Finset.univ : Finset (Fin n)) (i.val + 1) - MvPolynomial.C (a i))

abbrev ParameterFiber (R : Type palomarFiberCoeffU) [CommRing R] (n : ℕ) (lam : YoungDiagram)
    (m : ℕ) (a : Fin m → R) :=
  PolynomialRing n R ⧸ parameterFiberIdeal R n lam m a

section ParameterPolynomial
variable {R : Type*} [CommRing R]

theorem parameterPolynomial_index_lt {m : ℕ} (j : Fin m) :
    m - j.val - 1 < m := by omega

def parameterPolynomial {m : ℕ} (a : Fin m → R) : Polynomial R :=
  Polynomial.X ^ m + ∑ j : Fin m,
    Polynomial.C ((-1) ^ (m - j.val) * a ⟨m - j.val - 1, parameterPolynomial_index_lt j⟩) *
      Polynomial.X ^ j.val

end ParameterPolynomial

section Components
variable {n : ℕ}

def columnTail (μ : YoungDiagram) (h : ℕ) : ℕ :=
  (μ.cells.filter fun c => h ≤ c.2).card

def blockSpringerIdeal (R : Type palomarFiberCoeffU) [CommRing R] (A : Finset (Fin n))
    (mu : YoungDiagram) : Ideal (PolynomialRing n R) :=
  Ideal.span {p | ∃ (Y : Finset (Fin n)) (d : ℕ), Y ⊆ A ∧ d ≤ Y.card ∧
    (Y.card : ℤ) - (columnTail mu (A.card - Y.card) : ℤ) < (d : ℤ) ∧
    p = elementaryOn Y d}

abbrev SpringerCoordinateBlocks (n : ℕ) (mu : YoungDiagram) :=
  {A : Finset (Fin n) // A.card = mu.card}

def springerComponentIntersection (R : Type palomarFiberCoeffU) [CommRing R] (n : ℕ)
    (mu : YoungDiagram) : Ideal (PolynomialRing n R) :=
  ⨅ A : SpringerCoordinateBlocks n mu, blockSpringerIdeal R A.val mu

def coordinateIdeal (R : Type palomarFiberCoeffU) [CommRing R] (A : Finset (Fin n)) :
    Ideal (PolynomialRing n R) :=
  Ideal.span (MvPolynomial.X '' (A : Set (Fin n)))

end Components

section ComponentTheorems
variable {R : Type*} [CommRing R] {n : ℕ} {mu : YoungDiagram}

theorem proposition_7_3_primary_decomposition [IsDomain R]
    (hn : mu.card ≤ n) :
    untruncatedIdeal R n mu = springerComponentIntersection R n mu ∧
      (∀ A : SpringerCoordinateBlocks n mu,
        (blockSpringerIdeal R A.val mu).IsPrimary ∧
        (blockSpringerIdeal R A.val mu).radical = coordinateIdeal R A.val) ∧
      (∀ A : SpringerCoordinateBlocks n mu,
        ∃ p : PolynomialRing n R,
          (∀ B : SpringerCoordinateBlocks n mu, B ≠ A →
            p ∈ blockSpringerIdeal R B.val mu) ∧
          p ∉ blockSpringerIdeal R A.val mu) := by sorry

theorem untruncated_isReduced_iff [IsDomain R] (hn : mu.card ≤ n) :
    IsReduced (UntruncatedRing R n mu) ↔ mu.colLen 0 ≤ 1 := by sorry

end ComponentTheorems

section Fibers
variable {K : Type*} [Field K] {n m : ℕ}

theorem parameterFiber_etale_iff_polynomial
    (lam : YoungDiagram) (a : Fin m → K) (hsize : lam.card + m = n) :
    Algebra.Etale K (ParameterFiber K n lam m a) ↔
      lam.colLen 0 ≤ 1 ∧ (parameterPolynomial a).Separable ∧
        (lam.colLen 0 ≠ 0 → (parameterPolynomial a).eval 0 ≠ 0) := by sorry

theorem parameterFiber_geometricallyReduced_iff_squarefree
    (lam : YoungDiagram) (a : Fin m → K) (hsize : lam.card + m = n) :
    Algebra.IsGeometricallyReduced K (ParameterFiber K n lam m a) ↔
      lam.colLen 0 ≤ 1 ∧
        Squarefree ((parameterPolynomial a).map (algebraMap K (AlgebraicClosure K))) ∧
        (lam.colLen 0 ≠ 0 → (parameterPolynomial a).eval 0 ≠ 0) := by sorry

end Fibers

section EtaleLocus
variable {K : Type*} [Field K] {n : ℕ} {lam : YoungDiagram}

theorem parameter_etale_atPrime_iff_polynomial
    (hn : lam.card ≤ n)
    (p : Ideal (ElementaryParameterRing K n lam)) [p.IsPrime] :
    Algebra.Etale (Localization.AtPrime p)
      (Localization.AtPrime p ⊗[ElementaryParameterRing K n lam] UntruncatedRing K n lam) ↔
      lam.colLen 0 ≤ 1 ∧
        (parameterPolynomial (fun i =>
          algebraMap (ElementaryParameterRing K n lam) p.ResidueField (MvPolynomial.X i))).Separable ∧
        (lam.colLen 0 ≠ 0 →
          (parameterPolynomial (fun i =>
            algebraMap (ElementaryParameterRing K n lam) p.ResidueField
              (MvPolynomial.X i))).eval 0 ≠ 0) := by sorry

end EtaleLocus

def rowFactorialProduct (lam : YoungDiagram) : ℕ :=
  ∏ j ∈ Finset.range (lam.colLen 0), (lam.rowLen j).factorial

theorem coordinateIdeal_isPrime {K : Type palomarFiberCoeffU} [Field K] {n : ℕ}
    (A : Finset (Fin n)) : (coordinateIdeal K A).IsPrime :=
  MvPolynomial.span_X_image_isPrime (R := K) (A : Set (Fin n))

attribute [instance] coordinateIdeal_isPrime

section LocalLength
variable {n : ℕ} {lam : YoungDiagram}

def genericComponentLength (K : Type palomarFiberCoeffU) [Field K]
    (A : SpringerCoordinateBlocks n lam) : ℕ∞ :=
  Module.length (Localization.AtPrime (coordinateIdeal K A.val))
    (Localization.AtPrime (coordinateIdeal K A.val) ⧸
      (untruncatedIdeal K n lam).map
        (algebraMap (PolynomialRing n K) (Localization.AtPrime (coordinateIdeal K A.val))))

end LocalLength

section GradedPiece
variable {R : Type palomarFiberCoeffU} [CommRing R] {n : ℕ}

theorem homogeneousQuotientScalarTower (R : Type palomarFiberCoeffU) [CommRing R] (n : ℕ) :
    IsScalarTower R (PolynomialRing n R) (PolynomialRing n R) :=
  inferInstance

abbrev homogeneousQuotientModule (R : Type palomarFiberCoeffU) [CommRing R] {n : ℕ}
    (I : Ideal (PolynomialRing n R)) : Module R (PolynomialRing n R ⧸ I) :=
  @Submodule.Quotient.module' (PolynomialRing n R) (PolynomialRing n R)
    inferInstance inferInstance inferInstance R inferInstance inferInstance
    inferInstance (homogeneousQuotientScalarTower R n) I

def homogeneousQuotientPiece (I : Ideal (PolynomialRing n R)) (d : ℕ) :
    @Submodule R (PolynomialRing n R ⧸ I) inferInstance inferInstance
      (homogeneousQuotientModule R I) :=
  (homogeneousSubmodule (Fin n) R d).map (Ideal.Quotient.mkₐ R I).toLinearMap

end GradedPiece

def untruncatedHilbertFunction (K : Type palomarFiberCoeffU) [Field K]
    (n : ℕ) (lam : YoungDiagram) (d : ℕ) : ℕ :=
  let I := untruncatedIdeal K n lam
  let P := homogeneousQuotientPiece I d
  let M := homogeneousQuotientModule K I
  @Module.finrank K P inferInstance
    (@Submodule.addCommMonoid K (PolynomialRing n K ⧸ I) inferInstance inferInstance M P)
    (@Submodule.module K (PolynomialRing n K ⧸ I) inferInstance inferInstance M P)

/-- Both conventional multiplicities: actual local length and the leading
coefficient of the eventual Hilbert polynomial of the actual quotient. -/
theorem untruncated_primary_and_graded_multiplicities (K : Type*) [Field K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    (∀ A : SpringerCoordinateBlocks n lam,
      genericComponentLength K A = (lam.card.factorial / rowFactorialProduct lam : ℕ)) ∧
    let m := n - lam.card
    let M : ℚ := ((n.factorial / (m.factorial * rowFactorialProduct lam) : ℕ) : ℚ)
    (m = 0 → (Module.finrank K (UntruncatedRing K n lam) : ℚ) = M) ∧
    (0 < m → ∃ P : Polynomial ℚ,
      (∃ N : ℕ, ∀ d > N, (untruncatedHilbertFunction K n lam d : ℚ) = P.eval (d : ℚ)) ∧
      P.natDegree = m - 1 ∧ ((m - 1).factorial : ℚ) * P.leadingCoeff = M) := by sorry

end HigherSpecht
