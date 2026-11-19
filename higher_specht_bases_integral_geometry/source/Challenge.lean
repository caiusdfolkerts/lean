/-
Definitions adapted verbatim from this project's retained Tau Ceti sources.
Copyright (c) 2026 The Tau Ceti contributors. Apache-2.0.
Original source paths and mathematical endpoints are recorded in map.json.
-/
module
public import Mathlib.Combinatorics.Young.YoungDiagram
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.FunLike.Fintype
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.Order.Antidiag.Pi
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Depth.Basic
public import Mathlib.Algebra.Category.ModuleCat.InjectiveDimension
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.Module.Opposite
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.LinearAlgebra.Dimension.Finite

/-! # The literal integral staircase basis and Cohen–Macaulayness -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators

universe u v w

open IsLocalRing

namespace Module

variable (R : Type u) [CommRing R] [IsLocalRing R] [Small.{v} R]
  (M : Type v) [AddCommGroup M] [Module R M]

/-- An `R`-module `M` over a local ring `R` is *Cohen–Macaulay* if it is zero or its depth equals
the dimension of its support. This is meant for finite modules over a Noetherian local ring, where
the depth never exceeds the dimension of the support. Stacks, Definition 10.103.1 (00N3). -/
@[stacks 00N3]
def IsCohenMacaulay : Prop :=
  Subsingleton M ∨ (depth (ModuleCat.of R M) : WithBot ℕ∞) = supportDim R M

end Module

namespace TauCeti
/-- A `μ`-tableau: a bijective filling of the cells of the Young diagram `μ` by the labels
`Fin μ.card`. -/
abbrev YoungTableau (μ : YoungDiagram) : Type := ↥μ.cells ≃ Fin μ.card

namespace YoungTableau
variable {μ : YoungDiagram}
/-- The row of the cell of `μ` carrying the label `k` in the tableau `t`. -/
def rowIndex (t : YoungTableau μ) (k : Fin μ.card) : ℕ := (t.symm k : ℕ × ℕ).1

/-- The column of the cell of `μ` carrying the label `k` in the tableau `t`. -/
def colIndex (t : YoungTableau μ) (k : Fin μ.card) : ℕ := (t.symm k : ℕ × ℕ).2

end YoungTableau

/-- A standard Young tableau of shape `μ` is a bijective labeling of its cells by
`Fin μ.card`, strictly increasing along rows and columns. -/
structure StandardYoungTableau (μ : YoungDiagram) where
  /-- The underlying Young tableau. -/
  toTableau : YoungTableau μ
  /-- Labels increase strictly from left to right. -/
  row_strict' : ∀ {i j₁ j₂ : ℕ} (h : j₁ < j₂) (hcell : (i, j₂) ∈ μ),
    toTableau ⟨(i, j₁), μ.up_left_mem (by rfl) h.le hcell⟩ < toTableau ⟨(i, j₂), hcell⟩
  /-- Labels increase strictly from top to bottom. -/
  col_strict' : ∀ {i₁ i₂ j : ℕ} (h : i₁ < i₂) (hcell : (i₂, j) ∈ μ),
    toTableau ⟨(i₁, j), μ.up_left_mem h.le (by rfl) hcell⟩ < toTableau ⟨(i₂, j), hcell⟩

end TauCeti

section DualOperator
namespace TauCeti

theorem dualScalarComm (k : Type u) [CommSemiring k] : SMulCommClass k k k :=
  ⟨fun a b x => mul_left_comm a b x⟩

abbrev dualScalarModule (k : Type u) (N : Type w) [CommSemiring k] [AddCommMonoid N]
    [Module k N] : Module k (Module.Dual k N) :=
  @LinearMap.module k k k N k _ _ _ _ _ _ (RingHom.id k) _ _ (dualScalarComm k)

attribute [local instance 1200] dualScalarModule

variable (k : Type u) (N : Type w) {A : Type v} [CommSemiring k] [Semiring A] [AddCommMonoid N]
  [Module k N] [Module Aᵐᵒᵖ N] [SMulCommClass Aᵐᵒᵖ k N]

/-- The **duality** `D = Hom_k(-, k)` turns a right `A`-module `N` into a left `A`-module: the
scalar `a` sends a functional `φ` to `x ↦ φ (x * a)`.  This records that action as a ring
homomorphism from `A` to the `k`-linear endomorphisms of `Module.Dual k N`.

Precomposition reverses composition, which is exactly what makes a *right* action on `N` into a
*left* action on its dual; the hypothesis `SMulCommClass Aᵐᵒᵖ k N` is what makes multiplication by
`a` a `k`-linear endomorphism of `N` in the first place. -/
def dualRightAction : A →+* Module.End k (Module.Dual k N) where
  toFun a := (Module.toModuleEnd k N (MulOpposite.op a)).dualMap
  map_one' := by ext φ x; simp
  map_mul' a b := by ext φ x; simp [mul_smul]
  map_zero' := by ext φ x; simp
  map_add' a b := by ext φ x; simp [add_smul]

end TauCeti

end DualOperator


universe palomarIntegralU

namespace HigherSpecht
open Finset MvPolynomial Module

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

/-- Stable name for the commutative ideal's two-sidedness in quotient data. -/
theorem untruncatedIdeal_isTwoSided (R : Type*) [CommRing R]
    (n : ℕ) (lam : YoungDiagram) : (untruncatedIdeal R n lam).IsTwoSided :=
  Ideal.instIsTwoSided_1 (untruncatedIdeal R n lam)

attribute [instance 1200] untruncatedIdeal_isTwoSided

end PolynomialDefinitions

/-- Literal source definition of UntruncatedRing. -/
abbrev UntruncatedRing (R : Type palomarIntegralU) [CommRing R] (n : ℕ) (μ : YoungDiagram) :=
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

/-- A basis assertion retaining the prescribed vector at every actual index. -/
def IsSpecifiedBasis {R V ι : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (v : ι → V) : Prop :=
  ∃ b : Basis ι R V, ∀ i, b i = v i

section Staircases
variable {n : ℕ} {μ : YoungDiagram}

theorem integralColumnMem (mu : YoungDiagram) (j : ℕ) (i : Fin (mu.colLen j)) :
    (i.val, j) ∈ mu := YoungDiagram.mem_iff_lt_colLen.mpr i.isLt

def columnEmbedding (U : ↥μ.cells ↪ Fin n) (j : ℕ) : Fin (μ.colLen j) ↪ Fin n where
  toFun i := U ⟨(i.val, j), integralColumnMem μ j i⟩
  inj' i l h := by
    have hi := congrArg (fun c : ↥μ.cells => c.val.1) (U.injective h)
    exact Fin.ext hi

def fillingLabels (U : ↥μ.cells ↪ Fin n) : Finset (Fin n) := Finset.univ.map U

def columnLeader (U : ↥μ.cells ↪ Fin n) (j : ℕ) : Fin n →₀ ℕ :=
  ∑ r : Fin (μ.colLen j), ∑ t ∈ Finset.Ioi r, Finsupp.single (columnEmbedding U j t) 1

def outsideLeader (U : ↥μ.cells ↪ Fin n) (s : ℕ) : Fin n →₀ ℕ :=
  ∑ i ∈ (fillingLabels U)ᶜ, Finsupp.single i (s - 1)

def staircaseVector (U : ↥μ.cells ↪ Fin n) (s : ℕ) : Fin n →₀ ℕ :=
  (∑ j ∈ Finset.range n, columnLeader U j) + outsideLeader U s

def ColumnDescending (U : ↥μ.cells ↪ Fin n) : Prop :=
  ∀ j, StrictAnti (columnEmbedding U j)

def GriffinStaircaseExponents (n : ℕ) (μ : YoungDiagram) (s : ℕ) : Set (Fin n →₀ ℕ) :=
  {c | ∃ U : ↥μ.cells ↪ Fin n, ColumnDescending U ∧ c ≤ staircaseVector U s}

def UntruncatedStaircaseExponents (n : ℕ) (μ : YoungDiagram) : Set (Fin n →₀ ℕ) :=
  {c | ∃ s : ℕ, c ∈ GriffinStaircaseExponents n μ s}

end Staircases

theorem adjoinOnes_isLowerSet (μ : YoungDiagram) (m : ℕ) :
    IsLowerSet (↑(μ.cells ∪ (Finset.range (μ.colLen 0 + m) ×ˢ {0})) : Set (ℕ × ℕ)) := by
    rintro ⟨a, b⟩ ⟨c, d⟩ ⟨hac, hbd⟩ h
    rcases Finset.mem_union.mp h with h | h
    · exact Finset.mem_union_left _ (μ.isLowerSet ⟨hac, hbd⟩ h)
    · apply Finset.mem_union_right
      simp only [Finset.mem_product, Finset.mem_range, Finset.mem_singleton] at h ⊢
      exact ⟨hac.trans_lt h.1, by omega⟩

def adjoinOnes (μ : YoungDiagram) (m : ℕ) : YoungDiagram where
  cells := μ.cells ∪ (Finset.range (μ.colLen 0 + m) ×ˢ {0})
  isLowerSet := adjoinOnes_isLowerSet μ m

abbrev SpecialFiberMonomialIndex (n : ℕ) (lam : YoungDiagram) :=
  UntruncatedStaircaseExponents n (adjoinOnes lam (n - lam.card))

def parameterMonomialClass (R : Type palomarIntegralU) [CommRing R] (n : ℕ) (lam : YoungDiagram)
    (a : Fin n →₀ ℕ) : UntruncatedRing R n lam :=
  Ideal.Quotient.mk (untruncatedIdeal R n lam) (MvPolynomial.monomial a 1)

/-- The actual staircase monomials from the enlarged special-fiber diagram
give a basis over the elementary parameters for every coefficient ring. -/
theorem untruncated_parameter_staircase_basis (R : Type*) [CommRing R]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    IsSpecifiedBasis (R := ElementaryParameterRing R n lam)
      (fun a : SpecialFiberMonomialIndex n lam => parameterMonomialClass R n lam a.val) := by sorry

/-- Every coefficient field gives the stated dimension and local
Cohen–Macaulayness at all primes. -/
theorem parameter_family_dimension_and_cohenMacaulay (K : Type*) [Field K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    ringKrullDim (UntruncatedRing K n lam) = (n - lam.card : ℕ) ∧
      IsNoetherianRing (UntruncatedRing K n lam) ∧
      ∀ (P : Ideal (UntruncatedRing K n lam)) [P.IsPrime],
        Module.IsCohenMacaulay (Localization.AtPrime P) (Localization.AtPrime P) := by sorry

open RingTheory.Sequence

def IsRegularSequencePresentation {R : Type*} [CommRing R] (I : Ideal R) : Prop :=
  ∃ xs : List R, IsRegular R xs ∧ Ideal.ofList xs = I

section Gorenstein
open CategoryTheory
variable (A : Type u) [CommRing A]

def IsGorensteinRing : Prop :=
  IsNoetherianRing A ∧ ∀ p : PrimeSpectrum A,
    ∃ d : ℕ, HasInjectiveDimensionLE
      (ModuleCat.of (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal)) d

end Gorenstein

/-- The two ordinary ring-theoretic classifications, over every field. -/
theorem untruncated_gorenstein_and_ci_cases (K : Type*) [Field K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    (IsGorensteinRing (UntruncatedRing K n lam) ↔
      lam.rowLen 0 ≤ 1 ∨ lam.card = n ∧ lam.colLen 0 ≤ 1) ∧
    (IsRegularSequencePresentation (untruncatedIdeal K n lam) ↔
      lam.rowLen 0 ≤ 1 ∨ lam.card = n ∧ lam.colLen 0 ≤ 1) := by sorry

section QuotientGrading
variable {R : Type*} [CommRing R] {n : ℕ}

def quotientHomogeneousPiece (I : Ideal (PolynomialRing n R)) (d : ℕ) :
    Submodule R (PolynomialRing n R ⧸ I) :=
  (MvPolynomial.homogeneousSubmodule (Fin n) R d).map (Ideal.Quotient.mkₐ R I).toLinearMap

end QuotientGrading

section Koszul
open scoped Classical
variable {K : Type*} [Field K] {n : ℕ}

def quotientIntegerPiece (I : Ideal (PolynomialRing n K)) (a : ℤ) :
    Submodule K (PolynomialRing n K ⧸ I) :=
  if 0 ≤ a then quotientHomogeneousPiece I a.toNat else ⊥

abbrev CoordinateKoszulCarrier (I : Ideal (PolynomialRing n K)) :=
  ExteriorAlgebra (PolynomialRing n K ⧸ I) (Fin n → PolynomialRing n K ⧸ I)

def coordinateKoszulBasis (I : Ideal (PolynomialRing n K)) :
    Basis (Finset (Fin n)) (PolynomialRing n K ⧸ I) (CoordinateKoszulCarrier I) :=
  (Pi.basisFun (PolynomialRing n K ⧸ I) (Fin n)).ExteriorAlgebra

def coordinateKoszulFunctional (I : Ideal (PolynomialRing n K)) :
    Module.Dual (PolynomialRing n K ⧸ I) (Fin n → PolynomialRing n K ⧸ I) :=
  ∑ j : Fin n, Ideal.Quotient.mk I (MvPolynomial.X j) •
    (Pi.basisFun (PolynomialRing n K ⧸ I) (Fin n)).coord j

def coordinateKoszulDifferential (I : Ideal (PolynomialRing n K)) :
    Module.End K (CoordinateKoszulCarrier I) :=
  (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm (PolynomialRing n K ⧸ I)
    (Fin n → PolynomialRing n K ⧸ I))) (coordinateKoszulFunctional I)).restrictScalars K

def coordinateKoszulPiece (I : Ideal (PolynomialRing n K)) (i a : ℤ) :
    Submodule K (CoordinateKoszulCarrier I) :=
  ⨅ s : Finset (Fin n),
    (if (s.card : ℤ) = i then quotientIntegerPiece I a else ⊥).comap
      (((coordinateKoszulBasis I).coord s).restrictScalars K)

def coordinateKoszulCycles (I : Ideal (PolynomialRing n K)) (i a : ℤ) :
    Submodule K (CoordinateKoszulCarrier I) :=
  coordinateKoszulPiece I i a ⊓ LinearMap.ker (coordinateKoszulDifferential I)

def coordinateKoszulBoundaries (I : Ideal (PolynomialRing n K)) (i a : ℤ) :
    Submodule K (CoordinateKoszulCarrier I) :=
  (coordinateKoszulPiece I (i + 1) (a - 1)).map (coordinateKoszulDifferential I)

abbrev CoordinateKoszulHomology (I : Ideal (PolynomialRing n K)) (i a : ℤ) :=
  coordinateKoszulCycles I i a ⧸
    (coordinateKoszulBoundaries I i a).comap (coordinateKoszulCycles I i a).subtype

end Koszul

def springerTopDegree (mu : YoungDiagram) : ℕ := ∑ c ∈ mu.cells, c.1

/-- The exact regularity value as the sharp support bound of the genuine
coordinate Koszul homology. -/
theorem untruncated_koszul_regularity_exact (K : Type*) [Field K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    let r : ℤ := (springerTopDegree lam : ℤ) +
      (n - lam.card : ℕ) * (lam.colLen 0 : ℤ)
    (∀ i a, r < a → Subsingleton (CoordinateKoszulHomology (untruncatedIdeal K n lam) i a)) ∧
      ∃ i, ¬ Subsingleton (CoordinateKoszulHomology (untruncatedIdeal K n lam) i r) := by sorry

section RelativeDualModule
variable (B A : Type*) [CommRing B] [CommRing A] [Algebra B A]

def RelativeDual := Module.Dual B A

namespace RelativeDual

attribute [local instance 1200] TauCeti.dualScalarModule

abbrev instAddCommGroup : AddCommGroup (RelativeDual B A) :=
  @LinearMap.addCommGroup B B A B _ _ _ _ _ _ (RingHom.id B)

attribute [instance] instAddCommGroup

abbrev instModule : Module B (RelativeDual B A) :=
  TauCeti.dualScalarModule B A

attribute [instance] instModule

abbrev instModule_1 : Module A (RelativeDual B A) :=
  show Module A (Module.Dual B A) from
    Module.compHom (Module.Dual B A) (TauCeti.dualRightAction B A)

attribute [instance] instModule_1

def toLinearMap (f : RelativeDual B A) : Module.Dual B A := f

def ofLinearMap (f : Module.Dual B A) : RelativeDual B A := f

instance : CoeFun (RelativeDual B A) (fun _ => A → B) :=
  ⟨fun f => toLinearMap B A f⟩

end RelativeDual
end RelativeDualModule

section IntrinsicCanonicalGrading
variable (K : Type*) [Field K]

def elementaryCanonicalShift (m : ℕ) : ℤ :=
  ∑ j : Fin m, (j.val + 1 : ℤ)

abbrev UntruncatedRelativeDual (n : ℕ) (lam : YoungDiagram) :=
  RelativeDual (ElementaryParameterRing K n lam) (UntruncatedRing K n lam)

def elementaryIntegerWeights (m : ℕ) (i : Fin m) : ℤ := i.val + 1

def elementaryWeightedPiece (m : ℕ) (d : ℤ) :
    Submodule K (MvPolynomial (Fin m) K) :=
  MvPolynomial.weightedHomogeneousSubmodule K (elementaryIntegerWeights m) d

end IntrinsicCanonicalGrading

section Dualizing
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
variable (A : Type u) [CommRing A]

def IsDualizingModule (M : Type u) [AddCommGroup M] [Module A M] : Prop :=
  IsNoetherianRing A ∧ Module.Finite A M ∧
    (∃ d : ℕ, HasInjectiveDimensionLE (ModuleCat.of A M) d) ∧
    (Function.Bijective (fun a : A => LinearMap.lsmul A M a)) ∧
    (letI := HasExt.standard (ModuleCat.{u} A)
     ∀ i : ℕ, 0 < i → ∀ e : Ext (ModuleCat.of A M) (ModuleCat.of A M) i, e = 0)

end Dualizing

/-- The actual canonical module, with homogeneous generators described
by their degree shift on every homogeneous input. -/
theorem untruncated_canonical_intrinsic_degree_and_type (K : Type*) [Field K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    let d : ℤ := ((n - lam.card + 1).choose 2 : ℤ) -
      springerTopDegree (adjoinOnes lam (n - lam.card))
    let t := Nat.card (TauCeti.StandardYoungTableau (adjoinOnes lam (n - lam.card)))
    IsDualizingModule (UntruncatedRing K n lam) (UntruncatedRelativeDual K n lam) ∧
    (∃ v : Fin t → UntruncatedRelativeDual K n lam,
      (∀ i q (x : UntruncatedRing K n lam),
        x ∈ quotientIntegerPiece (untruncatedIdeal K n lam) q →
        v i x ∈ elementaryWeightedPiece K (n - lam.card)
          (q + d - elementaryCanonicalShift (n - lam.card))) ∧
      Submodule.span (UntruncatedRing K n lam) (Set.range v) = ⊤) ∧
    (∀ r (v : Fin r → UntruncatedRelativeDual K n lam),
      Submodule.span (UntruncatedRing K n lam) (Set.range v) = ⊤ → t ≤ r) := by sorry

end HigherSpecht
