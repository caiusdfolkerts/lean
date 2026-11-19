module

public import paper_verification.literal004.PalomarPart000
import all paper_verification.literal004.PalomarPart000
public import paper_verification.literal003
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.Data.Nat.Choose.Basic
public import paper_verification.literal001
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Order.Interval.Finset.Nat
public import paper_verification.literal002
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Data.List.Pairwise
public import Mathlib.Order.MinMax
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.Linarith
public import paper_verification.literal000
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Multiset.Basic
public import Mathlib.Data.Finsupp.MonomialOrder
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Algebra.Order.Monoid.Prod
public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Order.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder
public import Mathlib.RingTheory.MvPolynomial.Groebner
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.Data.Finsupp.Option
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Tactic.Abel
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Logic.Equiv.Option
public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.Data.List.Chain
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Data.List.FinRange
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.LinearAlgebra.Finsupp.SumProd
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Homology.ShortComplex.Preadditive
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.RingTheory.Regular.RegularSequence

set_option Elab.async false

section TAF_LiteralSource_0273
/- Original module: PaperVerification.AlternatingFormsOddBarDegree -/


/-!
# The actual internal grading of the odd normalized bar complex

The degree of a tensor is the sum of the degrees of its actual positive
standard-product factors. The multiplication coefficients already proved
for the original quotient preserve this degree. Consequently the genuine
normalized bar complex, and not only its cut model, splits into these
internal-degree subcomplexes.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.AlternatingForms.BarDegrees

open PaperVerification.ReducedBarBasis PaperVerification.AugmentedAlgebraBasis

variable {K A C : Type*} [CommRing K] [Ring A] [Algebra K A]
  (B : Module.Basis (Option C) K A) (δ : C → ℕ)

@[expose]
def totalDegree (L : List C) : ℕ := (L.map δ).sum

@[simp] theorem totalDegree_nil : totalDegree δ []=0 := rfl

@[simp] theorem totalDegree_cons (c : C) (L : List C) :
    totalDegree δ (c::L)=δ c+totalDegree δ L := rfl

theorem totalDegree_append (L T : List C) :
    totalDegree δ (L++T)=totalDegree δ L+totalDegree δ T := by
  simp only [totalDegree,List.map_append,List.sum_append]

def degreePiece (N : ℕ) : Submodule K (List C →₀ K) :=
  Finsupp.supported K K {L | totalDegree δ L=N}

theorem degreePiece_eq_span (N : ℕ) :
    degreePiece (K := K) δ N=Submodule.span K
      ((fun L : List C ↦ Finsupp.single L (1 : K)) '' {L | totalDegree δ L=N}) :=
  Finsupp.supported_eq_span_single K _

theorem prefix_mem_degreePiece (c : C) {N : ℕ} (z : List C →₀ K)
    (hz : z∈degreePiece δ N) : prepend c z∈degreePiece δ (δ c+N) := by
  rw [degreePiece_eq_span] at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨L,hL,rfl⟩ := hz
    rw [prefix_single]
    apply Finsupp.single_mem_supported K 1
    change totalDegree δ (c::L)=δ c+N
    change totalDegree δ L=N at hL
    rw [totalDegree_cons,hL]
  | zero => simpa only [map_zero] using (degreePiece (K := K) δ (δ c+N)).zero_mem
  | add z w hz hw ihz ihw =>
    simpa only [map_add] using (degreePiece (K := K) δ (δ c+N)).add_mem ihz ihw
  | smul a z hz ih =>
    simpa only [map_smul] using (degreePiece (K := K) δ (δ c+N)).smul_mem a ih

variable (hδ : ∀ a b c,productCoefficients B a b c≠0 → δ c=δ a+δ b)

include hδ in
theorem product_appendTail_mem_degreePiece (a b : C) (L : List C) :
    appendTail L (productCoefficients B a b)∈degreePiece δ (δ a+δ b+totalDegree δ L) := by
  rw [appendTail,Finsupp.linearCombination_apply,Finsupp.sum]
  apply Submodule.sum_mem
  intro c hc
  apply Submodule.smul_mem
  apply Finsupp.single_mem_supported K 1
  change totalDegree δ (c::L)=δ a+δ b+totalDegree δ L
  rw [totalDegree_cons,hδ a b c (Finsupp.mem_support_iff.mp hc)]

include hδ in
theorem differentialBasis_mem_degreePiece (L : List C) :
    differentialBasis B L∈degreePiece δ (totalDegree δ L) := by
  induction L with
  | nil => exact Submodule.zero_mem _
  | cons a L ih =>
    cases L with
    | nil =>
      simp only [differentialBasis,merge_single,mergeBasis,smul_zero,map_zero,sub_zero]
      exact Submodule.zero_mem _
    | cons b L =>
      rw [differentialBasis]
      apply Submodule.sub_mem
      · rw [merge_single,one_smul,mergeBasis]
        simpa only [totalDegree_cons,Nat.add_assoc] using
          product_appendTail_mem_degreePiece B δ hδ a b L
      · exact prefix_mem_degreePiece δ a _ ih

include hδ in
theorem differential_mem_degreePiece {N : ℕ} (z : List C →₀ K)
    (hz : z∈degreePiece δ N) : differential B z∈degreePiece δ N := by
  rw [degreePiece_eq_span] at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨L,hL,rfl⟩ := hz
    rw [differential_single,one_smul]
    change totalDegree δ L=N at hL
    simpa only [hL] using differentialBasis_mem_degreePiece B δ hδ L
  | zero => simpa only [map_zero] using (degreePiece (K := K) δ N).zero_mem
  | add z w hz hw ihz ihw =>
    simpa only [map_add] using (degreePiece (K := K) δ N).add_mem ihz ihw
  | smul a z hz ih =>
    simpa only [map_smul] using (degreePiece (K := K) δ N).smul_mem a ih

end PaperVerification.AlternatingForms.BarDegrees

namespace PaperVerification.AlternatingForms

open BarCompositions BarDegrees PaperVerification.ReducedBarBasis
open CategoryTheory

universe u
variable {K : Type u} [Field K] [CharZero K]
  (k t : ℕ) (hs : t+2≤k+1)

local notation "C" => OddPositiveStandardIndex (K := K) k t hs
local notation "B" => oddAugmentedBasis (K := K) k t hs
local notation "e" => oddPositiveWordEquiv (K := K) k t hs
local notation "δ" => oddPositiveDegree (K := K) k t hs

theorem oddBarWord_length_eq_degree (L : List C) :
    (flattenBarWord e L).length=totalDegree δ L := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    change ((e a).val++flattenBarWord e L).length=δ a+totalDegree δ L
    rw [List.length_append,oddPositiveWord_degree,ih]

theorem oddInternalDegreePiece_eq_inf (r N : ℕ) :
    internalDegreePiece (K := K) e r N=
      BarFree.lengthPiece C K r ⊓ degreePiece δ N := by
  ext z
  change ((z.support : Set (List C))⊆{L : List C | L.length=r ∧ (flattenBarWord e L).length=N}) ↔
    ((z.support : Set (List C))⊆{L : List C | L.length=r}) ∧
      ((z.support : Set (List C))⊆{L : List C | totalDegree δ L=N})
  simp only [Set.subset_def,Set.mem_setOf_eq,oddBarWord_length_eq_degree]
  constructor
  · intro h
    exact ⟨fun L hL ↦ (h L hL).1,fun L hL ↦ (h L hL).2⟩
  · rintro ⟨h₁,h₂⟩ L hL
    exact ⟨h₁ L hL,h₂ L hL⟩

theorem oddReducedDifferential_mem_internalDegree {r N : ℕ} (z : List C →₀ K)
    (hz : z∈internalDegreePiece (K := K) e (r+1) N) :
    differential B z∈internalDegreePiece (K := K) e r N := by
  rw [oddInternalDegreePiece_eq_inf] at hz ⊢
  exact ⟨BarFree.reducedDifferential_mem_lengthPiece B z hz.1,
    differential_mem_degreePiece B δ (odd_productCoefficient_degree k t hs) z hz.2⟩

/-- The sign is the actual sign after tensoring the free bar resolution
with the augmentation residue. -/
def oddBigradedDifferential (r N : ℕ) :
    internalDegreePiece (K := K) e (r+1) N →ₗ[K]
      internalDegreePiece (K := K) e r N :=
  LinearMap.codRestrict _
    ((-differential B).comp (internalDegreePiece (K := K) e (r+1) N).subtype)
    (fun z ↦ Submodule.neg_mem _
      (oddReducedDifferential_mem_internalDegree k t hs z.val z.property))

@[simp] theorem oddBigradedDifferential_val (r N : ℕ)
    (z : internalDegreePiece (K := K) e (r+1) N) :
    (oddBigradedDifferential (K := K) k t hs r N z).val=-differential B z.val := rfl

theorem oddBigradedDifferential_squared (r N : ℕ) :
    (oddBigradedDifferential (K := K) k t hs r N).comp
      (oddBigradedDifferential (K := K) k t hs (r+1) N)=0 := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  change -differential B (-differential B z.val)=0
  rw [map_neg,neg_neg,differential_squared (oddAugmentation (K := K) k t) B
    (oddAugmentedBasis_none (K := K) k t hs) (oddAugmentation_positive (K := K) k t hs)]

def oddInternalDegreeInclusion (r N : ℕ) :
    internalDegreePiece (K := K) e r N →ₗ[K] BarFree.lengthPiece C K r :=
  Submodule.inclusion (by
    rw [oddInternalDegreePiece_eq_inf]
    exact inf_le_left)

theorem oddInternalDegreeInclusion_differential (r N : ℕ) :
    (oddInternalDegreeInclusion k t hs r N).comp (oddBigradedDifferential (K := K) k t hs r N)=
      (BarFree.negativeReducedDegreeDifferential B r).comp
        (oddInternalDegreeInclusion k t hs (r+1) N) := by
  apply LinearMap.ext
  intro z
  rfl

def oddInternalDegreeBasis (r N : ℕ) :
    Module.Basis (InternalDegreeIndex e r N) K (internalDegreePiece (K := K) e r N) :=
  .ofRepr (internalDegreeCoordinates e r N)

def oddInternalDegreeComplex (N : ℕ) : ChainComplex (ModuleCat K) ℕ :=
  ChainComplex.of (fun r ↦ ModuleCat.of K (internalDegreePiece (K := K) e r N))
    (fun r ↦ ModuleCat.ofHom (oddBigradedDifferential (K := K) k t hs r N))
    (fun r ↦ ModuleCat.hom_ext (oddBigradedDifferential_squared k t hs r N))

@[simp] theorem oddInternalDegreeComplex_d (r N : ℕ) :
    (oddInternalDegreeComplex (K := K) k t hs N).d (r+1) r=
      ModuleCat.ofHom (oddBigradedDifferential (K := K) k t hs r N) := by
  simp [oddInternalDegreeComplex]

/-- This is the actual inclusion into the complex computing ordinary
Tor, with its original differential and coefficient field. -/
def oddInternalDegreeInclusionChain (N : ℕ) :
    oddInternalDegreeComplex (K := K) k t hs N ⟶
      BarFree.reducedComplex (oddAugmentation (K := K) k t) B
        (oddAugmentedBasis_none (K := K) k t hs) (oddAugmentation_positive (K := K) k t hs) where
  f r := ModuleCat.ofHom (oddInternalDegreeInclusion k t hs r N)
  comm' i j hij := by
    change j+1=i at hij
    subst i
    rw [oddInternalDegreeComplex_d,BarFree.reducedComplex_d]
    apply ModuleCat.hom_ext
    exact (oddInternalDegreeInclusion_differential k t hs j N).symm

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0273

section TAF_LiteralSource_0274
/- Original module: PaperVerification.AlternatingFormsBarCoefficientFormula -/


/-!
# The full adjacent-product expansion of the bar differential

This expansion retains every adjacent multiplication and its actual
structure coefficients. It is the coefficient identity used to compare
the original normalized bar differential with a monomial leading complex.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace PaperVerification.AlternatingForms.BarCoefficientFormula

open PaperVerification.ReducedBarBasis PaperVerification.AugmentedAlgebraBasis

variable {K C : Type*} [CommRing K]

def adjacent (μ : C → C → (C →₀ K)) : ℕ → List C → (List C →₀ K)
  | 0,a::b::L => appendTail L (μ a b)
  | 0,_ => 0
  | i+1,a::L => prepend a (adjacent μ i L)
  | _+1,[] => 0

def basisDifferential (μ : C → C → (C →₀ K)) : List C → (List C →₀ K)
  | [] => 0
  | a::L => adjacent μ 0 (a::L)-prepend a (basisDifferential μ L)

def coefficientDifferential (μ : C → C → (C →₀ K)) :
    (List C →₀ K) →ₗ[K] (List C →₀ K) :=
  Finsupp.linearCombination K (basisDifferential μ)

@[simp] theorem coefficientDifferential_single (μ : C → C → (C →₀ K))
    (L : List C) (c : K) :
    coefficientDifferential μ (Finsupp.single L c)=c • basisDifferential μ L :=
  Finsupp.linearCombination_single _ _ _

theorem basisDifferential_expansion (μ : C → C → (C →₀ K)) (L : List C) :
    basisDifferential μ L=
      ∑ i∈Finset.range (L.length-1),(-1 : ℤˣ)^i • adjacent μ i L := by
  induction L with
  | nil => simp only [basisDifferential,List.length_nil,Nat.zero_sub,
      Finset.range_zero,Finset.sum_empty]
  | cons a L ih =>
    cases L with
    | nil => simp only [basisDifferential,adjacent,map_zero,sub_zero,List.length_cons,
        List.length_nil,Nat.add_sub_cancel,Finset.range_zero,Finset.sum_empty]
    | cons b L =>
      simp only [List.length_cons,Nat.add_sub_cancel] at ih ⊢
      rw [basisDifferential,ih,Finset.sum_range_succ']
      simp only [pow_zero,one_smul,adjacent,map_sum,map_zsmul_unit]
      rw [sub_eq_add_neg,←Finset.sum_neg_distrib,add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      simp [pow_succ',mul_smul,Units.smul_def]

theorem negative_basisDifferential_expansion (μ : C → C → (C →₀ K)) (L : List C) :
    -basisDifferential μ L=
      ∑ i∈Finset.range (L.length-1),(-1 : ℤˣ)^(i+1) • adjacent μ i L := by
  rw [basisDifferential_expansion,←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp [pow_succ',mul_smul,Units.smul_def]

variable {A : Type*} [Ring A] [Algebra K A] (B : Module.Basis (Option C) K A)

theorem basisDifferential_actual (L : List C) :
    basisDifferential (productCoefficients B) L=differentialBasis B L := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    change adjacent (productCoefficients B) 0 (a::L)-
        prepend a (basisDifferential (productCoefficients B) L)=
      merge B a (Finsupp.single L 1)-prepend a (differentialBasis B L)
    rw [ih]
    congr 1
    cases L <;> simp only [adjacent,merge_single,mergeBasis,one_smul,smul_zero]

theorem coefficientDifferential_actual :
    coefficientDifferential (productCoefficients B)=differential B := by
  apply Finsupp.lhom_ext
  intro L c
  rw [coefficientDifferential_single,differential_single,basisDifferential_actual]

/-- The tensor differential is the negative of the positive-sign
adjacent-product convention; its first merge has sign minus one. -/
theorem negative_differentialBasis_expansion (L : List C) :
    -differentialBasis B L=
      ∑ i∈Finset.range (L.length-1),(-1 : ℤˣ)^(i+1) •
        adjacent (productCoefficients B) i L := by
  rw [←basisDifferential_actual,basisDifferential_expansion,←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp [pow_succ',mul_smul,Units.smul_def]

end PaperVerification.AlternatingForms.BarCoefficientFormula
end
end
end TAF_LiteralSource_0274

section TAF_LiteralSource_0275
/- Original module: PaperVerification.AlternatingFormsOddBarLeadingComparison -/


/-!
# The highest terms of the actual odd bar differential

Normal adjacent products concatenate with coefficient one. Every term of
every nonnormal adjacent product strictly lowers the word order, even
inside a longer tensor. This proves the complete basis-level comparison
with the recursive normal-merge operator, including cancellation among
different adjacent multiplication positions.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators MonomialOrder

namespace PaperVerification.AlternatingForms

open Hibi BarCompositions BarCoefficientFormula PBWWords
open PaperVerification.ReducedBarBasis PaperVerification.AugmentedAlgebraBasis

universe u
variable {K : Type u} [Field K] [CharZero K]
  (k t : ℕ) (hs : t+2≤k+1)

local notation "C" => OddPositiveStandardIndex (K := K) k t hs
local notation "α" => oddIntervalLower k (t+2) hs
local notation "β" => oddIntervalUpper k (t+2) hs
local notation "J" => IntervalIndex α β
local notation "B" => oddAugmentedBasis (K := K) k t hs
local notation "e" => oddPositiveWordEquiv (K := K) k t hs

def oddNormalProduct (a b : C) : C →₀ K :=
  if h : ((e a).val++(e b).val).IsChain (·≤·) then
    Finsupp.single ((e).symm (appendPositiveNormalWord k t hs (e a) (e b) h)) 1
  else 0

def oddNormalDifferentialBasis (L : List C) : List C →₀ K :=
  basisDifferential (oddNormalProduct k t hs) L

def oddStrictWordPiece (m : MonomialOrder J) (W : List J) :
    Submodule K (List C →₀ K) :=
  Finsupp.supported K K {L |
    Before (oddGoodOrder k t hs m) (·≤·) (flattenBarWord e L) W ∧
      (flattenBarWord e L).length=W.length}

def oddSameWordPiece (W : List J) : Submodule K (List C →₀ K) :=
  Finsupp.supported K K {L | flattenBarWord e L=W}

theorem oddStrictWordPiece_prefix (m : MonomialOrder J) (W : List J)
    (a : C) (z : List C →₀ K) (hz : z∈oddStrictWordPiece k t hs m W) :
    prepend a z∈oddStrictWordPiece k t hs m ((e a).val++W) := by
  rw [oddStrictWordPiece,Finsupp.supported_eq_span_single] at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨L,hL,rfl⟩ := hz
    rw [prefix_single]
    apply Finsupp.single_mem_supported K 1
    constructor
    · change Before (oddGoodOrder k t hs m) (· ≤ ·)
        ((e a).val++flattenBarWord e L) ((e a).val++W)
      simpa only [List.append_nil] using
        before_context_of_before (oddGoodOrder k t hs m) (·≤·)
          (e a).val [] (flattenBarWord e L) W hL.1
    · change ((e a).val++flattenBarWord e L).length=((e a).val++W).length
      simp only [List.length_append,hL.2]
  | zero => simpa only [map_zero] using
      (oddStrictWordPiece k t hs m ((e a).val++W)).zero_mem
  | add z w hz hw ihz ihw => simpa only [map_add] using
      (oddStrictWordPiece k t hs m ((e a).val++W)).add_mem ihz ihw
  | smul c z hz ih => simpa only [map_smul] using
      (oddStrictWordPiece k t hs m ((e a).val++W)).smul_mem c ih

theorem oddSameWordPiece_prefix (W : List J) (a : C)
    (z : List C →₀ K) (hz : z∈oddSameWordPiece k t hs W) :
    prepend a z∈oddSameWordPiece k t hs ((e a).val++W) := by
  rw [oddSameWordPiece,Finsupp.supported_eq_span_single] at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨L,hL,rfl⟩ := hz
    rw [prefix_single]
    apply Finsupp.single_mem_supported K 1
    change (e a).val++flattenBarWord e L=(e a).val++W
    rw [hL]
  | zero => simpa only [map_zero] using
      (oddSameWordPiece k t hs ((e a).val++W)).zero_mem
  | add z w hz hw ihz ihw => simpa only [map_add] using
      (oddSameWordPiece k t hs ((e a).val++W)).add_mem ihz ihw
  | smul c z hz ih => simpa only [map_smul] using
      (oddSameWordPiece k t hs ((e a).val++W)).smul_mem c ih

theorem oddNormalAdjacent_mem_sameWord (a b : C) (L : List C) :
    appendTail L (oddNormalProduct k t hs a b)∈
      oddSameWordPiece k t hs (flattenBarWord e (a::b::L)) := by
  unfold oddNormalProduct
  split_ifs with h
  · rw [appendTail_single]
    apply Finsupp.single_mem_supported K 1
    change (e ((e).symm (appendPositiveNormalWord k t hs (e a) (e b) h))).val++
      flattenBarWord e L=(e a).val++((e b).val++flattenBarWord e L)
    rw [Equiv.apply_symm_apply]
    exact List.append_assoc _ _ _
  · rw [map_zero]
    exact Submodule.zero_mem _

theorem oddNormalDifferentialBasis_mem_sameWord (L : List C) :
    oddNormalDifferentialBasis k t hs L∈oddSameWordPiece k t hs (flattenBarWord e L) := by
  induction L with
  | nil => exact Submodule.zero_mem _
  | cons a L ih =>
    cases L with
    | nil =>
      simp only [oddNormalDifferentialBasis,basisDifferential,adjacent,map_zero,sub_zero]
      exact Submodule.zero_mem _
    | cons b L =>
      change appendTail L (oddNormalProduct k t hs a b)-
        prepend a (oddNormalDifferentialBasis k t hs (b::L))∈_
      exact Submodule.sub_mem _ (oddNormalAdjacent_mem_sameWord k t hs a b L)
        (oddSameWordPiece_prefix k t hs _ a _ ih)

theorem oddAdjacent_difference_mem_strict (m : MonomialOrder J)
    (a b : C) (L : List C) :
    appendTail L (productCoefficients B a b)-appendTail L (oddNormalProduct k t hs a b)∈
      oddStrictWordPiece k t hs m (flattenBarWord e (a::b::L)) := by
  by_cases h : ((e a).val++(e b).val).IsChain (·≤·)
  · rw [odd_productCoefficients_of_normal k t hs a b h,oddNormalProduct,dif_pos h,sub_self]
    exact Submodule.zero_mem _
  · rw [oddNormalProduct,dif_neg h,map_zero,sub_zero,
      appendTail,Finsupp.linearCombination_apply,Finsupp.sum]
    apply Submodule.sum_mem
    intro c hc
    apply Submodule.smul_mem
    apply Finsupp.single_mem_supported K 1
    have hn := Finsupp.mem_support_iff.mp hc
    constructor
    · have hm := odd_productCoefficient_exponent_le k t hs m a b c hn
      have hb := before_context (oddGoodOrder k t hs m) (·≤·) []
        (flattenBarWord e L) ((e a).val++(e b).val) (e c).val
        (by simpa only [exponent_append,oddPositiveWord_exponent] using hm)
        (fun hp ↦ h (List.isChain_iff_pairwise.mpr hp))
        (List.isChain_iff_pairwise.mp (e c).property.2)
      change Before (oddGoodOrder k t hs m) (· ≤ ·)
        ((e c).val++flattenBarWord e L)
        ((e a).val++((e b).val++flattenBarWord e L))
      simpa only [List.nil_append,List.append_assoc] using hb
    · have hd := odd_productCoefficient_degree k t hs a b c hn
      change ((e c).val++flattenBarWord e L).length=
        ((e a).val++((e b).val++flattenBarWord e L)).length
      simp only [List.length_append,oddPositiveWord_degree]
      omega

/-- The full difference, including every merge position, has strictly
smaller literal word weight. The induction handles cancellations by
submodule closure, so this is stronger than a list of possible terms. -/
theorem oddDifferentialBasis_difference_mem_strict (m : MonomialOrder J) (L : List C) :
    differentialBasis B L-oddNormalDifferentialBasis k t hs L∈
      oddStrictWordPiece k t hs m (flattenBarWord e L) := by
  induction L with
  | nil => simpa only [differentialBasis,oddNormalDifferentialBasis,basisDifferential,sub_self]
      using (oddStrictWordPiece k t hs m (flattenBarWord e [])).zero_mem
  | cons a L ih =>
    cases L with
    | nil =>
      simp only [differentialBasis,oddNormalDifferentialBasis,basisDifferential,adjacent,
        merge_single,mergeBasis,smul_zero,map_zero,sub_zero,sub_self]
      exact Submodule.zero_mem _
    | cons b L =>
      have h₁ := oddAdjacent_difference_mem_strict k t hs m a b L
      have h₂ := oddStrictWordPiece_prefix k t hs m (flattenBarWord e (b::L)) a _ ih
      have he : differentialBasis B (a::b::L)-oddNormalDifferentialBasis k t hs (a::b::L)=
          (appendTail L (productCoefficients B a b)-appendTail L (oddNormalProduct k t hs a b))-
            prepend a (differentialBasis B (b::L)-oddNormalDifferentialBasis k t hs (b::L)) := by
        simp only [differentialBasis,oddNormalDifferentialBasis,basisDifferential,adjacent,
          merge_single,mergeBasis,one_smul,map_sub]
        abel
      rw [he]
      exact Submodule.sub_mem _ h₁ h₂

theorem oddDifferentialBasis_difference_weight_lt (m : MonomialOrder J)
    (L T : List C)
    (h : (differentialBasis B L-oddNormalDifferentialBasis k t hs L) T≠0) :
    weight (oddGoodOrder k t hs m) (·≤·) (flattenBarWord e L).length (flattenBarWord e T)<
      weight (oddGoodOrder k t hs m) (·≤·) (flattenBarWord e L).length (flattenBarWord e L) := by
  have hm := oddDifferentialBasis_difference_mem_strict k t hs m L
  have hp := hm (Finsupp.mem_support_iff.mpr h)
  exact weight_lt (oddGoodOrder k t hs m) (·≤·) _ _ _ hp.2 hp.1

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0275

section TAF_LiteralSource_0276
/- Original module: PaperVerification.AlternatingFormsBarNormalMerging -/


/-!
# Normal adjacent multiplication and admissible cut deletion

Normal merging is defined on the literal positive words. Its output,
when present, is exactly the factorization obtained by deleting the
corresponding interior cut. Thus optional cuts are precisely the nonzero
normal adjacent products.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace PaperVerification.AlternatingForms.BarCompositions

open BarCoefficientFormula PaperVerification.ReducedBarBasis

variable {C J : Type*} [Preorder J] (e : C ≃ PositiveNormalWord J)

def concatenateNormal (a b : C)
    (h : ((e a).val++(e b).val).IsChain (·≤·)) : C :=
  e.symm ⟨(e a).val++(e b).val,
    by rw [List.length_append]; exact Nat.add_pos_left (e a).property.1 _,h⟩

@[simp] theorem concatenateNormal_word (a b : C)
    (h : ((e a).val++(e b).val).IsChain (·≤·)) :
    (e (concatenateNormal e a b h)).val=(e a).val++(e b).val := by
  exact congrArg (fun W : PositiveNormalWord J => W.val)
    (e.apply_symm_apply _)

def normalMerge : ℕ → List C → Option (List C)
  | 0,a::b::L => if h : ((e a).val++(e b).val).IsChain (·≤·)
      then some (concatenateNormal e a b h::L) else none
  | 0,_ => none
  | i+1,a::L => (normalMerge i L).map (a::·)
  | _+1,[] => none

theorem normalMerge_map (i : ℕ) (L M : List C)
    (h : normalMerge e i L=some M) :
    M.map (fun a ↦ (e a).val)=mergeAdjacent (·++·) i (L.map (fun a ↦ (e a).val)) := by
  induction i generalizing L M with
  | zero =>
    cases L with
    | nil => simp only [normalMerge] at h; cases h
    | cons a L =>
      cases L with
      | nil => simp only [normalMerge] at h; cases h
      | cons b L =>
        by_cases hab : ((e a).val++(e b).val).IsChain (· ≤ ·)
        · rw [normalMerge,dif_pos hab] at h
          cases h
          simp only [List.map_cons,mergeAdjacent,concatenateNormal_word]
        · rw [normalMerge,dif_neg hab] at h
          cases h
  | succ i ih =>
    cases L with
    | nil => simp only [normalMerge] at h; cases h
    | cons a L =>
      cases he : normalMerge e i L with
      | none => simp only [normalMerge,he,Option.map_none] at h; cases h
      | some T =>
        simp only [normalMerge,he,Option.map_some,Option.some.injEq] at h
        subst M
        simp only [List.map_cons,mergeAdjacent,ih L T he]

theorem normalMerge_length (i : ℕ) (L M : List C)
    (h : normalMerge e i L=some M) (hi : i+1<L.length) :
    M.length+1=L.length := by
  have hm := normalMerge_map e i L M h
  have hlen := congrArg List.length hm
  have hj : i+1<(L.map (fun a ↦ (e a).val)).length := by
    simpa only [List.length_map] using hi
  have he := mergeAdjacent_length (·++·) i (L.map (fun a ↦ (e a).val)) hj
  simpa only [List.length_map,←hlen] using he

theorem normalMerge_exists_iff (i : ℕ) (L : List C) (hi : i+1<L.length) :
    (∃ M,normalMerge e i L=some M) ↔
      ∀ T∈mergeAdjacent (·++·) i (L.map (fun a ↦ (e a).val)),T.IsChain (·≤·) := by
  constructor
  · rintro ⟨M,hM⟩ T hT
    rw [←normalMerge_map e i L M hM] at hT
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hT
    exact (e a).property.2
  · intro h
    induction i generalizing L with
    | zero =>
      cases L with
      | nil => simp only [List.length_nil] at hi; omega
      | cons a L =>
        cases L with
        | nil => simp only [List.length_cons,List.length_nil] at hi; omega
        | cons b L =>
          have hab : ((e a).val++(e b).val).IsChain (·≤·) :=
            h _ (by simp only [List.map_cons,mergeAdjacent]; exact List.mem_cons_self)
          exact ⟨concatenateNormal e a b hab::L,by rw [normalMerge,dif_pos hab]⟩
    | succ i ih =>
      cases L with
      | nil => simp only [List.length_nil] at hi; omega
      | cons a L =>
        have hi' : i+1<L.length := by simp only [List.length_cons] at hi; omega
        have h' : ∀ T∈mergeAdjacent (·++·) i (L.map (fun a ↦ (e a).val)),T.IsChain (·≤·) := by
          intro T hT
          apply h T
          exact List.mem_cons_of_mem _ hT
        obtain ⟨M,hM⟩ := ih L hi' h'
        exact ⟨a::M,by simp only [normalMerge,hM,Option.map_some]⟩

theorem normalMerge_optional (W : List J) (r : ℕ) (L : ActualBarIndex e W r)
    (i : ℕ) (hi : i+1<L.val.length) :
    (∃ M,normalMerge e i L.val=some M) ↔
      (factorizationComposition W (actualFactorization e W r L).val.val).boundary
        ⟨i+1,by
          simpa only [factorizationComposition,Composition.length,actualFactorization,
            List.length_map] using Nat.lt_succ_of_lt hi⟩∉mandatoryCuts (·≤·) W := by
  rw [normalMerge_exists_iff e i L.val hi]
  exact merge_admissible_iff_optional (·≤·) W (actualFactorization e W r L).val i
    (by simpa only [actualFactorization,List.length_map] using hi)

variable {K : Type*} [CommRing K]

def normalProduct (a b : C) : C →₀ K :=
  if h : ((e a).val++(e b).val).IsChain (·≤·)
    then Finsupp.single (concatenateNormal e a b h) 1 else 0

def optionalSingle (M : Option (List C)) : List C →₀ K :=
  M.elim 0 (fun L ↦ Finsupp.single L 1)

theorem adjacent_normalProduct (i : ℕ) (L : List C) :
    adjacent (normalProduct (K := K) e) i L=optionalSingle (normalMerge e i L) := by
  induction i generalizing L with
  | zero =>
    cases L with
    | nil => rfl
    | cons a L =>
      cases L with
      | nil => rfl
      | cons b L =>
        by_cases h : ((e a).val++(e b).val).IsChain (·≤·)
        · simp only [adjacent,normalProduct,normalMerge,dif_pos h,appendTail_single,
            optionalSingle,Option.elim_some]
        · simp only [adjacent,normalProduct,normalMerge,dif_neg h,map_zero,
            optionalSingle,Option.elim_none]
  | succ i ih =>
    cases L with
    | nil => rfl
    | cons a L =>
      rw [adjacent,normalMerge,ih]
      cases normalMerge e i L <;> simp only [optionalSingle,Option.map_none,
        Option.map_some,Option.elim_none,Option.elim_some,map_zero,prefix_single]

def barWordMap (W : List J) (r : ℕ) :
    (BarIndex (·≤·) W r →₀ K) →ₗ[K] (List C →₀ K) :=
  Finsupp.lmapDomain K K (fun L ↦ factorizationBarWord e W L.val)

@[simp] theorem barWordMap_single (W : List J) (r : ℕ)
    (L : BarIndex (·≤·) W r) (c : K) :
    barWordMap e W r (Finsupp.single L c)=
      Finsupp.single (factorizationBarWord e W L.val) c := by
  simp only [barWordMap,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]

theorem barWordMap_injective (W : List J) (r : ℕ) :
    Function.Injective (barWordMap (K := K) e W r) := by
  apply Finsupp.mapDomain_injective
  intro L M h
  apply (actualBarIndexEquiv e W r).symm.injective
  apply Subtype.ext
  change factorizationBarWord e W L.val = factorizationBarWord e W M.val
  exact h

end PaperVerification.AlternatingForms.BarCompositions
end
end
end TAF_LiteralSource_0276

section TAF_LiteralSource_0277
/- Original module: PaperVerification.AlternatingFormsBarCutTransport -/


/-!
# Exact transport from normal bar multiplication to cut contraction

Every normal adjacent merge is precisely an optional interior cut, with
the same output word and sign. The equality below is an identity for
the full differential, not a comparison of dimensions or possible terms.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.AlternatingForms.BarCompositions

open BarCoefficientFormula

variable {K C J : Type*} [CommRing K] [Preorder J]
  (e : C ≃ PositiveNormalWord J)

theorem adjacent_normalProduct_cut (W : List J) (r : ℕ)
    (L : ActualBarIndex e W (r+1))
    (j : Fin ((factorizationComposition W (actualFactorization e W (r+1) L).val.val).length+1))
    (hj : (factorizationComposition W (actualFactorization e W (r+1) L).val.val).boundary j∉
      mandatoryCuts (·≤·) W) :
    adjacent (normalProduct (K := K) e) (j.val-1) L.val=
      barWordMap (K := K) e W r (Finsupp.single
        (mergedBarIndex (·≤·) W r (actualFactorization e W (r+1) L) j hj) 1) := by
  have hb := optional_boundary_index_bounds (·≤·) W
    (actualFactorization e W (r+1) L).val j hj
  have hi : j.val-1+1<L.val.length := by
    simpa only [actualFactorization,List.length_map] using
      (show j.val-1+1<(actualFactorization e W (r+1) L).val.val.val.length by omega)
  have hj' := hj
  have he : j.val-1+1=j.val := by omega
  have ho : ∃ M,normalMerge e (j.val-1) L.val=some M := by
    apply (normalMerge_optional e W (r+1) L (j.val-1) hi).mpr
    have hindex : (⟨j.val-1+1, by
        simpa only [factorizationComposition,Composition.length,actualFactorization,
          List.length_map] using Nat.lt_succ_of_lt hi⟩ :
        Fin ((factorizationComposition W
          (actualFactorization e W (r+1) L).val.val).length+1)) = j := by
      apply Fin.ext
      exact he
    exact hindex.symm ▸ hj'
  obtain ⟨M,hM⟩ := ho
  rw [adjacent_normalProduct,hM,optionalSingle,Option.elim_some,barWordMap_single]
  congr 1
  apply (List.map_injective_iff.mpr
    (show Function.Injective (fun a : C ↦ (e a).val) from
      fun a b hab ↦ e.injective (Subtype.ext hab)))
  rw [factorizationBarWord_map]
  exact normalMerge_map e (j.val-1) L.val M hM

theorem adjacent_normalProduct_zero_of_mandatory (W : List J) (r : ℕ)
    (L : ActualBarIndex e W r) (i : ℕ) (hi : i+1<L.val.length)
    (hj : (factorizationComposition W (actualFactorization e W r L).val.val).boundary
      ⟨i+1,by
        simpa only [factorizationComposition,Composition.length,actualFactorization,
          List.length_map] using Nat.lt_succ_of_lt hi⟩∈mandatoryCuts (·≤·) W) :
    adjacent (normalProduct (K := K) e) i L.val=0 := by
  have hnone : normalMerge e i L.val=none := by
    cases hm : normalMerge e i L.val with
    | none => rfl
    | some M =>
      have ho := (normalMerge_optional e W r L i hi).mp ⟨M,hm⟩
      exact False.elim (ho hj)
  rw [adjacent_normalProduct,hnone]
  rfl

theorem sum_interior_bar_signs {M : Type*} [AddCommGroup M] (r : ℕ) (f : ℕ → M) :
    (∑ j∈Finset.range (r+2),if 0<j ∧ j<r+1 then (-1 : ℤˣ)^j • f (j-1) else 0)=
      ∑ i∈Finset.range r,(-1 : ℤˣ)^(i+1) • f i := by
  rw [Finset.sum_range_succ]
  simp only [lt_self_iff_false,and_false,if_false,add_zero]
  rw [Finset.sum_range_succ']
  simp only [Nat.lt_irrefl,false_and,if_false,add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < r := Finset.mem_range.mp hi
  rw [if_pos (by constructor <;> omega),Nat.add_sub_cancel]

set_option maxHeartbeats 800000 in
/-- The actual tensor sign convention is the negative of the recursive
positive-first-merge convention. Endpoints contribute zero because they
are mandatory, and every interior optional cut is retained. -/
theorem cutDifferential_transport_basis (W : List J) (r : ℕ)
    (L : ActualBarIndex e W (r+1)) :
    barWordMap (K := K) e W r
      (cutModelDifferential (K := K) (·≤·) W r
        (Finsupp.single (actualFactorization e W (r+1) L) 1))=
      -basisDifferential (normalProduct (K := K) e) L.val := by
  let A := actualFactorization e W (r+1) L
  let c := factorizationComposition W A.val.val
  have hc : c.length=L.val.length := by
    simp only [c,A,factorizationComposition,Composition.length,actualFactorization,
      List.length_map]
  rw [cutModelDifferential_single_merges,map_sum,negative_basisDifferential_expansion]
  calc
    (∑ j : Fin (c.length+1),barWordMap (K := K) e W r
      (if hj : c.boundary j∉mandatoryCuts (·≤·) W
        then (-1 : ℤˣ)^j.val • Finsupp.single (mergedBarIndex (·≤·) W r A j hj) (1 : K)
        else 0)) =
      ∑ j : Fin (c.length+1),if 0<j.val ∧ j.val<L.val.length
        then (-1 : ℤˣ)^j.val • adjacent (normalProduct (K := K) e) (j.val-1) L.val else 0 := by
      apply Finset.sum_congr rfl
      intro j hjmem
      by_cases hb : 0<j.val ∧ j.val<L.val.length
      · rw [if_pos hb]
        by_cases hj : c.boundary j∉mandatoryCuts (·≤·) W
        · rw [dif_pos hj,map_zsmul_unit,←adjacent_normalProduct_cut e W r L j hj]
        · rw [dif_neg hj,map_zero]
          have hi : j.val-1+1<L.val.length := by omega
          have hm : c.boundary
              ⟨j.val-1+1,by omega⟩∈mandatoryCuts (·≤·) W := by
            convert not_not.mp hj using 1
            congr 1
            apply Fin.ext
            change j.val-1+1=j.val
            omega
          rw [adjacent_normalProduct_zero_of_mandatory e W (r+1) L
            (j.val-1) hi hm,smul_zero]
      · have hj : ¬c.boundary j∉mandatoryCuts (·≤·) W := by
          intro hj
          have hp := optional_boundary_index_bounds (·≤·) W A.val j hj
          apply hb
          exact ⟨hp.1,by simpa only [A,actualFactorization,List.length_map] using hp.2⟩
        rw [dif_neg hj,if_neg hb,map_zero]
    _ = ∑ j∈Finset.range (c.length+1),if 0<j ∧ j<L.val.length
        then (-1 : ℤˣ)^j • adjacent (normalProduct (K := K) e) (j-1) L.val else 0 :=
      Fin.sum_univ_eq_sum_range
        (fun j : ℕ => if 0<j ∧ j<L.val.length then
          (-1 : ℤˣ)^j • adjacent (normalProduct (K := K) e) (j-1) L.val else 0)
        (c.length+1)
    _ = ∑ i∈Finset.range (L.val.length-1),
        (-1 : ℤˣ)^(i+1) • adjacent (normalProduct (K := K) e) i L.val := by
      rw [hc,L.property.2,Nat.add_sub_cancel]
      simpa only [Nat.add_assoc] using sum_interior_bar_signs r
        (fun i => adjacent (normalProduct (K := K) e) i L.val)

end PaperVerification.AlternatingForms.BarCompositions
end
end
end TAF_LiteralSource_0277

section TAF_LiteralSource_0278
/- Original module: PaperVerification.AlternatingFormsBarFiberCoordinates -/


/-!
# The cut decomposition in literal tensor coordinates

The inclusion of a fixed-word fiber sends each factorization to its
actual positive-basis tensor word. Its coordinates are a single outer
fiber. Consequently the leading degree differential has exactly the
normal adjacent-merge formula on each original tensor basis vector.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace PaperVerification.AlternatingForms.BarCompositions

open BarCoefficientFormula

variable {K C J : Type*} [CommRing K] [Preorder J] [Fintype J]
  (e : C ≃ PositiveNormalWord J)

theorem internalDegreeFiberCoordinates_apply (r N : ℕ)
    (z : internalDegreePiece (K := K) e r N)
    (W : {W : List J // W.length=N}) (L : BarIndex (·≤·) W.val r) :
    internalDegreeFiberCoordinates e r N z W L=
      z.val (factorizationBarWord e W.val L.val) := by
  rfl

theorem factorizationBarWord_injective (W : List J) (r : ℕ) :
    Function.Injective (fun L : BarIndex (·≤·) W r ↦ factorizationBarWord e W L.val) := by
  intro L M h
  apply (actualBarIndexEquiv e W r).symm.injective
  apply Subtype.ext
  change factorizationBarWord e W L.val = factorizationBarWord e W M.val
  exact h

theorem barWordMap_mem_internalDegree (r N : ℕ)
    (W : {W : List J // W.length=N}) (z : BarIndex (·≤·) W.val r →₀ K) :
    barWordMap e W.val r z∈internalDegreePiece (K := K) e r N := by
  induction z using Finsupp.induction_linear with
  | zero => simpa only [map_zero] using (internalDegreePiece (K := K) e r N).zero_mem
  | add z w hz hw => simpa only [map_add] using
      (internalDegreePiece (K := K) e r N).add_mem hz hw
  | single L c =>
    rw [barWordMap_single]
    apply Finsupp.single_mem_supported K c
    exact ⟨(factorizationBarWord_length e W.val L.val).trans L.property,
      by rw [factorizationBarWord_flatten]; exact W.property⟩

def fiberInclusion (r N : ℕ) (W : {W : List J // W.length=N}) :
    (BarIndex (·≤·) W.val r →₀ K) →ₗ[K] internalDegreePiece (K := K) e r N :=
  LinearMap.codRestrict _ (barWordMap e W.val r) (barWordMap_mem_internalDegree e r N W)

@[simp] theorem fiberInclusion_val (r N : ℕ) (W : {W : List J // W.length=N})
    (z : BarIndex (·≤·) W.val r →₀ K) :
    (fiberInclusion e r N W z).val=barWordMap e W.val r z := rfl

theorem internalDegreeFiberCoordinates_fiberInclusion (r N : ℕ)
    (W : {W : List J // W.length=N}) (z : BarIndex (·≤·) W.val r →₀ K) :
    internalDegreeFiberCoordinates e r N (fiberInclusion e r N W z)=Pi.single W z := by
  funext V
  ext L
  rw [internalDegreeFiberCoordinates_apply]
  change (Finsupp.mapDomain (fun T : BarIndex (·≤·) W.val r ↦
    factorizationBarWord e W.val T.val) z) (factorizationBarWord e V.val L.val)=_
  by_cases h : V=W
  · subst V
    rw [Finsupp.mapDomain_apply_of_injective (factorizationBarWord_injective e W.val r),
      Pi.single_eq_same]
  · have hn : factorizationBarWord e V.val L.val∉
        Set.range (fun T : BarIndex (·≤·) W.val r ↦ factorizationBarWord e W.val T.val) := by
      rintro ⟨T,hT⟩
      apply h
      apply Subtype.ext
      have hh := congrArg (flattenBarWord e) hT
      rw [factorizationBarWord_flatten,factorizationBarWord_flatten] at hh
      exact hh.symm
    rw [Finsupp.mapDomain_of_notMem_range _ _ hn,Pi.single_eq_of_ne h,Finsupp.zero_apply]

set_option maxHeartbeats 800000 in
theorem leadingDegreeDifferential_fiberInclusion (r N : ℕ)
    (W : {W : List J // W.length=N}) (z : BarIndex (·≤·) W.val (r+1) →₀ K) :
    leadingDegreeDifferential e r N (fiberInclusion e (r+1) N W z)=
      fiberInclusion e r N W (cutModelDifferential (·≤·) W.val r z) := by
  apply (internalDegreeFiberCoordinates e r N).injective
  rw [leadingDegreeDifferential_comm,internalDegreeFiberCoordinates_fiberInclusion,
    internalDegreeFiberCoordinates_fiberInclusion]
  exact leadingFiberDifferential_single r N W z

def tensorBasis (r N : ℕ) :
    Module.Basis (InternalDegreeIndex e r N) K (internalDegreePiece (K := K) e r N) :=
  .ofRepr (internalDegreeCoordinates e r N)

@[simp] theorem tensorBasis_val (r N : ℕ) (L : InternalDegreeIndex e r N) :
    (tensorBasis (K := K) e r N L).val=Finsupp.single L.val 1 := by
  change ((Finsupp.supportedEquivFinsupp (M := K) (R := K)
    {T : List C | T.length=r ∧ (flattenBarWord e T).length=N}).symm
      (Finsupp.single L 1)).val=Finsupp.single L.val 1
  exact Finsupp.supportedEquivFinsupp_symm_single _ _ _

@[simp] theorem tensorBasis_repr_apply (r N : ℕ)
    (z : internalDegreePiece (K := K) e r N) (L : InternalDegreeIndex e r N) :
    (tensorBasis e r N).repr z L=z.val L.val := rfl

theorem tensorBasis_repr_sub (r N : ℕ)
    (x y : internalDegreePiece (K := K) e r N) (L : InternalDegreeIndex e r N) :
    (tensorBasis e r N).repr (x-y) L=x.val L.val-y.val L.val := rfl

theorem tensorBasis_eq_fiberInclusion (r N : ℕ) (L : InternalDegreeIndex e r N) :
    tensorBasis (K := K) e r N L=
      fiberInclusion e r N ⟨flattenBarWord e L.val,L.property.2⟩
        (Finsupp.single (actualFactorization e (flattenBarWord e L.val) r
          ⟨L.val,rfl,L.property.1⟩) 1) := by
  apply Subtype.ext
  rw [tensorBasis_val,fiberInclusion_val,barWordMap_single]
  congr 1
  have h := (actualBarIndexEquiv e (flattenBarWord e L.val) r).left_inv
    ⟨L.val,rfl,L.property.1⟩
  have hw := congrArg
    (fun T : ActualBarIndex e (flattenBarWord e L.val) r => T.val) h
  exact hw.symm

/-- Coordinates of the leading operator on every original tensor. -/
theorem leadingDegreeDifferential_tensorBasis_val (r N : ℕ)
    (L : InternalDegreeIndex e (r+1) N) :
    (leadingDegreeDifferential e r N (tensorBasis (K := K) e (r+1) N L)).val=
      -basisDifferential (normalProduct e) L.val := by
  rw [tensorBasis_eq_fiberInclusion,leadingDegreeDifferential_fiberInclusion,
    fiberInclusion_val]
  exact cutDifferential_transport_basis e (flattenBarWord e L.val) r
    ⟨L.val,rfl,L.property.1⟩

end PaperVerification.AlternatingForms.BarCompositions
end
end
end TAF_LiteralSource_0278

section TAF_LiteralSource_0279
/- Original module: PaperVerification.AlternatingFormsOddBarExactness -/


/-! # Exactness of the actual odd normalized bar complex. -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
noncomputable section
open scoped Classical MonomialOrder

namespace PaperVerification.AlternatingForms

open Hibi BarCompositions BarCoefficientFormula PBWWords FilteredComparison
open PaperVerification.ReducedBarBasis PaperVerification.Fermion.BasisFiltered
open CategoryTheory CategoryTheory.Limits

universe u
variable {K : Type u} [Field K] [CharZero K]
  (k t : ℕ) (hs : t+2≤k+1)

local notation "C" => OddPositiveStandardIndex (K := K) k t hs
local notation "α" => oddIntervalLower k (t+2) hs
local notation "β" => oddIntervalUpper k (t+2) hs
local notation "J" => IntervalIndex α β
local notation "B" => oddAugmentedBasis (K := K) k t hs
local notation "e" => oddPositiveWordEquiv (K := K) k t hs

theorem oddNormalProduct_eq_normalProduct :
    oddNormalProduct (K := K) k t hs=normalProduct e := rfl

theorem oddLeadingDegreeDifferential_tensorBasis_val (r N : ℕ)
    (L : InternalDegreeIndex e (r+1) N) :
    (leadingDegreeDifferential e r N (tensorBasis (K := K) e (r+1) N L)).val=
      -oddNormalDifferentialBasis k t hs L.val := by
  rw [leadingDegreeDifferential_tensorBasis_val,←oddNormalProduct_eq_normalProduct]
  rfl

theorem oddBigradedDifferential_tensorBasis_val (r N : ℕ)
    (L : InternalDegreeIndex e (r+1) N) :
    (oddBigradedDifferential k t hs r N (tensorBasis (K := K) e (r+1) N L)).val=
      -differentialBasis B L.val := by
  rw [oddBigradedDifferential_val,tensorBasis_val,differential_single,one_smul]

def oddBarWordWeight (m : MonomialOrder J) (r N : ℕ)
    (L : InternalDegreeIndex e r N) : ℕ :=
  weight (oddGoodOrder k t hs m) (·≤·) N (flattenBarWord e L.val)

theorem oddLeadingDegreeDifferential_homogeneous (m : MonomialOrder J)
    (r N : ℕ) (L : InternalDegreeIndex e (r+1) N) :
    Homogeneous (R := K) (M := ↥(internalDegreePiece (K := K) e r N)) (tensorBasis (K := K) e r N) (oddBarWordWeight k t hs m r N)
      (oddBarWordWeight k t hs m (r+1) N L)
      (leadingDegreeDifferential e r N (tensorBasis e (r+1) N L)) := by
  intro T hT
  rw [tensorBasis_repr_apply,oddLeadingDegreeDifferential_tensorBasis_val,
    Finsupp.neg_apply,neg_ne_zero] at hT
  have hsame := oddNormalDifferentialBasis_mem_sameWord k t hs L.val
    (Finsupp.mem_support_iff.mpr hT)
  change weight (oddGoodOrder k t hs m) (·≤·) N (flattenBarWord e T.val)=
    weight (oddGoodOrder k t hs m) (·≤·) N (flattenBarWord e L.val)
  rw [hsame]

theorem oddBigradedDifferential_hasTop_basis (m : MonomialOrder J)
    (r N : ℕ) (L : InternalDegreeIndex e (r+1) N) :
    HasTop (R := K) (M := ↥(internalDegreePiece (K := K) e r N)) (tensorBasis (K := K) e r N) (oddBarWordWeight k t hs m r N)
      (oddBarWordWeight k t hs m (r+1) N L)
      (oddBigradedDifferential k t hs r N (tensorBasis e (r+1) N L))
      (leadingDegreeDifferential e r N (tensorBasis e (r+1) N L)) := by
  apply hasTop_of_strict_difference (K := K)
    (M₀ := ↥(internalDegreePiece (K := K) e r N))
    (tensorBasis (K := K) e r N) (oddBarWordWeight k t hs m r N)
  · exact oddLeadingDegreeDifferential_homogeneous k t hs m r N L
  · intro T hT
    have he : (tensorBasis (K := K) e r N).repr
        (oddBigradedDifferential k t hs r N (tensorBasis e (r+1) N L)-
          leadingDegreeDifferential e r N (tensorBasis e (r+1) N L)) T=
        -((differentialBasis B L.val-oddNormalDifferentialBasis k t hs L.val) T.val) := by
      rw [tensorBasis_repr_sub,oddBigradedDifferential_tensorBasis_val,
        oddLeadingDegreeDifferential_tensorBasis_val]
      simp only [Finsupp.neg_apply,Finsupp.sub_apply]
      abel
    rw [he,neg_ne_zero] at hT
    have hw := oddDifferentialBasis_difference_weight_lt k t hs m L.val T.val hT
    simpa only [oddBarWordWeight,L.property.2] using hw

/-- This is exactness of the genuine internally graded tensor differential
coming from the actual free resolution of the augmentation residue. -/
theorem oddBigradedDifferential_range_eq_ker (m : MonomialOrder J)
    (r N : ℕ) (hr : r+1≠N) :
    (oddBigradedDifferential (K := K) k t hs (r+1) N).range=
      (oddBigradedDifferential k t hs r N).ker := by
  exact range_eq_ker_of_basis (K := K)
    (M₀ := ↥(internalDegreePiece (K := K) e r N))
    (M₁ := ↥(internalDegreePiece (K := K) e (r+1) N))
    (M₂ := ↥(internalDegreePiece (K := K) e (r+2) N))
    (tensorBasis (K := K) e r N) (oddBarWordWeight k t hs m r N)
    (tensorBasis (K := K) e (r+1) N) (oddBarWordWeight k t hs m (r+1) N)
    (tensorBasis (K := K) e (r+2) N) (oddBarWordWeight k t hs m (r+2) N)
    (oddBigradedDifferential k t hs r N) (oddBigradedDifferential k t hs (r+1) N)
    (leadingDegreeDifferential e r N) (leadingDegreeDifferential e (r+1) N)
    (oddBigradedDifferential_squared k t hs r N)
    (oddBigradedDifferential_hasTop_basis k t hs m r N)
    (oddBigradedDifferential_hasTop_basis k t hs m (r+1) N)
    (leadingDegree_range_eq_ker e r N hr)

/-- Every actual off-diagonal normalized bar cycle is the differential of
an actual tensor of the next length and the same internal degree. -/
theorem odd_normalized_bar_off_diagonal (m : MonomialOrder J)
    (r N : ℕ) (hr : r+1≠N) (z : List C →₀ K)
    (hz : z∈internalDegreePiece (K := K) e (r+1) N)
    (hd : differential B z=0) :
    ∃ y∈internalDegreePiece (K := K) e (r+2) N,-differential B y=z := by
  have hc : (⟨z,hz⟩ : internalDegreePiece (K := K) e (r+1) N)∈
      (oddBigradedDifferential k t hs r N).ker := by
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    change -differential B z=0
    rw [hd,neg_zero]
  rw [←oddBigradedDifferential_range_eq_ker k t hs m r N hr] at hc
  obtain ⟨y,hy⟩ := hc
  exact ⟨y.val,y.property,congrArg Subtype.val hy⟩

theorem oddInternalDegreeComplex_exactAt_succ (m : MonomialOrder J)
    (r N : ℕ) (hr : r+1≠N) :
    (oddInternalDegreeComplex (K := K) k t hs N).ExactAt (r+1) := by
  rw [HomologicalComplex.exactAt_iff' _ (r+2) (r+1) r (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff_range_eq_ker]
  change (((oddInternalDegreeComplex (K := K) k t hs N).d (r+2) (r+1)).hom).range=
    (((oddInternalDegreeComplex (K := K) k t hs N).d (r+1) r).hom).ker
  rw [oddInternalDegreeComplex_d,oddInternalDegreeComplex_d]
  exact oddBigradedDifferential_range_eq_ker k t hs m r N hr

theorem oddInternalDegree_zero_eq_zero (N : ℕ) (hN : N≠0)
    (z : internalDegreePiece (K := K) e 0 N) : z=0 := by
  apply Subtype.ext
  apply Finsupp.ext
  intro L
  change z.val L=0
  apply (Finsupp.mem_supported' K z.val).mp z.property
  rintro ⟨hL,hW⟩
  have hnil : L=[] := List.length_eq_zero_iff.mp hL
  subst L
  exact hN hW.symm

/-- The homology here is Mathlib's actual homology of the actual
internal-degree subcomplex of the normalized Tor complex. -/
theorem odd_internal_bar_homology_off_diagonal (m : MonomialOrder J)
    (r N : ℕ) (hr : r≠N) :
    IsZero ((oddInternalDegreeComplex (K := K) k t hs N).homology r) := by
  apply HomologicalComplex.ExactAt.isZero_homology
  cases r with
  | zero =>
    apply HomologicalComplex.ExactAt.of_isZero
    change IsZero (ModuleCat.of K (internalDegreePiece (K := K) e 0 N))
    letI : Subsingleton (internalDegreePiece (K := K) e 0 N) :=
      ⟨fun x y ↦ (oddInternalDegree_zero_eq_zero k t hs N (Ne.symm hr) x).trans
        (oddInternalDegree_zero_eq_zero k t hs N (Ne.symm hr) y).symm⟩
    exact ModuleCat.isZero_of_subsingleton _
  | succ r => exact oddInternalDegreeComplex_exactAt_succ k t hs m r N hr

/-- The auxiliary monomial order is constructed, not supplied as a
hypothesis in the resulting diagonal homology statement. -/
theorem odd_actual_bar_homology_diagonal (r N : ℕ) (hr : r≠N) :
    IsZero ((oddInternalDegreeComplex (K := K) k t hs N).homology r) :=
  odd_internal_bar_homology_off_diagonal k t hs
    (PaperVerification.WeightedMonomialOrder.finiteBaseOrder J) r N hr

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0279

section TAF_LiteralSource_0280
/- Original module: PaperVerification.AlternatingFormsOddTorDegrees -/


/-!
# The internal pieces inside ordinary Tor

The degree projections below are coefficient projections for the actual
internal polynomial degrees. They commute with the genuine bar
differential, split its internal subcomplexes, and sum to every tensor.
The induced subspaces of ordinary Mathlib Tor therefore come from the
original grading. Off-diagonal vanishing is then a statement about these
actual Tor subspaces, not merely an unrelated combinatorial complex.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.AlternatingForms.BarDegrees

open PaperVerification.ReducedBarBasis PaperVerification.AugmentedAlgebraBasis

variable {K A C : Type*} [CommRing K] [Ring A] [Algebra K A]
  (B : Module.Basis (Option C) K A) (δ : C → ℕ)

def degreeProjection (N : ℕ) : (List C →₀ K) →ₗ[K] (List C →₀ K) where
  toFun z := z.filter (fun L ↦ totalDegree δ L=N)
  map_add' z w := Finsupp.filter_add
  map_smul' a z := Finsupp.filter_smul

@[simp] theorem degreeProjection_apply (N : ℕ) (z : List C →₀ K) (L : List C) :
    degreeProjection δ N z L=if totalDegree δ L=N then z L else 0 := rfl

theorem degreeProjection_single (N : ℕ) (L : List C) (c : K) :
    degreeProjection δ N (Finsupp.single L c)=
      if totalDegree δ L=N then Finsupp.single L c else 0 := by
  change (Finsupp.single L c).filter (fun T => totalDegree δ T=N)=
    if totalDegree δ L=N then Finsupp.single L c else 0
  by_cases h : totalDegree δ L=N
  · rw [if_pos h]
    exact Finsupp.filter_single_of_pos (fun T => totalDegree δ T=N) h
  · rw [if_neg h]
    exact Finsupp.filter_single_of_neg (fun T => totalDegree δ T=N) h

theorem degreeProjection_homogeneous (N M : ℕ) (z : List C →₀ K)
    (hz : z∈degreePiece δ M) :
    degreeProjection δ N z=if M=N then z else 0 := by
  by_cases h : M=N
  · subst M
    rw [if_pos rfl]
    apply (Finsupp.filter_eq_self_iff _ _).mpr
    intro L hL
    exact hz (Finsupp.mem_support_iff.mpr hL)
  · rw [if_neg h]
    apply (Finsupp.filter_eq_zero_iff _ _).mpr
    intro L hL
    apply (Finsupp.mem_supported' K z).mp hz
    intro hM
    exact h (hM.symm.trans hL)

variable (hδ : ∀ a b c,productCoefficients B a b c≠0 → δ c=δ a+δ b)

include hδ in
theorem differential_degreeProjection (N : ℕ) (z : List C →₀ K) :
    differential B (degreeProjection δ N z)=degreeProjection δ N (differential B z) := by
  have he : (differential B).comp (degreeProjection δ N)=
      (degreeProjection δ N).comp (differential B) := by
    apply Finsupp.lhom_ext
    intro L c
    simp only [LinearMap.comp_apply,degreeProjection_single,differential_single,map_smul]
    rw [degreeProjection_homogeneous δ N (totalDegree δ L) _
      (differentialBasis_mem_degreePiece B δ hδ L)]
    split_ifs <;> simp only [differential_single,map_zero,smul_zero]
  exact LinearMap.congr_fun he z

/-- Finite completeness of the internal-degree projections on every
actual tensor. No finite-degree bound on the entire bar term is assumed. -/
theorem sum_degreeProjection (z : List C →₀ K) :
    (∑ N∈z.support.image (totalDegree δ),degreeProjection δ N z)=z := by
  apply Finsupp.ext
  intro L
  change (Finsupp.applyAddHom L) (∑ N∈z.support.image (totalDegree δ),degreeProjection δ N z)=z L
  rw [map_sum]
  change (∑ N∈z.support.image (totalDegree δ),if totalDegree δ L=N then z L else 0)=z L
  rw [Finset.sum_eq_single (totalDegree δ L)]
  · rw [if_pos rfl]
  · intro N hN hne
    exact if_neg (Ne.symm hne)
  · intro hnot
    rw [if_pos rfl]
    by_contra hL
    exact hnot (Finset.mem_image.mpr ⟨L,Finsupp.mem_support_iff.mpr hL,rfl⟩)

end PaperVerification.AlternatingForms.BarDegrees

namespace PaperVerification.AlternatingForms

open BarCompositions BarDegrees PaperVerification.ReducedBarBasis
open CategoryTheory CategoryTheory.Limits

universe u
variable {K : Type u} [Field K] [CharZero K]
  (k t : ℕ) (hs : t+2≤k+1)

local notation "C" => OddPositiveStandardIndex (K := K) k t hs
local notation "B" => oddAugmentedBasis (K := K) k t hs
local notation "e" => oddPositiveWordEquiv (K := K) k t hs
local notation "δ" => oddPositiveDegree (K := K) k t hs
local notation "ε" => oddAugmentation (K := K) k t
local notation "ordinaryBar" => BarFree.reducedComplex ε B
  (oddAugmentedBasis_none k t hs) (oddAugmentation_positive k t hs)

theorem oddDegreeProjection_mem_internalDegree (r N : ℕ) (z : List C →₀ K)
    (hz : z∈BarFree.lengthPiece C K r) :
    degreeProjection δ N z∈internalDegreePiece (K := K) e r N := by
  intro L hL
  have hn := Finsupp.mem_support_iff.mp hL
  rw [degreeProjection_apply] at hn
  split_ifs at hn with hN
  · exact ⟨hz (Finsupp.mem_support_iff.mpr hn),
      by rw [oddBarWord_length_eq_degree]; exact hN⟩
  · exact False.elim (hn rfl)

def oddInternalDegreeProjection (r N : ℕ) :
    BarFree.lengthPiece C K r →ₗ[K] internalDegreePiece (K := K) e r N :=
  LinearMap.codRestrict _
    ((degreeProjection δ N).comp (BarFree.lengthPiece C K r).subtype)
    (fun z ↦ oddDegreeProjection_mem_internalDegree k t hs r N z.val z.property)

@[simp] theorem oddInternalDegreeProjection_val (r N : ℕ)
    (z : BarFree.lengthPiece C K r) :
    (oddInternalDegreeProjection k t hs r N z).val=degreeProjection δ N z.val := rfl

theorem oddInternalDegreeProjection_inclusion (r N : ℕ)
    (z : internalDegreePiece (K := K) e r N) :
    oddInternalDegreeProjection k t hs r N (oddInternalDegreeInclusion k t hs r N z)=z := by
  apply Subtype.ext
  have hz : z.val ∈ BarFree.lengthPiece C K r ⊓ degreePiece δ N :=
    (congrArg (fun U : Submodule K (List C →₀ K) => z.val ∈ U)
      (oddInternalDegreePiece_eq_inf (K := K) k t hs r N)).mp z.property
  exact (degreeProjection_homogeneous δ N N z.val hz.2).trans (if_pos rfl)

theorem oddInternalDegreeProjection_differential (r N : ℕ) :
    (oddInternalDegreeProjection k t hs r N).comp (BarFree.negativeReducedDegreeDifferential B r)=
      (oddBigradedDifferential k t hs r N).comp
        (oddInternalDegreeProjection k t hs (r+1) N) := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  change degreeProjection δ N (-differential B z.val)=
    -differential B (degreeProjection δ N z.val)
  rw [map_neg,differential_degreeProjection B δ (odd_productCoefficient_degree k t hs)]

def oddInternalDegreeProjectionChain (N : ℕ) :
    ordinaryBar ⟶ oddInternalDegreeComplex (K := K) k t hs N where
  f r := ModuleCat.ofHom (oddInternalDegreeProjection k t hs r N)
  comm' i j hij := by
    change j+1=i at hij
    subst i
    rw [oddInternalDegreeComplex_d,BarFree.reducedComplex_d]
    apply ModuleCat.hom_ext
    exact (oddInternalDegreeProjection_differential k t hs j N).symm

theorem oddInternalDegree_chain_retraction (N : ℕ) :
    oddInternalDegreeInclusionChain (K := K) k t hs N ≫
      oddInternalDegreeProjectionChain k t hs N=𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext r
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact oddInternalDegreeProjection_inclusion k t hs r N z

/-- The actual ordinary Tor subspace induced by internal degree N in
the original graded free bar resolution. -/
def oddTorInternalPiece (r N : ℕ) : Submodule K (BarFree.TorOverCoefficients ε r) :=
  LinearMap.range
    ((HomologicalComplex.homologyMap (oddInternalDegreeInclusionChain k t hs N) r ≫
      (oddNormalizedBarTorIso k t hs r).inv).hom)

theorem oddTorInternalPiece_eq_bot_of_ne (r N : ℕ) (hr : r≠N) :
    oddTorInternalPiece (K := K) k t hs r N=⊥ := by
  have hz := odd_actual_bar_homology_diagonal (K := K) k t hs r N hr
  have hmap : HomologicalComplex.homologyMap (oddInternalDegreeInclusionChain k t hs N) r ≫
      (oddNormalizedBarTorIso k t hs r).inv=0 := hz.eq_of_src _ _
  rw [oddTorInternalPiece,hmap,ModuleCat.hom_zero,LinearMap.range_zero]

/-- Internal degree is recovered injectively inside ordinary Tor, since
projection followed by inclusion is a retraction already on complexes. -/
theorem oddInternalHomology_injective (r N : ℕ) :
    Function.Injective
      (HomologicalComplex.homologyMap (oddInternalDegreeInclusionChain (K := K) k t hs N) r) := by
  have he := congrArg (fun f ↦ HomologicalComplex.homologyMap f r)
    (oddInternalDegree_chain_retraction (K := K) k t hs N)
  rw [HomologicalComplex.homologyMap_comp,HomologicalComplex.homologyMap_id] at he
  apply Function.LeftInverse.injective
    (g := HomologicalComplex.homologyMap (oddInternalDegreeProjectionChain k t hs N) r)
  intro z
  exact congrArg (fun f ↦ f z) he

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0280

section TAF_LiteralSource_0281
/- Original module: PaperVerification.AlternatingFormsOddTorPure -/


/-!
# Ordinary Tor is concentrated in its actual internal degree

Every bar tensor is the finite sum of its internal-degree projections.
The same decomposition holds on actual cycles and therefore on ordinary
Tor. Together with off-diagonal exactness, this identifies the genuine
internal-degree subspaces: the diagonal is all of Tor and every other
degree is zero. This is the homological concentration assertion, with
the original quotient, augmentation, and polynomial grading retained.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.AlternatingForms

open BarCompositions BarDegrees
open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u
variable {K : Type u} [Field K] [CharZero K]
  (k t : ℕ) (hs : t+2≤k+1)

local notation "C" => OddPositiveStandardIndex (K := K) k t hs
local notation "B" => oddAugmentedBasis (K := K) k t hs
local notation "e" => oddPositiveWordEquiv (K := K) k t hs
local notation "δ" => oddPositiveDegree (K := K) k t hs
local notation "ε" => oddAugmentation (K := K) k t
local notation "ordinaryBar" => BarFree.reducedComplex ε B
  (oddAugmentedBasis_none k t hs) (oddAugmentation_positive k t hs)

def oddDegreeEndomorphism (N : ℕ) : ordinaryBar ⟶ ordinaryBar :=
  oddInternalDegreeProjectionChain (K := K) k t hs N ≫ oddInternalDegreeInclusionChain (K := K) k t hs N

theorem oddDegreeEndomorphism_f_val (r N : ℕ) (z : BarFree.lengthPiece C K r) :
    ((oddDegreeEndomorphism (K := K) k t hs N).f r z).val=degreeProjection δ N z.val := rfl

theorem oddDegreeCycles_value (r N : ℕ) (c : (ordinaryBar).cycles r) :
    (((ordinaryBar).iCycles r) (cyclesMap (oddDegreeEndomorphism (K := K) k t hs N) r c)).val=
      degreeProjection δ N (((ordinaryBar).iCycles r) c).val := by
  have he := congrArg (fun f ↦ f c) (cyclesMap_i (oddDegreeEndomorphism (K := K) k t hs N) r)
  exact congrArg Subtype.val he

theorem sum_oddDegreeCycles (r : ℕ) (c : (ordinaryBar).cycles r) :
    (∑ N∈(((ordinaryBar).iCycles r) c).val.support.image (totalDegree δ),
      cyclesMap (oddDegreeEndomorphism (K := K) k t hs N) r c)=c := by
  apply (ModuleCat.mono_iff_injective ((ordinaryBar).iCycles r)).mp inferInstance
  rw [map_sum]
  apply Subtype.ext
  rw [Submodule.coe_sum]
  simp_rw [oddDegreeCycles_value]
  exact sum_degreeProjection δ (((ordinaryBar).iCycles r) c).val

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Completeness of the original internal grading on the actual Tor
group. This rules out a vacuous selection of purported degree pieces. -/
theorem oddTorInternalPieces_iSup (r : ℕ) :
    (⨆ N,oddTorInternalPiece (K := K) k t hs r N)=⊤ := by
  apply top_unique
  intro x hx
  obtain ⟨c,hc⟩ :=
    (ModuleCat.epi_iff_surjective ((ordinaryBar).homologyπ r)).mp inferInstance
      ((oddNormalizedBarTorIso (K := K) k t hs r).hom x)
  let S := (((ordinaryBar).iCycles r) c).val.support.image (totalDegree δ)
  have hsum :
      (∑ N∈S,(oddNormalizedBarTorIso (K := K) k t hs r).inv
        (((ordinaryBar).homologyπ r) (cyclesMap (oddDegreeEndomorphism (K := K) k t hs N) r c)))=x := by
    calc
      _ = (oddNormalizedBarTorIso (K := K) k t hs r).inv (((ordinaryBar).homologyπ r)
          (∑ N∈S,cyclesMap (oddDegreeEndomorphism (K := K) k t hs N) r c)) := by
        rw [map_sum,map_sum]
      _ = (oddNormalizedBarTorIso (K := K) k t hs r).inv (((ordinaryBar).homologyπ r) c) := by
        rw [sum_oddDegreeCycles]
      _ = x := by
        rw [hc]
        exact congrArg (fun f ↦ f x) (oddNormalizedBarTorIso (K := K) k t hs r).hom_inv_id
  rw [←hsum]
  apply Submodule.sum_mem
  intro N hN
  apply (le_iSup (fun N ↦ oddTorInternalPiece (K := K) k t hs r N) N)
  refine ⟨homologyMap (oddInternalDegreeProjectionChain (K := K) k t hs N) r
    (((ordinaryBar).homologyπ r) c),?_⟩
  change (oddNormalizedBarTorIso (K := K) k t hs r).inv
    (homologyMap (oddInternalDegreeInclusionChain (K := K) k t hs N) r
      (homologyMap (oddInternalDegreeProjectionChain (K := K) k t hs N) r
        (((ordinaryBar).homologyπ r) c)))=_
  apply congrArg (oddNormalizedBarTorIso (K := K) k t hs r).inv
  have he := congrArg (fun f ↦ f c)
    (homologyπ_naturality (oddDegreeEndomorphism (K := K) k t hs N) r)
  simpa only [oddDegreeEndomorphism,homologyMap_comp,ModuleCat.comp_apply] using he

theorem oddTorInternalPiece_diagonal (r : ℕ) :
    oddTorInternalPiece (K := K) k t hs r r=⊤ := by
  have hle : (⨆ N,oddTorInternalPiece (K := K) k t hs r N)≤
      oddTorInternalPiece (K := K) k t hs r r := by
    apply iSup_le
    intro N
    by_cases h : N=r
    · subst N
      exact le_rfl
    · rw [oddTorInternalPiece_eq_bot_of_ne (K := K) k t hs r N (Ne.symm h)]
      exact bot_le
  rw [oddTorInternalPieces_iSup] at hle
  exact top_unique hle

/-- The actual Tor concentration assertion for every homological and
internal degree of the original odd isotropic Plucker ring. -/
theorem odd_actual_Tor_internal_degree (r N : ℕ) :
    oddTorInternalPiece (K := K) k t hs r N=if N=r then ⊤ else ⊥ := by
  by_cases h : N=r
  · subst N
    rw [if_pos rfl,oddTorInternalPiece_diagonal]
  · rw [if_neg h,oddTorInternalPiece_eq_bot_of_ne (K := K) k t hs r N (Ne.symm h)]

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0281

section TAF_LiteralSource_0282
/- Original module: PaperVerification.AlternatingFormsOnePlane -/


/-!
# The one-plane boundary of the odd degeneration theorem

Every alternating form vanishes on a one-dimensional subspace. The generic
one-row minor map is an actual polynomial-ring isomorphism, so its kernel and
every weighted initial ideal are zero. The Rees construction therefore gives
the literal trivial flat family, and the empty set is its quadratic Gröbner basis.

This file reconstructs the lost boundary source; it is not yet a checked theorem
of this run.
-/

@[expose] public section
noncomputable section

open scoped BigOperators

namespace PaperVerification.AlternatingForms

open MvPolynomial PaperVerification.WeightedInitialFiber

variable {K : Type*} [Field K] {n : ℕ}

/-- The unique one-entry increasing column with the prescribed entry. -/
@[expose]
def onePlaneIndex (i : Fin n) : PluckerIndex 1 n :=
  ⟨fun _ ↦ i, fun a b hab ↦ by
    have h : a = b := Subsingleton.elim _ _
    exact (not_lt_of_ge h.ge hab).elim⟩

@[simp]
theorem onePlaneIndex_entry (i : Fin n) (a : Fin 1) :
    (onePlaneIndex i).val a = i := rfl

@[simp]
theorem onePlaneIndex_eta (I : PluckerIndex 1 n) :
    onePlaneIndex (I.val 0) = I := by
  apply Subtype.ext
  funext a
  have h : a = 0 := Subsingleton.elim _ _
  rw [h]
  rfl

/-- A single-row determinant is the corresponding independent matrix entry. -/
@[simp]
theorem onePlane_genericMinor (I : PluckerIndex 1 n) :
    genericPluckerMinor (K := K) I = X (0, I.val 0) := by
  simp only [genericPluckerMinor, Matrix.det_fin_one, Matrix.of_apply]

/-- The inverse of the literal generic one-row minor map. -/
def onePlaneGenericInverse :
    MvPolynomial (Fin 1 × Fin n) K →ₐ[K] MvPolynomial (PluckerIndex 1 n) K :=
  aeval fun ij ↦ X (onePlaneIndex ij.2)

theorem onePlaneGenericInverse_comp :
    (onePlaneGenericInverse (K := K) (n := n)).comp genericPluckerMap =
      AlgHom.id K _ := by
  ext I
  simp [genericPluckerMap, onePlaneGenericInverse]

theorem onePlaneGenericMap_comp :
    (genericPluckerMap (K := K) (s := 1) (n := n)).comp onePlaneGenericInverse =
      AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  simp [genericPluckerMap, onePlaneGenericInverse]

def onePlaneGenericMapEquiv :
    MvPolynomial (PluckerIndex 1 n) K ≃ₐ[K] MvPolynomial (Fin 1 × Fin n) K :=
  AlgEquiv.ofAlgHom genericPluckerMap onePlaneGenericInverse
    onePlaneGenericMap_comp onePlaneGenericInverse_comp

/-- There are no polynomial relations among the one-row minors. -/
theorem onePlane_matrixPluckerIdeal :
    matrixPluckerIdeal (K := K) (s := 1) (n := n) = ⊥ := by
  change RingHom.ker
    (genericPluckerMap (K := K) (s := 1) (n := n)).toRingHom = ⊥
  apply (RingHom.injective_iff_ker_eq_bot _).mp
  exact (onePlaneGenericMapEquiv (K := K) (n := n)).injective

def onePlanePluckerRingEquiv :
    (MvPolynomial (PluckerIndex 1 n) K ⧸ matrixPluckerIdeal) ≃ₐ[K]
      MvPolynomial (Fin 1 × Fin n) K :=
  (Ideal.quotientEquivAlgOfEq K onePlane_matrixPluckerIdeal).trans
    ((AlgEquiv.quotientBot K _).trans onePlaneGenericMapEquiv)

/-- Literal alternating row evaluation vanishes on any two multiples of
one vector, over every commutative coefficient algebra. -/
theorem onePlane_row_isotropic {R : Type*} [CommRing R] [Algebra K R]
    (f : StrictPairs n → K) (u : Fin n → R) (a b : R) :
    (∑ ij : StrictPairs n, f ij •
      ((a * u ij.val.1) * (b * u ij.val.2) -
        (a * u ij.val.2) * (b * u ij.val.1))) = 0 := by
  apply Finset.sum_eq_zero
  intro ij _
  have h : (a * u ij.val.1) * (b * u ij.val.2) =
      (a * u ij.val.2) * (b * u ij.val.1) := by ring
  rw [h, sub_self, smul_zero]

theorem onePlane_initialIdeal (w : PluckerIndex 1 n → ℕ) :
    initialIdeal (matrixPluckerIdeal (K := K) (s := 1) (n := n)) w =
      matrixPluckerIdeal := by
  rw [onePlane_matrixPluckerIdeal]
  apply le_antisymm ?_ bot_le
  apply Ideal.span_le.mpr
  rintro _ ⟨p, hp, rfl⟩
  have hp' : p = 0 := Ideal.mem_bot.mp hp
  rw [hp']
  simp [initialForm]

/-- The one-plane family, with its original polynomial presentation. -/
theorem onePlane_flat_family (w : PluckerIndex 1 n → ℕ) :
    Module.Flat (Polynomial K)
      (reesAlgebra (matrixPluckerIdeal (K := K) (s := 1) (n := n)) w) ∧
    Nonempty (ZeroFiber (matrixPluckerIdeal (K := K) (s := 1) (n := n)) w ≃ₐ[K]
      MvPolynomial (PluckerIndex 1 n) K ⧸ matrixPluckerIdeal) ∧
    ∀ c : K, c ≠ 0 →
      Nonempty (ParameterFiber (matrixPluckerIdeal (K := K) (s := 1) (n := n)) w c ≃ₐ[K]
        MvPolynomial (PluckerIndex 1 n) K ⧸ matrixPluckerIdeal) := by
  refine ⟨inferInstance, ?_, fun c hc ↦ ⟨nonzeroFiberEquiv _ _ c hc⟩⟩
  exact ⟨(initialQuotientEquiv _ _).symm.trans
    (Ideal.quotientEquivAlgOfEq K (onePlane_initialIdeal w))⟩

/-- The empty set is a finite homogeneous-quadratic Gröbner basis of the
actual one-row Plücker kernel. -/
theorem onePlane_quadratic_groebner (m : MonomialOrder (PluckerIndex 1 n)) :
    (∅ : Set (MvPolynomial (PluckerIndex 1 n) K)).Finite ∧
    (∀ p ∈ (∅ : Set (MvPolynomial (PluckerIndex 1 n) K)), p.IsHomogeneous 2) ∧
    m.IsGroebnerBasis ∅ (matrixPluckerIdeal (K := K) (s := 1) (n := n)) := by
  refine ⟨Set.finite_empty, by simp, ?_⟩
  rw [onePlane_matrixPluckerIdeal, MonomialOrder.isGroebnerBasis_iff]
  constructor
  · exact Set.empty_subset _
  · simp [MonomialOrder.leadingTerm_zero]

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0282

section TAF_LiteralSource_0283
/- Original module: TauCeti.Algebra.Homology.HomologicalComplex.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Additional API for homological complexes

This file records additivity of the cycles functor, degreewise recursion for powers of a
complex endomorphism, and the existence of coproducts of complexes, computed degreewise. It also
records the basic properties of the maps
`K.toCycles i j : K.X i ⟶ K.cycles j` induced by the differentials: they kill the cycles in degree
`i`, commute with morphisms of complexes, vanish after a morphism from a complex concentrated in
degree `i`, and are epimorphisms in degrees where the complex is exact. In a degree with no nonzero
differential into it, the identification of the homology with the cycles is natural
(`HomologicalComplex.isoHomologyπ_inv_naturality`). The sequence
`Zᵢ ⟶ Kᵢ ⟶ Zⱼ` of cycles is exact when `j = c.next i`
(`HomologicalComplex.cyclesShortComplex_exact`). For adjacent degrees `i` and `j`, the cycles of a
complex exact in degree `j` fit into a short exact sequence `0 ⟶ Zᵢ ⟶ Kᵢ ⟶ Zⱼ ⟶ 0`
(`HomologicalComplex.cyclesShortComplex_shortExact`), which stays short exact when its outer terms
are replaced by isomorphic objects (`HomologicalComplex.cyclesShortComplex_shortExact_of_iso`);
likewise a monomorphism onto the kernel of the differential `Kᵢ ⟶ Kⱼ` gives a short exact sequence
`0 ⟶ A ⟶ Kᵢ ⟶ Zⱼ ⟶ 0` (`HomologicalComplex.shortExact_toCycles`). Constructing the bundled cycle
sequence requires homology only in the two selected degrees.
The exactness results additionally require homology of the cycle sequence itself.
For chain complexes indexed by the natural numbers, the identification of zero chains with
cycles is natural (`ChainComplex.cycles₀Iso_inv_naturality`), and so is the passage from zero
chains to zeroth homology (`ChainComplex.pOpcycles_comp_isoHomologyι₀_inv_comp_homologyMap`).
The isomorphisms `homologyIsoSc'`
are natural (`HomologicalComplex.homologyMap_comp_homologyIsoSc'_hom`), and exactness in a degree
is the vanishing of the homology of the short complex `sc'` there
(`HomologicalComplex.exactAt_iff_isZero_homology_sc'`).
Homology of complexes commutes with an additive functor preserving homology
(`CategoryTheory.Functor.mapHomologicalComplexCompHomologyFunctorIso`), the complex-level form of
Mathlib's `CategoryTheory.ShortComplex.homologyFunctorIso`.
-/

public section

open CategoryTheory Limits

universe w v u

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {ι : Type*}
  {c : ComplexShape ι} {K : HomologicalComplex C c} {s : K ⟶ K}

/-- Degreewise recursion for the powers of a chain endomorphism. -/
lemma pow_f_succ (m : ℕ) (i : ι) :
    (End.of s ^ (m + 1)).asHom.f i = (End.of s ^ m).asHom.f i ≫ s.f i := by
  rw [pow_succ', End.mul_asHom, comp_f]

/-- Homological complexes have the coproducts that the underlying category has. They are
computed degreewise. -/
instance hasCoproducts [HasCoproducts.{w} C] : HasCoproducts.{w} (HomologicalComplex C c) :=
  fun _ ↦ inferInstance

/-! ### The maps onto the cycles -/

section Cycles

variable (K) {L : HomologicalComplex C c}

/-- The map from the cycles in degree `i` to the cycles in degree `j` induced by the differential
vanishes. -/
@[reassoc]
lemma iCycles_toCycles (i j : ι) [K.HasHomology i] [K.HasHomology j] :
    K.iCycles i ≫ K.toCycles i j = 0 := by
  rw [← cancel_mono (K.iCycles j), Category.assoc, toCycles_i, iCycles_d, zero_comp]

/-- The short complex `Zᵢ(K) ⟶ Kᵢ ⟶ Zⱼ(K)` cut out of a homological complex. Its
second map is the differential with codomain restricted to the cycles in degree `j`. -/
noncomputable def cyclesShortComplex (i j : ι) [K.HasHomology i] [K.HasHomology j] :
    ShortComplex C :=
  ShortComplex.mk (K.iCycles i) (K.toCycles i j) (K.iCycles_toCycles i j)

/-- The cycle sequence is formed by the inclusion of cycles and the corestricted differential. -/
lemma cyclesShortComplex_def (i j : ι) [K.HasHomology i] [K.HasHomology j] :
    K.cyclesShortComplex i j =
      ShortComplex.mk (K.iCycles i) (K.toCycles i j) (K.iCycles_toCycles i j) := (rfl)

@[simp]
lemma cyclesShortComplex_X₁ (i j : ι) [K.HasHomology i] [K.HasHomology j] :
    (K.cyclesShortComplex i j).X₁ = K.cycles i := (rfl)

@[simp]
lemma cyclesShortComplex_X₂ (i j : ι) [K.HasHomology i] [K.HasHomology j] :
    (K.cyclesShortComplex i j).X₂ = K.X i := (rfl)

@[simp]
lemma cyclesShortComplex_X₃ (i j : ι) [K.HasHomology i] [K.HasHomology j] :
    (K.cyclesShortComplex i j).X₃ = K.cycles j := (rfl)

/-- The first map of the cycle sequence is the inclusion of cycles, transported along the
object equalities `cyclesShortComplex_X₁` and `cyclesShortComplex_X₂`. -/
@[simp]
lemma cyclesShortComplex_f (i j : ι) [K.HasHomology i] [K.HasHomology j] :
    (K.cyclesShortComplex i j).f = eqToHom (K.cyclesShortComplex_X₁ i j) ≫ K.iCycles i ≫
      eqToHom (K.cyclesShortComplex_X₂ i j).symm :=
  (Category.comp_id _).symm.trans (Category.id_comp _).symm

/-- The second map of the cycle sequence is the corestricted differential, transported along the
object equalities `cyclesShortComplex_X₂` and `cyclesShortComplex_X₃`. -/
@[simp]
lemma cyclesShortComplex_g (i j : ι) [K.HasHomology i] [K.HasHomology j] :
    (K.cyclesShortComplex i j).g = eqToHom (K.cyclesShortComplex_X₂ i j) ≫ K.toCycles i j ≫
      eqToHom (K.cyclesShortComplex_X₃ i j).symm :=
  (Category.comp_id _).symm.trans (Category.id_comp _).symm

variable {K}

/-- The maps onto the cycles induced by the differentials commute with morphisms of complexes. -/
@[reassoc]
lemma toCycles_cyclesMap (φ : K ⟶ L) (i j : ι) [K.HasHomology j] [L.HasHomology j] :
    K.toCycles i j ≫ cyclesMap φ j = φ.f i ≫ L.toCycles i j :=
  (cancel_mono (L.iCycles j)).1 <| by simp

/-- In a degree `j` with no nonzero differential into it, the identifications
`K.isoHomologyπ i j` of the homology with the cycles commute with the maps induced by a morphism of
complexes. -/
@[reassoc]
lemma isoHomologyπ_inv_naturality (φ : K ⟶ L) (i j : ι) (hi : c.prev j = i) (hK : K.d i j = 0)
    (hL : L.d i j = 0) [K.HasHomology j] [L.HasHomology j] :
    homologyMap φ j ≫ (L.isoHomologyπ i j hi hL).inv =
      (K.isoHomologyπ i j hi hK).inv ≫ cyclesMap φ j := by
  rw [← cancel_epi (K.isoHomologyπ i j hi hK).hom]
  simp

variable [HasZeroObject C] [DecidableEq ι] {i : ι} {X : C}

/-- A morphism from a complex concentrated in degree `i` vanishes after the differential out of
degree `i`. -/
@[reassoc]
lemma single_f_d (g : (single C c i).obj X ⟶ L) (j : ι) : g.f i ≫ L.d i j = 0 := by
  rw [g.comm i j, single_obj_d, zero_comp]

/-- A morphism from a complex concentrated in degree `i` vanishes after the map onto the cycles in
degree `j`. -/
@[reassoc]
lemma single_f_toCycles (g : (single C c i).obj X ⟶ L) (j : ι) [L.HasHomology j] :
    g.f i ≫ L.toCycles i j = 0 := by
  rw [← cancel_mono (L.iCycles j), Category.assoc, toCycles_i, single_f_d, zero_comp]

end Cycles

end HomologicalComplex

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {ι : Type*}
  {c : ComplexShape ι} {K : HomologicalComplex C c}

variable (K) in
/-- The sequence `Zᵢ ⟶ Kᵢ ⟶ Zⱼ` of the cycles of a complex `K` is exact when `j` is the degree
following `i`: the cycles in degree `i` are the kernel of the differential. -/
lemma cyclesShortComplex_exact (i j : ι) [K.HasHomology i] [K.HasHomology j]
    [hH : (K.cyclesShortComplex i j).HasHomology] (hij : c.next i = j) :
    (K.cyclesShortComplex i j).Exact := by
  rw [cyclesShortComplex_def] at hH ⊢
  let S := ShortComplex.mk _ _ (K.iCycles_toCycles i j)
  have hS := isKernelOfComp (K.iCycles j) (K.d i j) (K.cyclesIsKernel i j hij)
    (K.iCycles_toCycles i j) (K.toCycles_i i j)
  rw [S.exact_iff_iCycles_pOpcycles_zero]
  have h : hS.lift (KernelFork.ofι S.iCycles S.iCycles_g) ≫ S.f = S.iCycles :=
    Fork.IsLimit.lift_ι _
  rw [← h, Category.assoc, S.f_pOpcycles, comp_zero]

/-- A morphism killed by the differential `Kᵢ ⟶ Kⱼ` is killed by its corestriction to the
cycles in degree `j`. -/
lemma comp_toCycles_eq_zero {A : C} {i : ι} (j : ι) [K.HasHomology j] (a : A ⟶ K.X i)
    (ha : a ≫ K.d i j = 0) : a ≫ K.toCycles i j = 0 := by
  rw [← cancel_mono (K.iCycles j), Category.assoc, K.toCycles_i, ha, zero_comp]

/-- The corestriction `Kᵢ ⟶ Zⱼ` of the differential has the same kernel as the differential
`Kᵢ ⟶ Kⱼ`: if `A ⟶ Kᵢ ⟶ Kⱼ` is exact, then so is `A ⟶ Kᵢ ⟶ Zⱼ`. -/
lemma exact_toCycles {A : C} {i : ι} (j : ι) [K.HasHomology j] (a : A ⟶ K.X i)
    (ha : a ≫ K.d i j = 0) (hex : (ShortComplex.mk a (K.d i j) ha).Exact) :
    (ShortComplex.mk a (K.toCycles i j) (comp_toCycles_eq_zero j a ha)).Exact :=
  (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
    (S₁ := ShortComplex.mk a (K.toCycles i j) (comp_toCycles_eq_zero j a ha))
    (S₂ := ShortComplex.mk a (K.d i j) ha)
    { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := K.iCycles j }).2 hex

end HomologicalComplex

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] {ι : Type*}
  {c : ComplexShape ι} {K : HomologicalComplex C c}

/-- In a complex exact in degree `j`, the map onto the cycles in degree `j` from the preceding
degree is an epimorphism. -/
lemma epi_toCycles_of_exactAt {i j : ι} [K.HasHomology j]
    (h : K.ExactAt j) (hij : c.prev j = i) :
    Epi (K.toCycles i j) := by
  rw [exactAt_iff' _ i j (c.next j) hij rfl] at h
  have := h.hasHomology
  rw [← epi_comp_iff_of_isIso _ (K.cyclesIsoSc' i j (c.next j) hij rfl).hom,
    K.toCycles_cyclesIsoSc'_hom]
  exact h.epi_toCycles

/-- The cycle sequence `Zᵢ(K) ⟶ Kᵢ ⟶ Zⱼ(K)` is short exact when `i` and `j` are adjacent
and `K` is exact in degree `j`. -/
lemma cyclesShortComplex_shortExact (i j : ι) [K.HasHomology i] [K.HasHomology j]
    [(K.cyclesShortComplex i j).HasHomology]
    (hij : c.Rel i j) (hK : K.ExactAt j) : (K.cyclesShortComplex i j).ShortExact := by
  have hE := K.cyclesShortComplex_exact i j (c.next_eq' hij)
  rw [cyclesShortComplex_def] at hE ⊢
  exact ShortComplex.ShortExact.mk' hE
    inferInstance (epi_toCycles_of_exactAt hK (c.prev_eq' hij))

/-- The cycle sequence `Zᵢ(K) ⟶ Kᵢ ⟶ Zⱼ(K)`, with its outer terms replaced along isomorphisms
`X ≅ Zᵢ(K)` and `Zⱼ(K) ≅ Y`, is short exact when `i` and `j` are adjacent and `K` is exact in
degree `j`. -/
lemma cyclesShortComplex_shortExact_of_iso {i j : ι} [K.HasHomology i] [K.HasHomology j]
    [(K.cyclesShortComplex i j).HasHomology] (hij : c.Rel i j) (hK : K.ExactAt j) {X Y : C}
    (e : X ≅ K.cycles i) (e' : K.cycles j ≅ Y) :
    (ShortComplex.mk (e.hom ≫ K.iCycles i) (K.toCycles i j ≫ e'.hom)
      (by simp [iCycles_toCycles_assoc])).ShortExact :=
  ShortComplex.shortExact_of_iso (ShortComplex.isoMk e.symm (Iso.refl (K.X i)) e') <|
    K.cyclesShortComplex_def i j ▸ K.cyclesShortComplex_shortExact i j hij hK

/-- A monomorphism `A ⟶ Kᵢ` onto the kernel of the differential `Kᵢ ⟶ Kⱼ` fits into a short exact
sequence `0 ⟶ A ⟶ Kᵢ ⟶ Zⱼ ⟶ 0` when `i` precedes `j` and `K` is exact in degree `j`. -/
lemma shortExact_toCycles {A : C} {i j : ι} [K.HasHomology j] (a : A ⟶ K.X i) [Mono a]
    (ha : a ≫ K.d i j = 0) (hex : (ShortComplex.mk a (K.d i j) ha).Exact)
    (hij : c.prev j = i) (hK : K.ExactAt j) :
    (ShortComplex.mk a (K.toCycles i j) (comp_toCycles_eq_zero j a ha)).ShortExact :=
  have := epi_toCycles_of_exactAt hK hij
  { exact := exact_toCycles j a ha hex }

end HomologicalComplex

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] {ι : Type*} {c : ComplexShape ι}
  {K L : HomologicalComplex C c}

/-- Taking cycles is additive on morphisms of complexes. -/
@[simp]
lemma cyclesMap_add (f g : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i] :
    cyclesMap (f + g) i = cyclesMap f i + cyclesMap g i := by
  apply (cancel_mono (L.iCycles i)).1
  simp only [Preadditive.add_comp, cyclesMap_i, add_f_apply, Preadditive.comp_add]

instance cyclesFunctor_additive [CategoryWithHomology C] (i : ι) :
    (cyclesFunctor C c i).Additive where
  map_add := by
    intro X Y f g
    -- `cyclesFunctor` is opaque, so expose its defining map before applying the map-level API.
    change cyclesMap (f + g) i = cyclesMap f i + cyclesMap g i
    exact cyclesMap_add f g i

section HomologyIsoSc'

variable {C : Type*} [Category* C] [HasZeroMorphisms C] {ι : Type*}
  {c : ComplexShape ι} {K L : HomologicalComplex C c} (f : K ⟶ L) (i j k : ι)
  (hi : c.prev j = i) (hk : c.next j = k) [K.HasHomology j] [L.HasHomology j]
  [(K.sc' i j k).HasHomology] [(L.sc' i j k).HasHomology]

/-- The isomorphisms `homologyIsoSc'` are natural (this is the naturality of Mathlib's
`homologyFunctorIso'`, for complexes which only individually have homology). -/
@[reassoc]
lemma homologyMap_comp_homologyIsoSc'_hom :
    homologyMap f j ≫ (L.homologyIsoSc' i j k hi hk).hom =
      (K.homologyIsoSc' i j k hi hk).hom ≫
        ShortComplex.homologyMap ((shortComplexFunctor' C c i j k).map f) := by
  rw [homologyIsoSc', homologyIsoSc', ShortComplex.homologyMapIso_hom,
    ShortComplex.homologyMapIso_hom, homologyMap]
  -- the source of `homologyMap f j` is `K.homology j`, which is `(K.sc j).homology` only up to
  -- unfolding `HomologicalComplex.homology`, so the generic `homologyMap_comp` needs `erw`
  erw [← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp]
  congr 1
  exact (natIsoSc' C c i j k hi hk).hom.naturality f

end HomologyIsoSc'

/-- A homological complex is exact at `j` exactly when the homology of its short complex at `j`,
with explicit neighbouring indices, is zero. -/
lemma exactAt_iff_isZero_homology_sc' {C : Type*} [Category* C] [HasZeroMorphisms C] {ι : Type*}
    {c : ComplexShape ι} (L : HomologicalComplex C c) (i j k : ι) (hi : c.prev j = i)
    (hk : c.next j = k) [(L.sc' i j k).HasHomology] :
    L.ExactAt j ↔ IsZero (L.sc' i j k).homology :=
  (exactAt_iff' L i j k hi hk).trans (ShortComplex.exact_iff_isZero_homology _)

end HomologicalComplex

namespace ChainComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {K L : ChainComplex C ℕ} [K.HasHomology 0] [L.HasHomology 0]

/-- The identification of degree-zero chains with degree-zero cycles is natural. -/
@[reassoc]
lemma cycles₀Iso_inv_naturality (φ : K ⟶ L) :
    K.cycles₀Iso.inv ≫ HomologicalComplex.cyclesMap φ 0 =
      φ.f 0 ≫ L.cycles₀Iso.inv := by
  apply (cancel_mono (L.iCycles 0)).1
  simp

/-- The passage from degree-zero chains to degree-zero homology, through the identification of
the homology with the opcycles, is natural. -/
@[reassoc]
lemma pOpcycles_comp_isoHomologyι₀_inv_comp_homologyMap (φ : K ⟶ L) :
    K.pOpcycles 0 ≫ K.isoHomologyι₀.inv ≫ HomologicalComplex.homologyMap φ 0 =
      φ.f 0 ≫ L.pOpcycles 0 ≫ L.isoHomologyι₀.inv := by
  rw [ChainComplex.isoHomologyι₀_inv_naturality, HomologicalComplex.p_opcyclesMap_assoc]

end ChainComplex

namespace HomologicalComplex

section HomologyTransport

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [CategoryWithHomology C]
  {ι : Type*} {c : ComplexShape ι} {L L' M M' : HomologicalComplex C c}

/-- A morphism transported along equalities of complexes induces the corresponding transport
of the homology map. -/
lemma homologyMap_comp_eqToHom (ψ : L ⟶ L') (hM : M = L) (hM' : M' = L')
    (τ : M ⟶ M') (hτ : τ = eqToHom hM ≫ ψ ≫ eqToHom hM'.symm) (q : ι) :
    homologyMap τ q ≫ eqToHom (congrArg (·.homology q) hM') =
      eqToHom (congrArg (·.homology q) hM) ≫ homologyMap ψ q := by
  subst hM hM' hτ
  simp

end HomologyTransport

end HomologicalComplex

namespace CategoryTheory.Functor

variable {C : Type*} [Category* C] {D : Type*} [Category* D]
  [Preadditive C] [Preadditive D] [CategoryWithHomology C] [CategoryWithHomology D]
  (F : C ⥤ D) [F.Additive] [F.PreservesHomology] {ι : Type*} (c : ComplexShape ι) (i : ι)

/-- Homology of homological complexes commutes with a functor preserving homology. -/
noncomputable def mapHomologicalComplexCompHomologyFunctorIso :
    F.mapHomologicalComplex c ⋙ HomologicalComplex.homologyFunctor D c i ≅
      HomologicalComplex.homologyFunctor C c i ⋙ F :=
  -- the short complex of `F` applied to `K` in degree `i` is `F` applied to that of `K`
  isoWhiskerLeft (HomologicalComplex.shortComplexFunctor C c i) (ShortComplex.homologyFunctorIso F)

@[simp]
lemma mapHomologicalComplexCompHomologyFunctorIso_hom_app (K : HomologicalComplex C c) :
    (F.mapHomologicalComplexCompHomologyFunctorIso c i).hom.app K =
      ((K.sc i).mapHomologyIso F).hom :=
  (rfl)

end CategoryTheory.Functor
end
end TAF_LiteralSource_0283

section TAF_LiteralSource_0284
/- Original module: TauCeti.Algebra.Homology.Homotopy -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Constructions on chain homotopies

Four constructions of chain homotopies: two produce new homotopies from old ones, and the
other two assemble a null-homotopy from components given all at once.

`Homotopy.descCokernel` descends a homotopy along a degreewise cokernel.  Let `p : L ⟶ M` exhibit
`M` in each degree as the cokernel of `u : K ⟶ L`, and let `p' : L' ⟶ M'` be any morphism of
complexes.  A chain homotopy between morphisms `L ⟶ L'` whose components send the image of `u`
into the kernel of `p'` then descends to a chain homotopy between the induced morphisms `M ⟶ M'`.
Only the source side is assumed to be a degreewise cokernel; on the target side the hypothesis is
the bare vanishing `u.f i ≫ HL.hom i j ≫ p'.f j = 0`, which is what the universal property needs.
This is the mechanism behind homotopy invariance of relative homology, where `M` is the relative
chain complex of a pair, that is, the degreewise cokernel of the chains of the subspace, and the
vanishing holds because the homotopy restricts to the subspace.

`Homotopy.idPow` iterates a chain homotopy from the identity of `K` to an endomorphism `s`: it
exhibits every power `sᵐ` as homotopic to the identity, through the explicit operator
`∑_{k < m} sᵏ ≫ h`.  Its components are needed, and not just the existence of some homotopy, when
`m` is allowed to vary from one summand of `K` to another, as in the proof that small singular
chains for an open cover include as a chain homotopy equivalence.

`Homotopy.mkChainComplex` builds a null-homotopy of a chain map between `ℕ`-indexed chain
complexes from its components `h n : P.X n ⟶ Q.X (n + 1)`, given all at once together with the
homotopy identities in degree zero and in positive degrees.  It is the non-inductive counterpart of
Mathlib's `Homotopy.mkInductive`, for the situation where the components are constructed by a
recursion of their own rather than one degree at a time from the previous two.

`Homotopy.mkCochainComplexInt` is its counterpart for `ℤ`-indexed cochain complexes: a
null-homotopy of `e : P ⟶ Q` from components `h n : P.X (n + 1) ⟶ Q.X n` and the homotopy
identities `e.f (n + 1) = d ≫ h (n + 1) + h n ≫ d`, stated in every degree `n + 1` so that no
index is a difference.

`Homotopy.comm_zero_apply` and `Homotopy.comm_succ_apply` are the homotopy identities of a
homotopy between maps of `ℕ`-indexed chain complexes of modules, evaluated on elements.

`CochainComplex.nonempty_homotopy_mkHomToSingle_zero_iff` characterizes null-homotopic chain maps
from a cochain complex `K` to an object `A` placed in degree `i`: the map given by `φ : Kⁱ ⟶ A` is
null-homotopic if and only if `φ` factors through the differential `Kⁱ ⟶ Kⁱ⁺¹`. It is Mathlib's
criterion `CochainComplex.HomComplex.Cocycle.toSingleMk_mem_coboundaries_iff`, translated from
coboundaries to homotopies.

`Homotopy.cyclesMap_sub_eq` expresses the difference of the maps on cycles induced by
homotopic maps as a factorization through a term of the target complex. In particular, these
maps agree after passing to a stable category that kills that term.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v u

namespace Homotopy

/-- On cycles, the difference of homotopic maps factors through the preceding target term.
This identity does not require exactness of either complex. -/
theorem cyclesMap_sub_eq {C : Type u} [Category.{v} C] [Preadditive C]
    {ι : Type*} {c : ComplexShape ι} {K L : HomologicalComplex C c} {f g : K ⟶ L}
    (h : Homotopy f g) (i : ι) [K.HasHomology i] [L.HasHomology i] :
    HomologicalComplex.cyclesMap f i - HomologicalComplex.cyclesMap g i =
      K.iCycles i ≫ h.hom i (c.prev i) ≫ L.toCycles (c.prev i) i := by
  apply (cancel_mono (L.iCycles i)).mp
  simp only [Preadditive.sub_comp, HomologicalComplex.cyclesMap_i, Category.assoc,
    HomologicalComplex.toCycles_i]
  rw [h.comm i]
  simp [dNext, prevD, Preadditive.comp_add, ← Category.assoc]

variable {C : Type u} [Category.{v} C] [Preadditive C] {ι : Type*} {c : ComplexShape ι}
  {K L M L' M' : HomologicalComplex C c}
  {fL gL : L ⟶ L'} {fM gM : M ⟶ M'}
  (HL : Homotopy fL gL)
  (u : K ⟶ L) (p : L ⟶ M) (p' : L' ⟶ M')
  (hw : ∀ i, u.f i ≫ p.f i = 0)
  (hp : ∀ i, IsColimit (CokernelCofork.ofπ (p.f i) (hw i)))
  (hcomm : ∀ i j, u.f i ≫ HL.hom i j ≫ p'.f j = 0)

include hw hp hcomm

/-- The components of the chain homotopy that `Homotopy.descCokernel` obtains on the quotient
complex `M`. -/
@[no_expose]
def descCokernelHom (i j : ι) : M.X i ⟶ M'.X j :=
  (CokernelCofork.IsColimit.desc' (hp i) (HL.hom i j ≫ p'.f j) (hcomm i j)).1

@[reassoc (attr := simp)]
lemma π_descCokernelHom (i j : ι) :
    p.f i ≫ descCokernelHom HL u p p' hw hp hcomm i j = HL.hom i j ≫ p'.f j :=
  (CokernelCofork.IsColimit.desc' (hp i) (HL.hom i j ≫ p'.f j) (hcomm i j)).2

private lemma π_comp_dNext (i : ι) :
    p.f i ≫ dNext i (descCokernelHom HL u p p' hw hp hcomm) = dNext i HL.hom ≫ p'.f i := by
  rw [← dNext_comp_left, ← dNext_comp_right]
  exact congrArg (fun F ↦ dNext i F) (by funext a b; exact π_descCokernelHom ..)

private lemma π_comp_prevD (i : ι) :
    p.f i ≫ prevD i (descCokernelHom HL u p p' hw hp hcomm) = prevD i HL.hom ≫ p'.f i := by
  rw [← prevD_comp_left, ← prevD_comp_right]
  exact congrArg (fun F ↦ prevD i F) (by funext a b; exact π_descCokernelHom ..)

/-- A chain homotopy on the total complexes whose components kill the subcomplex after composing
with `p'` descends to a chain homotopy on the quotient complex `M`. -/
@[no_expose]
def descCokernel (hf : p ≫ fM = fL ≫ p') (hg : p ≫ gM = gL ≫ p') : Homotopy fM gM where
  hom := descCokernelHom HL u p p' hw hp hcomm
  zero i j hij := Cofork.IsColimit.hom_ext (hp i) (by simp [HL.zero i j hij])
  comm i := Cofork.IsColimit.hom_ext (hp i) (by
    simp only [Cofork.π_ofπ, Preadditive.comp_add, π_comp_dNext, π_comp_prevD,
      ← HomologicalComplex.comp_f p fM, ← HomologicalComplex.comp_f p gM, hf, hg,
      HomologicalComplex.comp_f]
    rw [← Preadditive.add_comp, ← Preadditive.add_comp, ← HL.comm i])

@[simp]
lemma descCokernel_hom (hf : p ≫ fM = fL ≫ p') (hg : p ≫ gM = gL ≫ p') :
    (descCokernel HL u p p' hw hp hcomm hf hg).hom = descCokernelHom HL u p p' hw hp hcomm := (rfl)

@[reassoc]
lemma π_descCokernel_hom (hf : p ≫ fM = fL ≫ p') (hg : p ≫ gM = gL ≫ p') (i j : ι) :
    p.f i ≫ (descCokernel HL u p p' hw hp hcomm hf hg).hom i j = HL.hom i j ≫ p'.f j :=
  π_descCokernelHom HL u p p' hw hp hcomm i j

end Homotopy

section Pow

variable {C : Type u} [Category.{v} C] {ι : Type*} {c : ComplexShape ι}

namespace Homotopy

variable [Preadditive C] {K : HomologicalComplex C c} {s : K ⟶ K}

/-- Iterating a chain homotopy from the identity.  If `h` is a chain homotopy from the identity of
`K` to a chain endomorphism `s`, then `h.idPow m` is a chain homotopy from the identity to the
`m`-th power of `s`, whose operator in bidegree `(i, j)` is `∑_{k < m} (sᵏ)ᵢ ≫ hᵢⱼ`. -/
@[no_expose]
def idPow (h : Homotopy (𝟙 K) s) (m : ℕ) : Homotopy (𝟙 K) (End.of s ^ m).asHom where
  hom i j := ∑ k ∈ Finset.range m, (End.of s ^ k).asHom.f i ≫ h.hom i j
  zero i j hij := by simp [h.zero i j hij]
  comm i := by
    have hdn : dNext i (fun a b ↦ ∑ k ∈ Finset.range m, (End.of s ^ k).asHom.f a ≫ h.hom a b) =
        ∑ k ∈ Finset.range m, (End.of s ^ k).asHom.f i ≫ dNext i h.hom := by
      simpa only [Finset.sum_fn, dNext_comp_left] using
        map_sum (dNext i) (fun k a b ↦ (End.of s ^ k).asHom.f a ≫ h.hom a b) (Finset.range m)
    have hpv : prevD i (fun a b ↦ ∑ k ∈ Finset.range m, (End.of s ^ k).asHom.f a ≫ h.hom a b) =
        ∑ k ∈ Finset.range m, (End.of s ^ k).asHom.f i ≫ prevD i h.hom := by
      simpa only [Finset.sum_fn, prevD_comp_left] using
        map_sum (prevD i) (fun k a b ↦ (End.of s ^ k).asHom.f a ≫ h.hom a b) (Finset.range m)
    have hstep : ∀ k ∈ Finset.range m, (End.of s ^ k).asHom.f i ≫ dNext i h.hom +
        (End.of s ^ k).asHom.f i ≫ prevD i h.hom =
        (End.of s ^ k).asHom.f i - (End.of s ^ (k + 1)).asHom.f i := fun k _ ↦ by
      have hsum : dNext i h.hom + prevD i h.hom = 𝟙 (K.X i) - s.f i := by
        have hc := h.comm i
        rw [HomologicalComplex.id_f] at hc
        rw [hc]
        abel
      rw [← Preadditive.comp_add, hsum, Preadditive.comp_sub, Category.comp_id,
        HomologicalComplex.pow_f_succ]
    rw [hdn, hpv, ← Finset.sum_add_distrib, Finset.sum_congr rfl hstep,
      Finset.sum_range_sub' (fun k ↦ (End.of s ^ k).asHom.f i) m, pow_zero, End.one_asHom,
      HomologicalComplex.id_f]
    abel

@[simp]
lemma idPow_hom (h : Homotopy (𝟙 K) s) (m : ℕ) (i j : ι) :
    (h.idPow m).hom i j = ∑ k ∈ Finset.range m, (End.of s ^ k).asHom.f i ≫ h.hom i j := (rfl)

end Homotopy

end Pow

section MkChainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] {P Q : ChainComplex C ℕ}

namespace Homotopy

/-- A null-homotopy of a chain map `e : P ⟶ Q` between `ℕ`-indexed chain complexes, from its
components `h n : P.X n ⟶ Q.X (n + 1)` and the homotopy identities `e.f 0 = h 0 ≫ d` and
`e.f (n + 1) = d ≫ h n + h (n + 1) ≫ d`. The components are given all at once; compare
`Homotopy.mkInductive`, which constructs them one degree at a time. -/
@[no_expose]
def mkChainComplex (e : P ⟶ Q) (h : ∀ n, P.X n ⟶ Q.X (n + 1)) (comm_zero : e.f 0 = h 0 ≫ Q.d 1 0)
    (comm_succ : ∀ n, e.f (n + 1) = P.d (n + 1) n ≫ h n + h (n + 1) ≫ Q.d (n + 2) (n + 1)) :
    Homotopy e 0 where
  hom i j := if hij : i + 1 = j then h i ≫ eqToHom (congrArg Q.X hij) else 0
  zero i j hij := dite_eq_right (by simpa [ComplexShape.down_Rel] using hij)
  comm i := by
    cases i with
    | zero =>
        rw [dNext_zero_chainComplex, prevD_chainComplex]
        simpa using comm_zero
    | succ i =>
        rw [dNext_succ_chainComplex, prevD_chainComplex]
        simpa using comm_succ i

@[simp]
lemma mkChainComplex_hom_succ (e : P ⟶ Q) (h : ∀ n, P.X n ⟶ Q.X (n + 1))
    (comm_zero : e.f 0 = h 0 ≫ Q.d 1 0)
    (comm_succ : ∀ n, e.f (n + 1) = P.d (n + 1) n ≫ h n + h (n + 1) ≫ Q.d (n + 2) (n + 1))
    (n : ℕ) : (mkChainComplex e h comm_zero comm_succ).hom n (n + 1) = h n := by
  simp [mkChainComplex]

end Homotopy

end MkChainComplex

section MkCochainComplexInt

variable {C : Type u} [Category.{v} C] [Preadditive C] {P Q : CochainComplex C ℤ}

namespace Homotopy

/-- A null-homotopy of a map `e : P ⟶ Q` between `ℤ`-indexed cochain complexes, from its
components `h n : P.X (n + 1) ⟶ Q.X n` and the homotopy identities
`e.f (n + 1) = d ≫ h (n + 1) + h n ≫ d`. Every degree is written as `n + 1`, so that no index is
ever a difference. The components are given all at once, as in `Homotopy.mkChainComplex`. -/
@[no_expose]
def mkCochainComplexInt (e : P ⟶ Q) (h : ∀ n, P.X (n + 1) ⟶ Q.X n)
    (comm : ∀ n, e.f (n + 1) = P.d (n + 1) (n + 1 + 1) ≫ h (n + 1) + h n ≫ Q.d n (n + 1)) :
    Homotopy e 0 where
  hom i j := if hij : j + 1 = i then eqToHom (congrArg P.X hij.symm) ≫ h j else 0
  zero i j hij := dite_eq_right (by simpa [ComplexShape.up_Rel] using hij)
  comm i := by
    obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
    rw [dNext_eq _ (ComplexShape.up_mk (n + 1) (n + 1 + 1) rfl),
      prevD_eq _ (ComplexShape.up_mk n (n + 1) rfl)]
    simpa using comm n

@[simp]
lemma mkCochainComplexInt_hom (e : P ⟶ Q) (h : ∀ n, P.X (n + 1) ⟶ Q.X n)
    (comm : ∀ n, e.f (n + 1) = P.d (n + 1) (n + 1 + 1) ≫ h (n + 1) + h n ≫ Q.d n (n + 1))
    (n : ℤ) : (mkCochainComplexInt e h comm).hom (n + 1) n = h n := by
  simp [mkCochainComplexInt]

end Homotopy

end MkCochainComplexInt

section ModuleCat

variable {R : Type*} [Ring R] {P Q : ChainComplex (ModuleCat R) ℕ} {e e' : P ⟶ Q}

namespace Homotopy

/-- The homotopy identity in degree zero, on elements: the difference of the two maps is the
boundary of the homotopy. -/
theorem comm_zero_apply (h : Homotopy e e') (x : P.X 0) :
    e.f 0 x = Q.d 1 0 (h.hom 0 1 x) + e'.f 0 x := by
  have hc := h.comm 0
  rw [dNext_zero_chainComplex, prevD_chainComplex, zero_add] at hc
  simpa using congrArg (fun φ : P.X 0 ⟶ Q.X 0 ↦ φ x) hc

/-- The homotopy identity in positive degrees, on elements. -/
theorem comm_succ_apply (h : Homotopy e e') (n : ℕ) (x : P.X (n + 1)) :
    e.f (n + 1) x =
      h.hom n (n + 1) (P.d (n + 1) n x) + Q.d (n + 2) (n + 1) (h.hom (n + 1) (n + 2) x) +
        e'.f (n + 1) x := by
  have hc := h.comm (n + 1)
  rw [dNext_succ_chainComplex, prevD_chainComplex] at hc
  simpa [add_assoc] using congrArg (fun φ : P.X (n + 1) ⟶ Q.X (n + 1) ↦ φ x) hc

end Homotopy

end ModuleCat

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

open HomComplex in
/-- **Null-homotopic chain maps to an object in one degree**: the chain map from `K` to `A`
placed in degree `i` given by `φ : Kⁱ ⟶ A` is null-homotopic if and only if `φ` factors through
the differential `Kⁱ ⟶ Kʲ`, where `j = i + 1`. -/
lemma nonempty_homotopy_mkHomToSingle_zero_iff (K : CochainComplex C ℤ) {i j : ℤ}
    (hij : i + 1 = j) {A : C} (φ : K.X i ⟶ A)
    (hφ : ∀ k, (ComplexShape.up ℤ).Rel k i → K.d k i ≫ φ = 0) :
    Nonempty (Homotopy (HomologicalComplex.mkHomToSingle φ hφ) 0) ↔
      ∃ g : K.X j ⟶ A, K.d i j ≫ g = φ := by
  have hφ' : K.d (i - 1) i ≫ φ = 0 := hφ _ (by simp)
  rw [← Cocycle.toSingleMk_mem_coboundaries_iff φ (add_zero i) (i - 1) (by lia) hφ' j hij,
    mem_coboundaries_iff _ (-1) (by simp)]
  -- The cocycle of `Cocycle.toSingleMk` is the zero-cochain of the chain map.
  have h : (Cocycle.toSingleMk φ (add_zero i) (i - 1) (by lia) hφ' : Cochain _ _ 0) =
      Cochain.ofHom (HomologicalComplex.mkHomToSingle φ hφ) :=
    (Cochain.toSingleEquiv (add_zero i)).injective (by
      simp [Cochain.toSingleEquiv, HomologicalComplex.mkHomToSingle_f])
  rw [h]
  exact ⟨fun ⟨ho⟩ ↦ ⟨Cochain.ofHomotopy ho, by simp [δ_ofHomotopy]⟩,
    fun ⟨z, hz⟩ ↦ ⟨(Cochain.equivHomotopy _ _).symm ⟨z, by simpa using hz.symm⟩⟩⟩

end CochainComplex
end
end
end TAF_LiteralSource_0284

section TAF_LiteralSource_0285
/- Original module: TauCeti.Algebra.Homology.Linear -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Homology commutes with scalar multiplication of chain maps

For a linear category `C`, the map induced on homology by a chain map is linear in the chain
map: `homologyMap (a • φ) i = a • homologyMap φ i`. This is the homological-complex version of
Mathlib's `ShortComplex.homologyMap_smul`, recorded as a TODO in
`Mathlib/Algebra/Homology/Linear.lean`. It identifies, for instance, the map induced by
multiplication by a scalar on a complex of modules with multiplication by that scalar on
homology, and it makes the homology functor in each degree a linear functor.
-/

public section

open CategoryTheory

namespace HomologicalComplex

variable {R : Type*} [Semiring R] {C : Type*} [Category* C] [Preadditive C]
  [CategoryTheory.Linear R C] {ι : Type*} {c : ComplexShape ι}

/-- The short complex attached to a degree sends a scalar multiple of a chain map to the scalar
multiple of the induced morphism of short complexes. -/
@[simp]
lemma shortComplexFunctor_map_smul (i : ι) (a : R) {K L : HomologicalComplex C c} (φ : K ⟶ L) :
    (shortComplexFunctor C c i).map (a • φ) = a • (shortComplexFunctor C c i).map φ := by
  -- Each component is `smul_f_apply`, stated for the `SMul` instance of the complexes.
  ext <;> exact smul_f_apply _ _ _

/-- The map induced on homology by a scalar multiple of a chain map is the scalar multiple of the
induced map. -/
@[simp]
lemma homologyMap_smul (a : R) {K L : HomologicalComplex C c} (φ : K ⟶ L) (i : ι)
    [K.HasHomology i] [L.HasHomology i] :
    homologyMap (a • φ) i = a • homologyMap φ i := by
  rw [homologyMap, shortComplexFunctor_map_smul]
  exact ShortComplex.homologyMap_smul _ _

/-- Taking homology in a fixed degree is a linear functor. -/
instance [CategoryWithHomology C] (i : ι) : (homologyFunctor C c i).Linear R where
  map_smul φ a := homologyMap_smul a φ i

end HomologicalComplex
end
end TAF_LiteralSource_0285

section TAF_LiteralSource_0286
/- Original module: TauCeti.RingTheory.KoszulComplex.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The Koszul complex of a linear functional

For a linear functional `φ : M → R` on a module over a commutative ring, the Koszul complex
`K(φ)` is the chain complex `⋯ → ⋀³ M → ⋀² M → M → R` with `K(φ)ₙ = ⋀ⁿ M` and differential the
contraction by `φ`,
`d(v₀ ∧ ⋯ ∧ vₙ) = ∑ᵢ (-1) ^ i φ(vᵢ) v₀ ∧ ⋯ ∧ v̂ᵢ ∧ ⋯ ∧ vₙ`.
For a finite sequence `x = (x₁, …, xₙ)` in `R`, the functional `v ↦ ∑ᵢ vᵢ xᵢ` on `Rⁿ` gives the
Koszul complex `K(x)` of the sequence, whose zeroth homology is `R ⧸ (x₁, …, xₙ)`.

## Main declarations

* `TauCeti.koszulComplex φ`: the Koszul complex of `φ`, as an `ℕ`-indexed chain complex of
  `R`-modules.
* `TauCeti.koszulDifferential φ n`: its differential `⋀ⁿ⁺¹ M → ⋀ⁿ M`, the contraction by `φ`, with
  the alternating-deletion formula `TauCeti.koszulDifferential_ιMulti`.
* `TauCeti.zeroEquiv_koszulDifferential_zero`: under `⋀⁰ M ≅ R` and `⋀¹ M ≅ M`, the first
  differential is `φ` itself.
* `TauCeti.exact_koszulDifferential_of_retract`: exactness of a Koszul complex passes to a
  retract along linear maps compatible with the functionals.
* `TauCeti.map_fst_koszulDifferential_coprod`: the coordinate formula for the differential
  after adjoining one scalar to a linear functional.
* `TauCeti.koszulComplex.exactAt_succ_iff`: `Hₖ₊₁(K(φ)) = 0` exactly when the Koszul
  differentials out of and into `⋀ᵏ⁺¹ M` are exact.
* `TauCeti.koszulComplex.map`: the chain map `K(φ) → K(ψ)` induced by a linear map `g` with
  `ψ ∘ g = φ`, functorial in `g`, and `TauCeti.koszulComplex.mapIso`, the isomorphism induced by a
  linear equivalence.
* `TauCeti.koszulComplex.smulHomotopy`: for `m : M`, exterior multiplication by `m` is a
  null-homotopy of multiplication by `φ(m)`, so that `φ(m)` annihilates the Koszul homology
  (`TauCeti.koszulComplex.smul_homology_eq_zero`).
* `TauCeti.koszulComplex.homologyZeroEquiv`: `H₀(K(φ)) ≃ R ⧸ φ(M)`, and its specialization
  `TauCeti.koszulComplex.homologyZeroEquivSpan` to `H₀(K(x)) ≃ R ⧸ (x₁, …, xₙ)` for a finite
  sequence.

## References

* [The Stacks Project, Tags 0622, 0623 and 0624](https://stacks.math.columbia.edu/tag/0621)

The interface (the Koszul complex of a linear functional with exterior-power terms, the
alternating-deletion differential, `koszulComplex.map` along `ψ ∘ g = φ`, and the homotopy
`d(m ∧ v) + m ∧ d(v) = φ(m) v`) follows the design of Nailin Guan in the Mathlib pull requests
[mathlib4#43708](https://github.com/leanprover-community/mathlib4/pull/43708) (definition
of the Koszul complex) and
[mathlib4#43706](https://github.com/leanprover-community/mathlib4/pull/43706) (homotopy of the
Koszul complex). No code from those pull requests is vendored here.
-/

public section

noncomputable section

universe u v

open CategoryTheory CliffordAlgebra

namespace TauCeti

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

section Differential

variable (φ : Module.Dual R M)

/-- The Koszul differential `⋀ⁿ⁺¹ M → ⋀ⁿ M` of a linear functional `φ`: the contraction by `φ`,
`v₀ ∧ ⋯ ∧ vₙ ↦ ∑ᵢ (-1) ^ i φ(vᵢ) v₀ ∧ ⋯ ∧ v̂ᵢ ∧ ⋯ ∧ vₙ` (see `koszulDifferential_ιMulti`). -/
@[expose]
def koszulDifferential (n : ℕ) : ⋀[R]^(n + 1) M →ₗ[R] ⋀[R]^n M :=
  (contractLeft (Q := (0 : QuadraticForm R M)) φ).restrict fun _ hx ↦
    ExteriorAlgebra.contractLeft_mem_exteriorPower φ hx

/-- The Koszul differential is the contraction by `φ`. -/
@[simp]
theorem coe_koszulDifferential_apply (n : ℕ) (x : ⋀[R]^(n + 1) M) :
    (koszulDifferential φ n x : ExteriorAlgebra R M) =
      contractLeft (Q := (0 : QuadraticForm R M)) φ x :=
  (rfl)

/-- The Koszul differential on a wedge product of vectors is the alternating sum of deletions:
`d(v₀ ∧ ⋯ ∧ vₙ) = ∑ᵢ (-1) ^ i φ(vᵢ) v₀ ∧ ⋯ ∧ v̂ᵢ ∧ ⋯ ∧ vₙ`. -/
theorem koszulDifferential_ιMulti (n : ℕ) (v : Fin (n + 1) → M) :
    koszulDifferential φ n (exteriorPower.ιMulti R (n + 1) v) =
      ∑ i : Fin (n + 1), ((-1 : R) ^ (i : ℕ) * φ (v i)) •
        exteriorPower.ιMulti R n (i.removeNth v) := by
  ext
  simp only [coe_koszulDifferential_apply, exteriorPower.ιMulti_apply_coe,
    ExteriorAlgebra.contractLeft_ιMulti, Submodule.coe_sum, Submodule.coe_smul]

/-- The Koszul differential squares to zero. -/
@[simp]
theorem koszulDifferential_comp_koszulDifferential (n : ℕ) :
    koszulDifferential φ n ∘ₗ koszulDifferential φ (n + 1) = 0 :=
  LinearMap.ext fun x ↦ Subtype.ext (contractLeft_contractLeft φ x.1)

/-- The Koszul differential squares to zero, elementwise. -/
@[simp]
theorem koszulDifferential_koszulDifferential (n : ℕ) (x : ⋀[R]^(n + 2) M) :
    koszulDifferential φ n (koszulDifferential φ (n + 1) x) = 0 :=
  LinearMap.congr_fun (koszulDifferential_comp_koszulDifferential φ n) x

/-- **The first Koszul differential is `φ`**: under the identifications `⋀⁰ M ≅ R` and
`⋀¹ M ≅ M`, the differential `⋀¹ M → ⋀⁰ M` is `φ`. -/
theorem zeroEquiv_comp_koszulDifferential_zero :
    (exteriorPower.zeroEquiv R M).toLinearMap ∘ₗ koszulDifferential φ 0 =
      φ ∘ₗ (exteriorPower.oneEquiv R M).toLinearMap := by
  refine exteriorPower.linearMap_ext (AlternatingMap.ext fun v ↦ ?_)
  simp [koszulDifferential_ιMulti]

/-- **The first Koszul differential is `φ`**, elementwise. -/
@[simp]
theorem zeroEquiv_koszulDifferential_zero (x : ⋀[R]^1 M) :
    exteriorPower.zeroEquiv R M (koszulDifferential φ 0 x) = φ (exteriorPower.oneEquiv R M x) :=
  LinearMap.congr_fun (zeroEquiv_comp_koszulDifferential_zero φ) x

/-- The image of the first Koszul differential, transported along `⋀⁰ M ≅ R`, is the image
of `φ`. -/
theorem map_zeroEquiv_range_koszulDifferential_zero :
    (LinearMap.range (koszulDifferential φ 0)).map (exteriorPower.zeroEquiv R M).toLinearMap =
      LinearMap.range φ := by
  rw [← LinearMap.range_comp, zeroEquiv_comp_koszulDifferential_zero,
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]

/-- The Koszul differential is natural: if `ψ ∘ g = φ`, then `⋀ g` intertwines the Koszul
differentials of `φ` and `ψ`. -/
theorem koszulDifferential_comp_map {N : Type*} [AddCommGroup N] [Module R N]
    {ψ : Module.Dual R N} {g : M →ₗ[R] N} (h : ψ ∘ₗ g = φ) (n : ℕ) :
    koszulDifferential ψ n ∘ₗ exteriorPower.map (n + 1) g =
      exteriorPower.map n g ∘ₗ koszulDifferential φ n :=
  LinearMap.ext fun x ↦ Subtype.ext <| by simp [ExteriorAlgebra.contractLeft_map, h]

/-- The Koszul differential is natural, elementwise: `⋀ g` carries the Koszul differential of
`ψ ∘ g` to that of `ψ`. -/
@[simp]
theorem koszulDifferential_map {N : Type*} [AddCommGroup N] [Module R N]
    (ψ : Module.Dual R N) (g : M →ₗ[R] N) (n : ℕ) (x : ⋀[R]^(n + 1) M) :
    koszulDifferential ψ n (exteriorPower.map (n + 1) g x) =
      exteriorPower.map n g (koszulDifferential (ψ ∘ₗ g) n x) :=
  LinearMap.congr_fun (koszulDifferential_comp_map _ rfl n) x

/-- The `⋀ M`-component of the Koszul differential of `K(φ, x)`: writing `z = a + e ∧ b`, it is
`d a + x b`. -/
theorem map_fst_koszulDifferential_coprod (x : R) (k : ℕ) (z : ⋀[R]^(k + 1) (M × R)) :
    exteriorPower.map k (LinearMap.fst R M R)
        (koszulDifferential (φ.coprod (LinearMap.toSpanSingleton R R x)) k z) =
      koszulDifferential φ k (exteriorPower.map (k + 1) (LinearMap.fst R M R) z) +
        x • exteriorPower.map k (LinearMap.fst R M R)
          (koszulDifferential (LinearMap.snd R M R) k z) :=
  Subtype.ext <| by
    simp only [exteriorPower.coe_map, coe_koszulDifferential_apply, Submodule.coe_add,
      Submodule.coe_smul, ExteriorAlgebra.map_fst_contractLeft_coprod]

variable {φ} in
/-- **Exactness passes to retracts.** If `g : M → N` has a retraction `h` and `ψ = φ ∘ h` (so
that also `φ = ψ ∘ g`), then the Koszul complex `K(φ)` is a retract of `K(ψ)`, and exactness of
`K(ψ)` at `⋀ⁿ⁺¹ N` implies exactness of `K(φ)` at `⋀ⁿ⁺¹ M`. -/
theorem exact_koszulDifferential_of_retract {N : Type*} [AddCommGroup N] [Module R N]
    {ψ : Module.Dual R N} (g : M →ₗ[R] N) (h : N →ₗ[R] M) (hhg : h ∘ₗ g = LinearMap.id)
    (hψ : φ ∘ₗ h = ψ) (n : ℕ)
    (hex : Function.Exact (koszulDifferential ψ (n + 1)) (koszulDifferential ψ n)) :
    Function.Exact (koszulDifferential φ (n + 1)) (koszulDifferential φ n) := by
  have hφ : ψ ∘ₗ g = φ := by rw [← hψ, LinearMap.comp_assoc, hhg, LinearMap.comp_id]
  refine LinearMap.exact_of_comp_of_mem_range
    (koszulDifferential_comp_koszulDifferential φ n) fun z hz ↦ ?_
  obtain ⟨y, hy⟩ := (hex (exteriorPower.map (n + 1) g z)).1 (by
    rw [koszulDifferential_map, hφ, hz, map_zero])
  refine ⟨exteriorPower.map (n + 2) h y, ?_⟩
  rw [koszulDifferential_map, hψ, hy]
  simp only [← LinearMap.comp_apply, ← exteriorPower.map_comp, hhg,
    exteriorPower.map_id, LinearMap.id_apply]

/-- The Koszul homotopy identity in degree zero: `d(m ∧ r) = φ(m) r` for `r ∈ ⋀⁰ M`. -/
theorem koszulDifferential_comp_wedgeLeft_zero (m : M) :
    koszulDifferential φ 0 ∘ₗ ExteriorAlgebra.wedgeLeft m 0 = φ m • LinearMap.id :=
  LinearMap.ext fun x ↦ Subtype.ext <| by
    simp [contractLeft_ι_mul, ExteriorAlgebra.contractLeft_eq_zero_of_mem_exteriorPower_zero φ x.2]

/-- The Koszul homotopy identity in positive degrees: `m ∧ d(v) + d(m ∧ v) = φ(m) v`. -/
theorem wedgeLeft_comp_koszulDifferential_add (m : M) (n : ℕ) :
    ExteriorAlgebra.wedgeLeft m n ∘ₗ koszulDifferential φ n +
        koszulDifferential φ (n + 1) ∘ₗ ExteriorAlgebra.wedgeLeft m (n + 1) =
      φ m • LinearMap.id :=
  LinearMap.ext fun x ↦ Subtype.ext <| by simp [contractLeft_ι_mul]

end Differential

/-- The **Koszul complex** `K(φ)` of a linear functional `φ : M → R`: the `ℕ`-indexed chain complex
with `K(φ)ₙ = ⋀ⁿ M` and differential `koszulDifferential φ`, the contraction by `φ`.

The body is exposed so that the terms of the complex are definitionally the exterior powers, and
elements of `(koszulComplex φ).X n` can be used as elements of `⋀ⁿ M`. -/
@[expose] def koszulComplex (φ : Module.Dual R M) : ChainComplex (ModuleCat.{max u v} R) ℕ :=
  ChainComplex.of (fun n ↦ ModuleCat.of R (⋀[R]^n M))
    (fun n ↦ ModuleCat.ofHom (koszulDifferential φ n))
    fun n ↦ ModuleCat.hom_ext (koszulDifferential_comp_koszulDifferential φ n)

section

variable (φ : Module.Dual R M)

/-- The terms of the Koszul complex are the exterior powers. -/
@[simp]
theorem koszulComplex_X (n : ℕ) : (koszulComplex φ).X n = ModuleCat.of R (⋀[R]^n M) :=
  (rfl)

/-- The differential of the Koszul complex is the Koszul differential. -/
theorem koszulComplex_d (n : ℕ) :
    (koszulComplex φ).d (n + 1) n = ModuleCat.ofHom (koszulDifferential φ n) := by
  simp [koszulComplex]

/-- The differential of the Koszul complex is the Koszul differential, elementwise. -/
@[simp]
theorem koszulComplex_d_apply (n : ℕ) (x : ⋀[R]^(n + 1) M) :
    ((koszulComplex φ).d (n + 1) n).hom x = koszulDifferential φ n x :=
  congr($(koszulComplex_d φ n).hom x)

end

namespace koszulComplex

variable (φ : Module.Dual R M)

/-- The Koszul complex `K(φ)` is exact at `⋀ᵏ⁺¹ M`, i.e. `Hₖ₊₁(K(φ)) = 0`, exactly when the
Koszul differentials `⋀ᵏ⁺² M → ⋀ᵏ⁺¹ M → ⋀ᵏ M` are exact. -/
theorem exactAt_succ_iff (k : ℕ) :
    (koszulComplex φ).ExactAt (k + 1) ↔
      Function.Exact (koszulDifferential φ (k + 1)) (koszulDifferential φ k) := by
  rw [HomologicalComplex.exactAt_iff' _ (k + 2) (k + 1) k (by simp) (by simp),
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  simp only [HomologicalComplex.shortComplexFunctor'_obj_f,
    HomologicalComplex.shortComplexFunctor'_obj_g, koszulComplex_d]
  -- `ModuleCat.Hom.hom (ModuleCat.ofHom f)` is `f`; `ModuleCat.hom_ofHom` does not rewrite here
  -- because the terms of `koszulComplex φ` are only definitionally the exterior powers.
  rfl

section Map

variable {N P : Type v} [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
  {φ} {ψ : Module.Dual R N} {χ : Module.Dual R P}

/-- The chain map `K(φ) → K(ψ)` induced by a linear map `g : M → N` with `ψ ∘ g = φ`: in degree
`n` it is `⋀ⁿ g`. -/
def map (g : M →ₗ[R] N) (h : ψ ∘ₗ g = φ) : koszulComplex φ ⟶ koszulComplex ψ :=
  ChainComplex.ofHom (fun n ↦ ModuleCat.ofHom (exteriorPower.map n g)) fun n ↦ by
    rw [koszulComplex_d, koszulComplex_d]
    exact ModuleCat.hom_ext (koszulDifferential_comp_map _ h n)

/-- In degree `n`, the chain map induced by `g` is `⋀ⁿ g`. -/
@[simp]
theorem map_f (g : M →ₗ[R] N) (h : ψ ∘ₗ g = φ) (n : ℕ) :
    (map g h).f n = ModuleCat.ofHom (exteriorPower.map n g) := by
  rfl

/-- The identity of `M` induces the identity of `K(φ)`. -/
@[simp]
theorem map_id : map (φ := φ) LinearMap.id (LinearMap.comp_id φ) = 𝟙 (koszulComplex φ) := by
  ext n : 1
  rw [map_f, exteriorPower.map_id, HomologicalComplex.id_f]
  exact ModuleCat.ofHom_id

/-- The chain map induced by a composite is the composite of the induced chain maps. -/
@[reassoc]
theorem map_comp (g : M →ₗ[R] N) (h : ψ ∘ₗ g = φ) (g' : N →ₗ[R] P) (h' : χ ∘ₗ g' = ψ) :
    map (g' ∘ₗ g) (by rw [← LinearMap.comp_assoc, h', h]) = map g h ≫ map g' h' := by
  ext n : 1
  rw [map_f, HomologicalComplex.comp_f, map_f, map_f, exteriorPower.map_comp]
  exact ModuleCat.ofHom_comp _ _

/-- The isomorphism `K(φ) ≅ K(ψ)` induced by a linear equivalence `e : M ≃ N` with `ψ ∘ e = φ`;
in degree `n` it is `⋀ⁿ e`. -/
def mapIso (e : M ≃ₗ[R] N) (h : ψ ∘ₗ e.toLinearMap = φ) :
    koszulComplex φ ≅ koszulComplex ψ where
  hom := map e.toLinearMap h
  inv := map e.symm.toLinearMap (by rw [← h, LinearMap.comp_assoc, e.comp_symm, LinearMap.comp_id])
  hom_inv_id := by
    rw [← map_comp, ← map_id]
    congr 1
    exact e.symm_comp
  inv_hom_id := by
    rw [← map_comp, ← map_id]
    congr 1
    exact e.comp_symm

/-- The isomorphism induced by a linear equivalence `e` is the chain map induced by `e`. -/
@[simp]
theorem mapIso_hom (e : M ≃ₗ[R] N) (h : ψ ∘ₗ e.toLinearMap = φ) :
    (mapIso e h).hom = map e.toLinearMap h :=
  (rfl)

/-- The inverse of the isomorphism induced by `e` is the chain map induced by `e.symm`. -/
@[simp]
theorem mapIso_inv (e : M ≃ₗ[R] N) (h : ψ ∘ₗ e.toLinearMap = φ) :
    (mapIso e h).inv =
      map e.symm.toLinearMap (by rw [← h, LinearMap.comp_assoc, e.comp_symm, LinearMap.comp_id]) :=
  (rfl)

end Map

section Homotopy

/-- **Koszul homotopy**: for `m : M`, exterior multiplication `v ↦ m ∧ v` is a null-homotopy of
multiplication by `φ(m)` on `K(φ)`; see `koszulDifferential_comp_wedgeLeft_zero` and
`wedgeLeft_comp_koszulDifferential_add`. -/
def smulHomotopy (m : M) : Homotopy (φ m • 𝟙 (koszulComplex φ)) 0 :=
  Homotopy.mkChainComplex _ (fun n ↦ ModuleCat.ofHom (ExteriorAlgebra.wedgeLeft m n))
    (ModuleCat.hom_ext (koszulDifferential_comp_wedgeLeft_zero φ m).symm)
    fun n ↦ by
      rw [koszulComplex_d, koszulComplex_d]
      exact ModuleCat.hom_ext (wedgeLeft_comp_koszulDifferential_add φ m n).symm

/-- The components of the Koszul homotopy are exterior multiplication by `m`. -/
@[simp]
theorem smulHomotopy_hom (m : M) (n : ℕ) :
    (smulHomotopy φ m).hom n (n + 1) = ModuleCat.ofHom (ExteriorAlgebra.wedgeLeft m n) :=
  Homotopy.mkChainComplex_hom_succ _ _ _ _ n

/-- **Every value of `φ` annihilates the Koszul homology**: `φ(m) • z = 0` for every class `z` in
every homology module of `K(φ)`. -/
theorem smul_homology_eq_zero (m : M) (n : ℕ) (z : (koszulComplex φ).homology n) :
    φ m • z = 0 := by
  have h := (smulHomotopy φ m).homologyMap_eq n
  rw [HomologicalComplex.homologyMap_smul, HomologicalComplex.homologyMap_id,
    HomologicalComplex.homologyMap_zero] at h
  simpa only [ModuleCat.hom_smul, ModuleCat.hom_id, ModuleCat.hom_zero,
    LinearMap.smul_apply, LinearMap.id_apply, LinearMap.zero_apply] using congr(($h).hom z)

end Homotopy

section HomologyZero

/-- `H₀(K(φ))` is the cokernel of the first differential `⋀¹ M → ⋀⁰ M`. -/
private def homologyZeroIso :
    (koszulComplex φ).homology 0 ≅
      ModuleCat.of R (⋀[R]^0 M ⧸ LinearMap.range (koszulDifferential φ 0)) :=
  (koszulComplex φ).isoHomologyι₀ ≪≫
    (koszulComplex φ).opcyclesIsoSc' 1 0 0 (by simp) (by simp) ≪≫
      ((koszulComplex φ).sc' 1 0 0).moduleCatOpcyclesIso

private theorem pOpcycles_comp_homologyZeroIso_hom :
    (koszulComplex φ).pOpcycles 0 ≫ (koszulComplex φ).isoHomologyι₀.inv ≫
        (homologyZeroIso φ).hom =
      ModuleCat.ofHom (LinearMap.range (koszulDifferential φ 0)).mkQ := by
  have h := ((koszulComplex φ).pOpcycles_opcyclesIsoSc'_hom_assoc 1 0 0 (by simp) (by simp)
    ((koszulComplex φ).sc' 1 0 0).moduleCatOpcyclesIso.hom).trans
      ((koszulComplex φ).sc' 1 0 0).pOpcycles_comp_moduleCatOpcyclesIso_hom
  simp only [homologyZeroIso, Iso.trans_hom, Iso.inv_hom_id_assoc]
  -- The codomain of `homologyZeroIso` is that of `moduleCatOpcyclesIso` with `sc'` unfolded.
  exact h

/-- **Zeroth Koszul homology**: `H₀(K(φ)) ≃ R ⧸ φ(M)`. It is the cokernel of the first
differential, transported along `⋀⁰ M ≅ R`; see `homologyZeroEquiv_apply`. -/
def homologyZeroEquiv : (koszulComplex φ).homology 0 ≃ₗ[R] R ⧸ LinearMap.range φ :=
  (homologyZeroIso φ).toLinearEquiv ≪≫ₗ
    Submodule.Quotient.equiv _ _ (exteriorPower.zeroEquiv R M)
      (map_zeroEquiv_range_koszulDifferential_zero φ)

/-- `homologyZeroEquiv` sends the class of `x ∈ ⋀⁰ M` to the class of the corresponding scalar. -/
@[simp]
theorem homologyZeroEquiv_apply (x : ⋀[R]^0 M) :
    homologyZeroEquiv φ
        ((koszulComplex φ).isoHomologyι₀.inv.hom (((koszulComplex φ).pOpcycles 0).hom x)) =
      Ideal.Quotient.mk _ (exteriorPower.zeroEquiv R M x) := by
  have hx : (homologyZeroIso φ).hom.hom
      ((koszulComplex φ).isoHomologyι₀.inv.hom (((koszulComplex φ).pOpcycles 0).hom x)) =
      (LinearMap.range (koszulDifferential φ 0)).mkQ x :=
    congr(($(pOpcycles_comp_homologyZeroIso_hom φ)).hom x)
  -- `simp` does not rewrite with `Iso.toLinearEquiv_apply` here, so expose `hx` by `rw` first.
  rw [homologyZeroEquiv, LinearEquiv.trans_apply, Iso.toLinearEquiv_apply, hx]
  simp

/-- **Zeroth Koszul homology of a finite sequence**: for `x = (xᵢ)` in `R`, the Koszul complex of
the functional `v ↦ ∑ᵢ vᵢ xᵢ` has `H₀ ≃ R ⧸ (xᵢ)`. -/
def homologyZeroEquivSpan {ι : Type*} [Fintype ι] (x : ι → R) :
    (koszulComplex (Fintype.linearCombination R x)).homology 0 ≃ₗ[R]
      R ⧸ Ideal.span (Set.range x) :=
  homologyZeroEquiv _ ≪≫ₗ Submodule.quotEquivOfEq _ _ (Fintype.range_linearCombination R x)

/-- `homologyZeroEquivSpan` sends the class of `y ∈ ⋀⁰ Rⁿ` to the class of the corresponding
scalar modulo `(xᵢ)`. -/
@[simp]
theorem homologyZeroEquivSpan_apply {ι : Type*} [Fintype ι] (x : ι → R)
    (y : ⋀[R]^0 (ι → R)) :
    homologyZeroEquivSpan x
        ((koszulComplex (Fintype.linearCombination R x)).isoHomologyι₀.inv.hom
          (((koszulComplex (Fintype.linearCombination R x)).pOpcycles 0).hom y)) =
      Ideal.Quotient.mk _ (exteriorPower.zeroEquiv R (ι → R) y) := by
  simpa [homologyZeroEquivSpan] using Submodule.quotEquivOfEq_mk _ _
    (Fintype.range_linearCombination R x) (exteriorPower.zeroEquiv R (ι → R) y)

end HomologyZero

end koszulComplex

end TauCeti
end
end
end TAF_LiteralSource_0286

section TAF_LiteralSource_0287
/- Original module: TauCeti.RingTheory.KoszulComplex.Regular -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Koszul complexes of weakly regular sequences

For a weakly regular sequence `x = (x₁, …, xₙ)` in a commutative ring `R`, the Koszul complex
`K(x)` is acyclic in positive degrees: `Hₖ(K(x)) = 0` for `k > 0`. Together with
`H₀(K(x)) ≃ R ⧸ (x₁, …, xₙ)` (`TauCeti.koszulComplex.homologyZeroEquivSpan`), this says that the
complex of finite free modules `K(x)ₖ = ⋀ᵏ Rⁿ` resolves `R ⧸ (x₁, …, xₙ)`.

The proof adjoins one element at a time. For a linear functional `φ : M → R` and `x : R`, the
functional `(m, r) ↦ φ(m) + r x` on `M × R` is the Koszul complex `K(φ, x)` of `φ` with `x`
adjoined. Writing `e = (0, 1)`, every element of `⋀ᵏ⁺¹ (M × R)` is uniquely `a + e ∧ b` with
`a ∈ ⋀ᵏ⁺¹ M` and `b ∈ ⋀ᵏ M`, and the Koszul differential is
`d(a + e ∧ b) = (d a + x b) - e ∧ d b`. Hence a cycle `a + e ∧ b` of `K(φ, x)` has `d b = 0` and
`x b = -d a`. If `K(φ)` is exact at `⋀ᵏ⁺¹ M` and `b` is a boundary, then `a + e ∧ b` is a
boundary. In degree `k + 2` the cycle `b` is a boundary when `Hₖ₊₁(K(φ)) = 0`; in degree one,
`x b ∈ φ(M)` forces `b ∈ φ(M)` when `x` is a nonzerodivisor on `R ⧸ φ(M) ≃ H₀(K(φ))`. For a
weakly regular sequence, induction on its length provides these hypotheses: the higher homology
of the shorter sequence vanishes, and the last element is a nonzerodivisor on its zeroth homology
`R ⧸ (x₁, …, xₙ₋₁)`.

## Main declarations

* `TauCeti.exact_koszulDifferential_coprod_succ`: if `Hₖ₊₂(K(φ))` and `Hₖ₊₁(K(φ))` both vanish,
  then adjoining any element `x` to `φ` gives `Hₖ₊₂(K(φ, x)) = 0`.
* `TauCeti.exact_koszulDifferential_coprod_zero`: if `H₁(K(φ))` vanishes and `x` is a
  nonzerodivisor on `R ⧸ φ(M)`, then `H₁(K(φ, x)) = 0`.
* `TauCeti.koszulComplex.exactAt_of_isWeaklyRegular`: **the Koszul complex of a weakly regular
  sequence is acyclic in positive degrees.**

## References

* [The Stacks Project, Tags 0626 and 062F](https://stacks.math.columbia.edu/tag/062F)
-/

public section

noncomputable section

universe u v

open CategoryTheory CliffordAlgebra

namespace TauCeti

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

section Adjoin

/-! ### Adjoining one element to a linear functional -/

variable (φ : Module.Dual R M) (x : R)

/-- Writing a cycle `z` of `K(φ, x)` of degree `k + 1` as `a + e ∧ b`, if `b` is a boundary of
`K(φ)` and `K(φ)` is exact at `⋀ᵏ⁺¹ M`, then `z` is a boundary. -/
private theorem mem_range_koszulDifferential_coprod (k : ℕ)
    (hex : Function.Exact (koszulDifferential φ (k + 1)) (koszulDifferential φ k))
    (z : ⋀[R]^(k + 1) (M × R))
    (hz : koszulDifferential (φ.coprod (LinearMap.toSpanSingleton R R x)) k z = 0)
    (hb : exteriorPower.map k (LinearMap.fst R M R)
      (koszulDifferential (LinearMap.snd R M R) k z) ∈ LinearMap.range (koszulDifferential φ k)) :
    z ∈ LinearMap.range
      (koszulDifferential (φ.coprod (LinearMap.toSpanSingleton R R x)) (k + 1)) := by
  obtain ⟨c, hc⟩ := hb
  obtain ⟨u, hu⟩ := (hex (exteriorPower.map (k + 1) (LinearMap.fst R M R) z + x • c)).1 (by
    rw [map_add, map_smul, hc, ← map_fst_koszulDifferential_coprod, hz, map_zero])
  refine ⟨exteriorPower.map (k + 2) (LinearMap.inl R M R) u -
    ExteriorAlgebra.wedgeLeft (LinearMap.inr R M R 1) (k + 1)
      (exteriorPower.map (k + 1) (LinearMap.inl R M R) c), Subtype.ext ?_⟩
  have hu' := congrArg Subtype.val hu
  have hc' := congrArg Subtype.val hc
  simp only [coe_koszulDifferential_apply, exteriorPower.coe_map, Submodule.coe_add,
    Submodule.coe_smul] at hu' hc'
  simp only [coe_koszulDifferential_apply, Submodule.coe_sub, exteriorPower.coe_map,
    ExteriorAlgebra.coe_wedgeLeft_apply, map_sub, ExteriorAlgebra.contractLeft_coprod_map_inl,
    ExteriorAlgebra.contractLeft_coprod_ι_inr_mul, hu', hc', map_add, map_smul]
  conv_rhs => rw [← ExteriorAlgebra.map_inl_map_fst_add_ι_inr_mul_contractLeft_snd
    (z : ExteriorAlgebra R (M × R))]
  abel

/-- **Adjoining an element preserves higher acyclicity.** If the Koszul complex `K(φ)` is exact
at `⋀ᵏ⁺² M` and at `⋀ᵏ⁺¹ M`, then for every `x : R` the Koszul complex `K(φ, x)` of the functional
`(m, r) ↦ φ(m) + r x` on `M × R` is exact at `⋀ᵏ⁺² (M × R)`. -/
theorem exact_koszulDifferential_coprod_succ (k : ℕ)
    (h₁ : Function.Exact (koszulDifferential φ (k + 2)) (koszulDifferential φ (k + 1)))
    (h₀ : Function.Exact (koszulDifferential φ (k + 1)) (koszulDifferential φ k)) :
    Function.Exact (koszulDifferential (φ.coprod (LinearMap.toSpanSingleton R R x)) (k + 2))
      (koszulDifferential (φ.coprod (LinearMap.toSpanSingleton R R x)) (k + 1)) := by
  refine LinearMap.exact_of_comp_of_mem_range
    (koszulDifferential_comp_koszulDifferential _ (k + 1)) fun z hz ↦
    mem_range_koszulDifferential_coprod φ x (k + 1) h₁ z hz ((h₀ _).1 ?_)
  have hz' := congrArg Subtype.val hz
  simp only [coe_koszulDifferential_apply, ZeroMemClass.coe_zero] at hz'
  refine Subtype.ext ?_
  simp only [coe_koszulDifferential_apply, exteriorPower.coe_map,
    ExteriorAlgebra.contractLeft_map_fst_contractLeft_snd φ x, hz', map_zero, neg_zero,
    ZeroMemClass.coe_zero]

/-- **Adjoining a nonzerodivisor preserves acyclicity in degree one.** If the Koszul complex
`K(φ)` is exact at `⋀¹ M` and `x` is a nonzerodivisor on `R ⧸ φ(M) ≃ H₀(K(φ))`, then the Koszul
complex `K(φ, x)` of the functional `(m, r) ↦ φ(m) + r x` on `M × R` is exact at `⋀¹ (M × R)`. -/
theorem exact_koszulDifferential_coprod_zero (hx : IsSMulRegular (R ⧸ LinearMap.range φ) x)
    (h₀ : Function.Exact (koszulDifferential φ 1) (koszulDifferential φ 0)) :
    Function.Exact (koszulDifferential (φ.coprod (LinearMap.toSpanSingleton R R x)) 1)
      (koszulDifferential (φ.coprod (LinearMap.toSpanSingleton R R x)) 0) := by
  refine LinearMap.exact_of_comp_of_mem_range
    (koszulDifferential_comp_koszulDifferential _ 0) fun z hz ↦
    mem_range_koszulDifferential_coprod φ x 0 h₀ z hz ?_
  set b := exteriorPower.map 0 (LinearMap.fst R M R)
    (koszulDifferential (LinearMap.snd R M R) 0 z)
  have hxb : x • b ∈ LinearMap.range (koszulDifferential φ 0) :=
    ⟨-exteriorPower.map 1 (LinearMap.fst R M R) z, by
      rw [map_neg, neg_eq_iff_add_eq_zero, ← map_fst_koszulDifferential_coprod, hz, map_zero]⟩
  have hrange := map_zeroEquiv_range_koszulDifferential_zero φ
  have h₁ : exteriorPower.zeroEquiv R M b ∈ LinearMap.range φ := by
    refine (isSMulRegular_on_quot_iff_lsmul_comap_le _ _).1 hx ?_
    rw [Submodule.mem_comap, LinearMap.lsmul_apply, ← map_smul, ← hrange]
    exact Submodule.mem_map_of_mem hxb
  rw [← hrange] at h₁
  obtain ⟨y, hy, hyb⟩ := h₁
  rwa [← (exteriorPower.zeroEquiv R M).injective hyb]

end Adjoin

namespace koszulComplex

/-- **The Koszul complex of a weakly regular sequence is acyclic in positive degrees**: if
`x = (x₀, …, xₙ₋₁)` is a weakly regular sequence in `R`, then `Hₖ₊₁(K(x)) = 0` for every `k`.
With `homologyZeroEquivSpan`, the complex of finite free modules `K(x)` resolves
`R ⧸ (x₀, …, xₙ₋₁)`. -/
theorem exactAt_of_isWeaklyRegular {n : ℕ} (x : Fin n → R)
    (hx : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn x)) (k : ℕ) :
    (koszulComplex (Fintype.linearCombination R x)).ExactAt (k + 1) := by
  rw [exactAt_succ_iff]
  induction n generalizing k with
  | zero =>
    intro z
    obtain rfl : z = 0 := by
      rcases subsingleton_or_nontrivial R with _ | _
      · exact (Module.subsingleton R _).elim z 0
      · exact exteriorPower.eq_zero_of_finrank_lt _
          (by rw [Module.finrank_zero_of_subsingleton]; omega) z
    exact ⟨fun _ ↦ ⟨0, map_zero _⟩, fun _ ↦ map_zero _⟩
  | succ n ih =>
    rw [List.ofFn_succ', List.concat_eq_append, RingTheory.Sequence.isWeaklyRegular_append_iff,
      RingTheory.Sequence.isWeaklyRegular_singleton_iff] at hx
    obtain ⟨hx₁, hx₂⟩ := hx
    set x' : Fin n → R := fun i ↦ x i.castSucc
    have hrange : (Ideal.ofList (List.ofFn x') • ⊤ : Submodule R R) =
        LinearMap.range (Fintype.linearCombination R x') := by
      rw [Fintype.range_linearCombination, smul_eq_mul, Ideal.mul_top, Ideal.ofList]
      congr 1
      ext r
      simp [List.mem_ofFn]
    rw [hrange] at hx₂
    have hexact : ∀ k, Function.Exact
        (koszulDifferential ((Fintype.linearCombination R x').coprod
          (LinearMap.toSpanSingleton R R (x (Fin.last n)))) (k + 1))
        (koszulDifferential ((Fintype.linearCombination R x').coprod
          (LinearMap.toSpanSingleton R R (x (Fin.last n)))) k)
    | 0 => exact_koszulDifferential_coprod_zero _ _ hx₂ (ih x' hx₁ 0)
    | k + 1 => exact_koszulDifferential_coprod_succ _ _ k (ih x' hx₁ (k + 1)) (ih x' hx₁ k)
    refine exact_koszulDifferential_of_retract
      ((LinearMap.pi fun i : Fin n ↦ LinearMap.proj i.castSucc).prod
        (LinearMap.proj (Fin.last n)))
      (LinearMap.pi fun i : Fin (n + 1) ↦ Fin.lastCases (LinearMap.snd R (Fin n → R) R)
        (fun j ↦ LinearMap.proj j ∘ₗ LinearMap.fst R (Fin n → R) R) i) ?_ ?_ k (hexact k)
    · refine LinearMap.ext fun v ↦ funext fun i ↦ ?_
      refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp
    · ext v
      · simp [Fintype.linearCombination_apply, Fin.sum_univ_castSucc, x']
      · simp [Fintype.linearCombination_apply, Fin.sum_univ_castSucc]

end koszulComplex

end TauCeti
end
end
end TAF_LiteralSource_0287

