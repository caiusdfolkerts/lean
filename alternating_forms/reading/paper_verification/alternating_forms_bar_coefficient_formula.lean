module

public import PaperVerification.ReducedBarBasis
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

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
