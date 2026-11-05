module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous

public import PaperVerification.FermionPolynomialHilbert
public import Mathlib.RingTheory.AlgebraTower
public import Mathlib.LinearAlgebra.Basis.Submodule
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Hilbert series of an actual homogeneous polynomial-module basis

The pieces below are defined by homogeneity of every polynomial coordinate.
A homogeneous polynomial-module basis is expanded into its literal monomial
scalar multiples. Homogeneous projection proves that exactly the basis
vectors of the prescribed degree span each piece. Thus the Hilbert formula
does not assume a grading or a Hilbert function for the module.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace PaperVerification.GradedHilbert

open MvPolynomial Module
open scoped BigOperators

variable {K : Type*} [Field K] {n : ℕ} {κ : Type*}

local notation "P" => MvPolynomial (Fin n) K

def vectorHomogeneousPiece (N : Submodule P (κ → P)) (e : ℕ) : Submodule K N where
  carrier := {x | ∀ j, (x.val j).IsHomogeneous e}
  zero_mem' j := isHomogeneous_zero (Fin n) K e
  add_mem' hx hy j := (hx j).add (hy j)
  smul_mem' c x hx j := (homogeneousSubmodule (Fin n) K e).smul_mem c (hx j)

def vectorHomogeneousProjection (e : ℕ) : Module.End K (κ → P) :=
  LinearMap.pi fun j ↦ (homogeneousComponent e).comp (LinearMap.proj j)

@[simp] theorem vectorHomogeneousProjection_apply (e : ℕ) (x : κ → P) (j : κ) :
    vectorHomogeneousProjection e x j = homogeneousComponent e (x j) := rfl

theorem vectorHomogeneousProjection_of_mem (e d : ℕ) (x : κ → P)
    (hx : ∀ j, (x j).IsHomogeneous d) :
    vectorHomogeneousProjection e x = if e = d then x else 0 := by
  funext j
  rw [vectorHomogeneousProjection_apply, homogeneousComponent_of_mem (hx j)]
  split_ifs <;> rfl

section FieldBasis

variable {I : Type*} (N : Submodule P (κ → P))
variable (B : Basis I K N) (degree : I → ℕ)
variable (hB : ∀ (i : I) (j : κ), ((B i : N).val j).IsHomogeneous (degree i))

/-- Homogeneous projection of the actual basis expansion identifies the
actual homogeneous subspace with the span of exactly its degree fibre. -/
theorem span_basis_degree_eq_vectorPiece
    (N : Submodule (MvPolynomial (Fin n) K) (κ → MvPolynomial (Fin n) K))
    (B : Basis I K N) (degree : I → ℕ)
    (hB : ∀ (i : I) (j : κ), ((B i : N).val j).IsHomogeneous (degree i)) (e : ℕ) :
    Submodule.span K (Set.range (fun i : {i : I // degree i = e} ↦ B i.val)) =
      vectorHomogeneousPiece (K := K) (n := n) N e := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩ j
    simpa only [i.property] using hB i.val j
  · intro x hx
    let y : N := ∑ i ∈ (B.repr x).support,
      if degree i = e then B.repr x i • B i else 0
    have hy : y ∈ Submodule.span K
        (Set.range (fun i : {i : I // degree i = e} ↦ B i.val)) := by
      apply Submodule.sum_mem
      intro i hi
      split_ifs with he
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i,he⟩,rfl⟩)
      · exact Submodule.zero_mem _
    have hrepr : (∑ i ∈ (B.repr x).support, B.repr x i • B i : N) = x := by
      simpa only [Finsupp.linearCombination_apply, Finsupp.sum] using B.linearCombination_repr x
    have hp := congrArg (vectorHomogeneousProjection (K := K) (n := n) (κ := κ) e)
      (congrArg (fun z : N ↦ (z : κ → P)) hrepr)
    have hxproj : vectorHomogeneousProjection (K := K) (n := n) e (x : κ → P) = x := by
      rw [vectorHomogeneousProjection_of_mem e e (x : κ → P) hx, if_pos rfl]
    have hproj (i : I) : vectorHomogeneousProjection (K := K) (n := n) e (B i : κ → P) =
        if degree i = e then (B i : κ → P) else 0 := by
      rw [vectorHomogeneousProjection_of_mem e (degree i) (B i : κ → P) (hB i)]
      simp only [eq_comm]
    have hxy : y = x := by
      apply Subtype.ext
      simpa only [y, Submodule.coe_sum, Submodule.coe_smul_of_tower, map_sum,
        map_smul, hproj, hxproj, smul_ite, smul_zero, Submodule.coe_zero,
        apply_ite] using hp
    rwa [hxy] at hy

def vectorPieceBasis
    (N : Submodule (MvPolynomial (Fin n) K) (κ → MvPolynomial (Fin n) K))
    (B : Basis I K N) (degree : I → ℕ)
    (hB : ∀ (i : I) (j : κ), ((B i : N).val j).IsHomogeneous (degree i))
    (e : ℕ) : Basis {i : I // degree i = e} K (vectorHomogeneousPiece (K := K) (n := n) N e) :=
  (Basis.span (B.linearIndependent.comp Subtype.val Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ (span_basis_degree_eq_vectorPiece N B degree hB e))

theorem vectorPiece_finrank_of_basis
    (N : Submodule (MvPolynomial (Fin n) K) (κ → MvPolynomial (Fin n) K))
    (B : Basis I K N) (degree : I → ℕ)
    (hB : ∀ (i : I) (j : κ), ((B i : N).val j).IsHomogeneous (degree i)) (e : ℕ) :
    Module.finrank K (vectorHomogeneousPiece (K := K) (n := n) N e) = Nat.card {i : I // degree i = e} :=
  Module.finrank_eq_nat_card_basis (vectorPieceBasis (K := K) (n := n) N B degree hB e)

end FieldBasis

section PolynomialBasis

variable {I : Type*} [Fintype I] (N : Submodule P (κ → P))
variable (B : Basis I P N) (degree : I → ℕ)
variable (hB : ∀ (i : I) (j : κ), ((B i : N).val j).IsHomogeneous (degree i))

def polynomialScalarBasis (N : Submodule (MvPolynomial (Fin n) K) (κ → MvPolynomial (Fin n) K))
    (B : Basis I (MvPolynomial (Fin n) K) N) : Basis ((Fin n →₀ ℕ) × I) K N :=
  (basisMonomials (Fin n) K).smulTower B

def polynomialScalarDegree (a : (Fin n →₀ ℕ) × I) : ℕ := a.1.degree + degree a.2

theorem polynomialScalarBasis_homogeneous (N : Submodule (MvPolynomial (Fin n) K) (κ → MvPolynomial (Fin n) K))
    (B : Basis I (MvPolynomial (Fin n) K) N) (degree : I → ℕ)
    (hB : ∀ (i : I) (j : κ), ((B i : N).val j).IsHomogeneous (degree i))
    (a : (Fin n →₀ ℕ) × I) (j : κ) :
    ((polynomialScalarBasis (K := K) (n := n) N B a : N).val j).IsHomogeneous (polynomialScalarDegree degree a) := by
  simp only [polynomialScalarBasis, Basis.smulTower_apply, coe_basisMonomials]
  change (monomial a.1 (1 : K) * (B a.2 : N).val j).IsHomogeneous _
  exact (isHomogeneous_monomial 1 rfl).mul (hB a.2 j)

def scalarDegreeSigmaEquiv (e : ℕ) :
    {a : (Fin n →₀ ℕ) × I // polynomialScalarDegree degree a = e} ≃
      Σ i : I, {a : Fin n →₀ ℕ // a.degree + degree i = e} where
  toFun a := ⟨a.val.2,⟨a.val.1,a.property⟩⟩
  invFun a := ⟨(a.2.val,a.1),a.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def shiftedMonomialFibreEquiv (e : ℕ) (i : I) (hi : degree i ≤ e) :
    {a : Fin n →₀ ℕ // a.degree + degree i = e} ≃
      {a : Fin n →₀ ℕ // a.degree = e - degree i} where
  toFun a := ⟨a.val,by have h := a.property; omega⟩
  invFun a := ⟨a.val,by have h := a.property; omega⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem monomialDegreeFibre_finite (e : ℕ) : Finite {a : Fin n →₀ ℕ // a.degree = e} := by
  have h : Set.Finite {a : Fin n →₀ ℕ | a.degree = e} := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using
      Finsupp.finite_of_nat_weight_eq (fun _ : Fin n ↦ 1) (by simp) e
  exact h.to_subtype

theorem shiftedMonomialFibre_finite (e : ℕ) (i : I) :
    Finite {a : Fin n →₀ ℕ // a.degree + degree i = e} := by
  by_cases hi : degree i ≤ e
  · letI := monomialDegreeFibre_finite (n := n) (e - degree i)
    exact Finite.of_equiv _ (shiftedMonomialFibreEquiv (n := n) degree e i hi).symm
  · haveI : IsEmpty {a : Fin n →₀ ℕ // a.degree + degree i = e} :=
      ⟨fun a ↦ by have h := a.property; omega⟩
    infer_instance

theorem vectorPiece_finite_of_polynomial_basis (N : Submodule (MvPolynomial (Fin n) K) (κ → MvPolynomial (Fin n) K))
    (B : Basis I (MvPolynomial (Fin n) K) N) (degree : I → ℕ)
    (hB : ∀ (i : I) (j : κ), ((B i : N).val j).IsHomogeneous (degree i)) (e : ℕ) :
    Module.Finite K (vectorHomogeneousPiece (K := K) (n := n) N e) := by
  letI := fun i : I ↦ shiftedMonomialFibre_finite (n := n) degree e i
  letI : Finite {a : (Fin n →₀ ℕ) × I // polynomialScalarDegree degree a = e} :=
    Finite.of_equiv _ (scalarDegreeSigmaEquiv (n := n) degree e).symm
  exact Module.Finite.of_basis
    (vectorPieceBasis (K := K) (n := n) N (polynomialScalarBasis (K := K) (n := n) N B) (polynomialScalarDegree degree)
      (polynomialScalarBasis_homogeneous N B degree hB) e)

theorem monomialDegreeFibre_card (e : ℕ) :
    Nat.card {a : Fin n →₀ ℕ // a.degree = e} =
      Module.finrank K ((polynomialGrading (K := K) (fun _ : Fin n ↦ 1)).piece e) := by
  rw [polynomialGrading_piece, ← Pi.one_def, weightedHomogeneousSubmodule_one,
    homogeneousSubmodule_eq_finsupp_supported]
  change _ = Module.finrank K (restrictSupport K {a : Fin n →₀ ℕ | a.degree = e})
  exact (Module.finrank_eq_nat_card_basis (basisRestrictSupport K {a : Fin n →₀ ℕ | a.degree = e})).symm

/-- Each coefficient of the Hilbert series is counted from an actual basis
of the homogeneous piece, including degrees below every basis shift. -/
theorem vectorPiece_finrank_sum (N : Submodule (MvPolynomial (Fin n) K) (κ → MvPolynomial (Fin n) K))
    (B : Basis I (MvPolynomial (Fin n) K) N) (degree : I → ℕ)
    (hB : ∀ (i : I) (j : κ), ((B i : N).val j).IsHomogeneous (degree i)) (e : ℕ) :
    Module.finrank K (vectorHomogeneousPiece (K := K) (n := n) N e) =
      ∑ i : I, if degree i ≤ e then
        Module.finrank K ((polynomialGrading (K := K) (fun _ : Fin n ↦ 1)).piece (e - degree i))
      else 0 := by
  rw [vectorPiece_finrank_of_basis N (polynomialScalarBasis (K := K) (n := n) N B)
    (polynomialScalarDegree degree) (polynomialScalarBasis_homogeneous N B degree hB) e,
    Nat.card_congr (scalarDegreeSigmaEquiv (n := n) degree e)]
  letI := fun i : I ↦ shiftedMonomialFibre_finite (n := n) degree e i
  rw [Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hie : degree i ≤ e
  · rw [if_pos hie, Nat.card_congr (shiftedMonomialFibreEquiv degree e i hie),
      monomialDegreeFibre_card (K := K)]
  · rw [if_neg hie]
    haveI : IsEmpty {a : Fin n →₀ ℕ // a.degree + degree i = e} :=
      ⟨fun a ↦ by have h := a.property; omega⟩
    exact Nat.card_of_isEmpty

def vectorHilbertSeries (N : Submodule (MvPolynomial (Fin n) K) (κ → MvPolynomial (Fin n) K)) : PowerSeries ℤ :=
  PowerSeries.mk fun e ↦ (Module.finrank K (vectorHomogeneousPiece (K := K) (n := n) N e) : ℤ)

/-- The complete homogeneous free-module Hilbert formula for the literal
coordinate grading. The degree shifts may be unequal and may be zero. -/
theorem vectorHilbertSeries_eq_basis_sum (N : Submodule (MvPolynomial (Fin n) K) (κ → MvPolynomial (Fin n) K))
    (B : Basis I (MvPolynomial (Fin n) K) N) (degree : I → ℕ)
    (hB : ∀ (i : I) (j : κ), ((B i : N).val j).IsHomogeneous (degree i)) :
    vectorHilbertSeries (K := K) (n := n) N = (∑ i : I, (PowerSeries.X : PowerSeries ℤ) ^ degree i) *
      series (polynomialGrading (K := K) (fun _ : Fin n ↦ 1)) := by
  ext e
  rw [Finset.sum_mul, map_sum]
  simp only [vectorHilbertSeries, PowerSeries.coeff_mk, PowerSeries.coeff_X_pow_mul',
    coeff_series, vectorPiece_finrank_sum N B degree hB, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> simp

end PolynomialBasis

end PaperVerification.GradedHilbert
