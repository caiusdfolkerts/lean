module

public import VolumePolynomials.HigherLiftCoefficients
public import VolumePolynomials.DegreeDimension
public import Mathlib.Tactic.FinCases

@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# The exact support of the lifted slice

All seven possible monomials are retained, including the potentially zero
triple coefficient. Their support bounds, together with the literal degree
and dimension theorem, determine the dimensions in Proposition 6.2.
-/

open Set MvPolynomial Module
open scoped BigOperators Pointwise

namespace VolumePolynomials.HigherLift

def ternaryExponent (a b c : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.single 0 a + Finsupp.single 1 b + Finsupp.single 2 c

@[simp] theorem ternaryExponent_apply (a b c : ℕ) (i : Fin 3) :
    ternaryExponent a b c i = ![a, b, c] i := by
  first
  | fin_cases i <;> simp [ternaryExponent]

theorem ternaryExponent_degree (a b c : ℕ) :
    (ternaryExponent a b c).degree = a + b + c := by
  first
  | simp [Finsupp.degree_eq_sum, Fin.sum_univ_three]

theorem ternaryMonomial (a b c : ℕ) (r : ℝ) :
    (C r * X 0 ^ a * X 1 ^ b * X 2 ^ c : MvPolynomial (Fin 3) ℝ) =
      monomial (ternaryExponent a b c) r := by
  first
  | simp only [C_apply, X_pow_eq_monomial, monomial_mul_monomial,
      zero_add, mul_one, ternaryExponent]

def termExponent (k : ℕ) : Fin 7 → Fin 3 →₀ ℕ :=
  ![ternaryExponent (k + 2) 1 0, ternaryExponent (k + 2) 0 1,
    ternaryExponent (k + 1) 2 0, ternaryExponent k 2 1,
    ternaryExponent (k + 1) 0 2, ternaryExponent k 1 2,
    ternaryExponent (k + 1) 1 1]

def termCoefficient (k : ℕ) (α s z : ℝ) : Fin 7 → ℝ :=
  ![3 * (correction k * α), 3 * (correction k * α), 3, 3, 3 * s, 3, 6 * z]

theorem termExponent_degree (k : ℕ) (j : Fin 7) :
    (termExponent k j).degree = 3 + k := by
  first
  | fin_cases j <;> simp [termExponent, ternaryExponent_degree] <;> omega

def termIndex (k : ℕ) (j : Fin 7) : MultiIndex 3 (3 + k) :=
  multiIndexOfDegree (termExponent k j) (termExponent_degree k j)

@[simp] theorem exponent_termIndex (k : ℕ) (j : Fin 7) :
    exponent (termIndex k j) = termExponent k j :=
  exponent_multiIndexOfDegree _ _

@[simp] theorem termIndex_apply (k : ℕ) (j : Fin 7) (i : Fin 3) :
    ((termIndex k j).1 i : ℕ) = termExponent k j i := rfl

theorem termExponent_injective (k : ℕ) : Function.Injective (termExponent k) := by
  first
  | intro i j hij
    have h0 := congrArg (fun e : Fin 3 →₀ ℕ => e 0) hij
    have h1 := congrArg (fun e : Fin 3 →₀ ℕ => e 1) hij
    have h2 := congrArg (fun e : Fin 3 →₀ ℕ => e 2) hij
    fin_cases i <;> fin_cases j <;>
      simp [termExponent] at h0 h1 h2 ⊢ <;> omega

theorem polynomial_eq_terms (k : ℕ) (α s z : ℝ) :
    polynomial k α s z = ∑ j : Fin 7, monomial (termExponent k j) (termCoefficient k α s z j) := by
  first
  | simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ, termExponent, termCoefficient,
      Matrix.cons_val_zero, Matrix.cons_val_succ]
    simp only [← ternaryMonomial, polynomial, CubicSlice.polynomial,
      pow_zero, pow_one, pow_add, mul_one]
    ring

theorem coefficients_eq_terms (k : ℕ) (α s z : ℝ) (β : MultiIndex 3 (3 + k)) :
    coefficients k α s z β = ∑ j : Fin 7,
      if termExponent k j = exponent β then termCoefficient k α s z j else 0 := by
  first
  | classical
    simp only [coefficients, coefficientsOfPolynomial, polynomial_eq_terms,
      coeff_sum, coeff_monomial]

theorem coefficient_termIndex (k : ℕ) (α s z : ℝ) (j : Fin 7) :
    coefficients k α s z (termIndex k j) = termCoefficient k α s z j := by
  first
  | classical
    rw [coefficients_eq_terms, exponent_termIndex]
    simp only [(termExponent_injective k).eq_iff, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem nonzero_coefficient_mem_terms {k : ℕ} {α s z : ℝ}
    (β : MultiIndex 3 (3 + k)) (hβ : coefficients k α s z β ≠ 0) :
    ∃ j : Fin 7, β = termIndex k j := by
  first
  | classical
    by_contra h
    have hne (j : Fin 7) : termExponent k j ≠ exponent β := by
      first
      | intro he
        apply h
        refine ⟨j, ?_⟩
        apply exponent_injective
        rw [exponent_termIndex]
        exact he.symm
    rw [coefficients_eq_terms] at hβ
    simp only [hne, if_false, Finset.sum_const_zero, ne_self_iff_false] at hβ

theorem correction_pos (k : ℕ) : 0 < correction k := by
  first
  | unfold correction
    positivity

theorem triple_parameter_nonnegative {k : ℕ} {α s z : ℝ}
    {K : Fin 3 → Body (3 + k)} (hK : Realizes K (coefficients k α s z)) : 0 ≤ z := by
  first
  | have h := Realizes.coefficients_nonnegative hK (termIndex k 6)
    rw [coefficient_termIndex] at h
    norm_num [termCoefficient] at h
    linarith

theorem dimensions_of_realization {k : ℕ} {α s z : ℝ} (hα : 0 < α) (hs : 0 < s)
    {K : Fin 3 → Body (3 + k)} (hK : Realizes K (coefficients k α s z)) :
    affineDimension (K 0) = k + 2 ∧ affineDimension (K 1) = 2 ∧
      affineDimension (K 2) = 2 ∧ affineDimension (K 1 + K 2) = 3 ∧
      affineDimension (K 0 + K 1) = 3 + k ∧
      affineDimension (K 0 + K 2) = 3 + k := by
  first
  | have hpos0 : 0 < coefficients k α s z (termIndex k 0) := by
      first
      | rw [coefficient_termIndex]
        simpa only [termCoefficient, Matrix.cons_val_zero] using
          mul_pos (by norm_num : (0 : ℝ) < 3) (mul_pos (correction_pos k) hα)
    have hpos1 : 0 < coefficients k α s z (termIndex k 1) := by
      first
      | rw [coefficient_termIndex]
        change 0 < 3 * (correction k * α)
        exact mul_pos (by norm_num : (0 : ℝ) < 3) (mul_pos (correction_pos k) hα)
    have hpos2 : 0 < coefficients k α s z (termIndex k 2) := by
      first
      | rw [coefficient_termIndex]
        norm_num [termCoefficient]
    have hpos3 : 0 < coefficients k α s z (termIndex k 3) := by
      first
      | rw [coefficient_termIndex]
        norm_num [termCoefficient]
    have hpos4 : 0 < coefficients k α s z (termIndex k 4) := by
      first
      | rw [coefficient_termIndex]
        change 0 < 3 * s
        exact mul_pos (by norm_num : (0 : ℝ) < 3) hs
    have h0 := degree_dimension_eq_of_support_bound hK ({0} : Finset (Fin 3))
      (m := k + 2) (by
        intro β hβ
        obtain ⟨j, rfl⟩ := nonzero_coefficient_mem_terms β hβ
        fin_cases j <;> simp [partialExponent, termIndex_apply, termExponent] <;> omega)
      ⟨termIndex k 0, hpos0, by simp [partialExponent, termExponent]⟩
    have h1 := degree_dimension_eq_of_support_bound hK ({1} : Finset (Fin 3))
      (m := 2) (by
        intro β hβ
        obtain ⟨j, rfl⟩ := nonzero_coefficient_mem_terms β hβ
        fin_cases j <;> simp [partialExponent, termIndex_apply, termExponent])
      ⟨termIndex k 2, hpos2, by simp [partialExponent, termExponent]⟩
    have h2 := degree_dimension_eq_of_support_bound hK ({2} : Finset (Fin 3))
      (m := 2) (by
        intro β hβ
        obtain ⟨j, rfl⟩ := nonzero_coefficient_mem_terms β hβ
        fin_cases j <;> simp [partialExponent, termIndex_apply, termExponent])
      ⟨termIndex k 4, hpos4, by simp [partialExponent, termExponent]⟩
    have h12 := degree_dimension_eq_of_support_bound hK ({1, 2} : Finset (Fin 3))
      (m := 3) (by
        intro β hβ
        obtain ⟨j, rfl⟩ := nonzero_coefficient_mem_terms β hβ
        fin_cases j <;> simp [partialExponent, termIndex_apply, termExponent])
      ⟨termIndex k 3, hpos3, by simp [partialExponent, termExponent]⟩
    have h01 := degree_dimension_eq_of_support_bound hK ({0, 1} : Finset (Fin 3))
      (m := 3 + k) (by
        intro β hβ
        obtain ⟨j, rfl⟩ := nonzero_coefficient_mem_terms β hβ
        fin_cases j <;> simp [partialExponent, termIndex_apply, termExponent] <;> omega)
      ⟨termIndex k 0, hpos0, by simp [partialExponent, termExponent]; omega⟩
    have h02 := degree_dimension_eq_of_support_bound hK ({0, 2} : Finset (Fin 3))
      (m := 3 + k) (by
        intro β hβ
        obtain ⟨j, rfl⟩ := nonzero_coefficient_mem_terms β hβ
        fin_cases j <;> simp [partialExponent, termIndex_apply, termExponent] <;> omega)
      ⟨termIndex k 1, hpos1, by simp [partialExponent, termExponent]; omega⟩
    simp only [partialBodySum, Finset.sum_singleton, Finset.sum_pair (by decide : (0 : Fin 3) ≠ 1),
      Finset.sum_pair (by decide : (0 : Fin 3) ≠ 2),
      Finset.sum_pair (by decide : (1 : Fin 3) ≠ 2)] at h0 h1 h2 h12 h01 h02
    exact ⟨h0, h1, h2, h12, h01, h02⟩

theorem affineDimension_eq_linearHull {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : ConvexBody E) (h0 : (0 : E) ∈ K) : affineDimension K = finrank ℝ (linearHull K) := by
  first
  | rw [affineDimension, vectorSpan_eq_span_vsub_set_right ℝ h0]
    change finrank ℝ (Submodule.span ℝ ((fun x : E => x - 0) '' (K : Set E))) =
      finrank ℝ (linearHull K)
    have heq : Submodule.span ℝ ((fun x : E => x - 0) '' (K : Set E)) = linearHull K := by
      rw [show (fun x : E => x - 0) = id from funext (fun x => sub_zero x), Set.image_id]
      rfl
    exact congrArg (fun V : Submodule ℝ E => finrank ℝ V) heq

theorem centered_dimensions {k : ℕ} {α s z : ℝ} (hα : 0 < α) (hs : 0 < s)
    {K : Fin 3 → Body (3 + k)} (hK : Realizes K (coefficients k α s z))
    (h0 : ∀ i, (0 : Space (3 + k)) ∈ K i) :
    finrank ℝ (linearHull (K 0)) = k + 2 ∧
      finrank ℝ (linearHull (K 1)) = 2 ∧ finrank ℝ (linearHull (K 2)) = 2 ∧
      finrank ℝ ((linearHull (K 1) ⊔ linearHull (K 2)) : Submodule ℝ (Space (3 + k))) = 3 ∧
      linearHull (K 0) ⊔ linearHull (K 1) = ⊤ ∧
      linearHull (K 0) ⊔ linearHull (K 2) = ⊤ := by
  first
  | obtain ⟨hd0, hd1, hd2, hd12, hd01, hd02⟩ := dimensions_of_realization hα hs hK
    rw [affineDimension_eq_linearHull _ (h0 0)] at hd0
    rw [affineDimension_eq_linearHull _ (h0 1)] at hd1
    rw [affineDimension_eq_linearHull _ (h0 2)] at hd2
    rw [affineDimension_eq_linearHull _ (zero_mem_body_add (h0 1) (h0 2)),
      linearHull_add (h0 1) (h0 2)] at hd12
    have hfull (i : Fin 3) (hi : affineDimension (K 0 + K i) = 3 + k) :
        linearHull (K 0) ⊔ linearHull (K i) = ⊤ := by
      first
      | rw [affineDimension_eq_linearHull _ (zero_mem_body_add (h0 0) (h0 i)),
          linearHull_add (h0 0) (h0 i)] at hi
        apply Submodule.eq_top_of_finrank_eq
        simpa [Space] using hi
    exact ⟨hd0, hd1, hd2, hd12, hfull 1 hd01, hfull 2 hd02⟩

end VolumePolynomials.HigherLift
