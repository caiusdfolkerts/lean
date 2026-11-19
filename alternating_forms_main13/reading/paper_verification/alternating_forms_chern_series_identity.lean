module

public import PaperVerification.AlternatingFormsChernRecurrence
public import PaperVerification.AlternatingFormsSymmetricSeries
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# The Chern relation series and their common zeros

Here the recurrence is connected to the actual relations of Section 4.3:
`R₂ₘ = hₘ(x₁²,…,xₛ²)` and
`R₂ₘ₊₁ = ∑ᵢ xᵢ (∂ᵢ hₘ₊₁)(x₁²,…,xₛ²)`.

All formal-series identities are proved by finite-product differentiation and the
geometric-series identity.  No eventual-vanishing or isolated-zero assumption is
introduced.  The remaining cohomological and regular-sequence identifications
belong to separate parts of the paper.
-/

@[expose] public section

set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open Finset

variable {K σ : Type*} [Field K] [CharZero K] [Fintype σ] [DecidableEq σ]

@[simp] theorem eulerSeries_one : eulerSeries (1 : PowerSeries K) = 0 := by
  simp [eulerSeries]

theorem eulerSeries_mul (f g : PowerSeries K) :
    eulerSeries (f * g) = f * eulerSeries g + g * eulerSeries f := by
  simp only [eulerSeries, Derivation.leibniz, smul_eq_mul]
  ring

/-- Multiplicativity of the differential identity used in equation (7). -/
theorem chern_product_identity {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (c b a : ι → PowerSeries K)
    (hlocal : ∀ i ∈ S, c i * (eulerSeries (b i) + 2 * a i * b i ^ 2) +
      2 * eulerSeries (c i) * b i = 0) :
    (∏ i ∈ S, c i) * (eulerSeries (∏ i ∈ S, b i) +
        2 * (∏ i ∈ S, b i) * ∑ i ∈ S, a i * b i) +
      2 * eulerSeries (∏ i ∈ S, c i) * (∏ i ∈ S, b i) = 0 := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert j S hj ih =>
    have hsmall := ih (fun i hi => hlocal i (by simp [hi]))
    have hjlocal := hlocal j (by simp)
    simp only [Finset.prod_insert hj, Finset.sum_insert hj, eulerSeries_mul]
    linear_combination (c j * b j) * hsmall +
      ((∏ i ∈ S, c i) * (∏ i ∈ S, b i)) * hjlocal

/-- The geometric factor `(1-x²t²)⁻¹`. -/
noncomputable def rootGeometricSeries (x : K) : PowerSeries K :=
  PowerSeries.expand 2 (by decide) (geometricSeries (x ^ 2))

theorem rootGeometricSeries_inverse (x : K) :
    rootGeometricSeries x * (1 - (PowerSeries.C x * PowerSeries.X) ^ 2) = 1 := by
  have h := congrArg (PowerSeries.expand 2 (by decide))
    (geometricSeries_inverse (x ^ 2))
  simpa [rootGeometricSeries, PowerSeries.expand_C, mul_pow] using h

/-- The one-variable factor of the differential identity. -/
theorem rootGeometricSeries_identity (x : K) :
    (1 - PowerSeries.C x * PowerSeries.X) *
        (eulerSeries (rootGeometricSeries x) +
          2 * (PowerSeries.C x * PowerSeries.X) * rootGeometricSeries x ^ 2) +
      2 * eulerSeries (1 - PowerSeries.C x * PowerSeries.X) *
        rootGeometricSeries x = 0 := by
  have hinv := rootGeometricSeries_inverse x
  have hderivative := PowerSeries.derivative.leibniz_of_mul_eq_one hinv
  have hB : eulerSeries (rootGeometricSeries x) =
      2 * (PowerSeries.C x * PowerSeries.X) ^ 2 * rootGeometricSeries x ^ 2 := by
    rw [eulerSeries, hderivative]
    simp only [map_sub, Derivation.map_one_eq_zero, PowerSeries.derivative_pow,
      Derivation.leibniz, PowerSeries.derivative_C, PowerSeries.derivative_X,
      smul_eq_mul, mul_one, mul_zero, add_zero, zero_sub]
    norm_num
    ring
  have hC : eulerSeries (1 - PowerSeries.C x * PowerSeries.X) =
      -(PowerSeries.C x * PowerSeries.X) := by
    simp [eulerSeries, smul_eq_mul]
    ring
  rw [hB, hC]
  linear_combination (2 * (PowerSeries.C x * PowerSeries.X) *
    rootGeometricSeries x) * hinv

/-- `C(t)=∏ᵢ(1-xᵢt)` as an actual polynomial. -/
noncomputable def chernPolynomial (x : σ → K) : Polynomial K :=
  ∏ i, (1 - Polynomial.C (x i) * Polynomial.X)

theorem chernPolynomial_coe (x : σ → K) :
    (chernPolynomial x : PowerSeries K) =
      ∏ i, (1 - PowerSeries.C (x i) * PowerSeries.X) := by
  change Polynomial.coeToPowerSeries.ringHom (∏ i, (1 - Polynomial.C (x i) * Polynomial.X)) = _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  simp

@[simp] theorem chernPolynomial_coeff_zero (x : σ → K) :
    (chernPolynomial x).coeff 0 = 1 := by
  simp [chernPolynomial, Polynomial.coeff_zero_prod]

theorem chernPolynomial_natDegree_le (x : σ → K) :
    (chernPolynomial x).natDegree ≤ Fintype.card σ := by
  calc
    _ ≤ ∑ i : σ, (1 - Polynomial.C (x i) * Polynomial.X).natDegree :=
      Polynomial.natDegree_prod_le Finset.univ _
    _ ≤ ∑ _i : σ, 1 := by
      apply Finset.sum_le_sum
      intro i _
      apply (Polynomial.natDegree_sub_le _ _).trans
      apply max_le
      · simp
      · exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
    _ = _ := by simp

/-- The even series from the actual complete symmetric polynomials. -/
noncomputable def evenRootSeries (x : σ → K) : PowerSeries K :=
  PowerSeries.expand 2 (by decide) (completeEvaluationSeries fun i => x i ^ 2)

/-- The odd series in the paper, in its proved rational generating form. -/
noncomputable def oddRootSeries (x : σ → K) : PowerSeries K :=
  PowerSeries.X * evenRootSeries x * ∑ i, PowerSeries.C (x i) * rootGeometricSeries (x i)

theorem evenRootSeries_eq_prod (x : σ → K) :
    evenRootSeries x = ∏ i, rootGeometricSeries (x i) := by
  rw [evenRootSeries, completeEvaluationSeries_eq_prod, map_prod]
  rfl

theorem oddRootSeries_eq_product_sum (x : σ → K) :
    oddRootSeries x = evenRootSeries x *
      ∑ i, (PowerSeries.C (x i) * PowerSeries.X) * rootGeometricSeries (x i) := by
  unfold oddRootSeries
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The odd generating series is obtained from the actual first variation,
including the shift by one power of the formal variable. -/
theorem X_mul_oddRootSeries (x : σ → K) :
    PowerSeries.X * oddRootSeries x =
      PowerSeries.expand 2 (by decide) (firstVariationSeries (fun i => x i ^ 2) x) := by
  rw [firstVariationSeries_formula]
  simp only [map_mul, map_sum, PowerSeries.expand_X, PowerSeries.expand_C]
  change PowerSeries.X * oddRootSeries x =
    PowerSeries.X ^ 2 * evenRootSeries x *
      ∑ i, PowerSeries.C (x i) * rootGeometricSeries (x i)
  unfold oddRootSeries
  ring

/-- The differential identity is proved for the actual symmetric root series. -/
theorem root_series_differential_identity (x : σ → K) :
    (chernPolynomial x : PowerSeries K) *
        (eulerSeries (evenRootSeries x) + 2 * oddRootSeries x) +
      2 * eulerSeries (chernPolynomial x : PowerSeries K) * evenRootSeries x = 0 := by
  rw [oddRootSeries_eq_product_sum, evenRootSeries_eq_prod, chernPolynomial_coe]
  convert chern_product_identity (K := K) Finset.univ
    (fun i => 1 - PowerSeries.C (x i) * PowerSeries.X)
    (fun i => rootGeometricSeries (x i))
    (fun i => PowerSeries.C (x i) * PowerSeries.X)
    (fun i _ => rootGeometricSeries_identity (x i)) using 1 <;> ring

/-- `B(t) C(t) C(-t)=1`, proved in the formal power-series ring. -/
theorem root_series_inverse_identity (x : σ → K) :
    evenRootSeries x * (chernPolynomial x : PowerSeries K) *
      (chernPolynomial (fun i => -x i) : PowerSeries K) = 1 := by
  rw [evenRootSeries_eq_prod, chernPolynomial_coe, chernPolynomial_coe,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro i _
  have hinv := rootGeometricSeries_inverse (x i)
  simp only [map_neg]
  convert hinv using 1 <;> ring

/-- The paper's relations, defined through the actual complete homogeneous
symmetric polynomials and their actual partial derivatives. -/
noncomputable def chernRootRelation (x : σ → K) (n : ℕ) : K :=
  if Even n then
    MvPolynomial.eval (fun i => x i ^ 2) (MvPolynomial.hsymm σ K (n / 2))
  else
    ∑ i, x i * MvPolynomial.eval (fun j => x j ^ 2)
      (MvPolynomial.pderiv i (MvPolynomial.hsymm σ K ((n + 1) / 2)))

theorem evenRelationSeries_chernRootRelation (x : σ → K) :
    evenRelationSeries (chernRootRelation x) = evenRootSeries x := by
  ext n
  simp only [coeff_evenRelationSeries, evenRootSeries, PowerSeries.coeff_expand,
    completeEvaluationSeries, PowerSeries.coeff_mk, chernRootRelation,
    ← even_iff_two_dvd]
  split_ifs <;> rfl

theorem oddRelationSeries_chernRootRelation (x : σ → K) :
    oddRelationSeries (chernRootRelation x) = oddRootSeries x := by
  ext n
  have h := congrArg (PowerSeries.coeff (n + 1)) (X_mul_oddRootSeries x)
  rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_expand] at h
  rw [h]
  simp only [coeff_oddRelationSeries, firstVariationSeries, PowerSeries.coeff_mk,
    chernRootRelation, ← even_iff_two_dvd, Nat.even_add_one]
  split_ifs <;> rfl

/-- Equation (7), now with no generating-function assumptions and with exactly
the symmetric polynomials defined by the paper. -/
theorem chernRootRelation_recurrence (x : σ → K) (m : ℕ) :
    ∑ i ∈ range (m + 1), (chernPolynomial x).coeff i *
      chernRecurrenceWeight m i * chernRootRelation x (m - i) = 0 := by
  apply chern_recurrence_of_series_identity
  rw [evenRelationSeries_chernRootRelation, oddRelationSeries_chernRootRelation]
  exact root_series_differential_identity x

/-- The isolated-zero step in Section 4.3, for every size and every positive
starting degree.  The conclusions concern the actual root tuple. -/
theorem chernRootRelation_common_zero {w : ℕ} (hw : 0 < w) (x : σ → K)
    (hwindow : ∀ m, w ≤ m → m < w + Fintype.card σ → chernRootRelation x m = 0) :
    ∀ i, x i = 0 := by
  have hC : chernPolynomial x = 1 := by
    apply chern_polynomial_eq_one_of_window hw (chernPolynomial x)
      (chernPolynomial fun i => -x i) (chernPolynomial_coeff_zero x)
      (chernPolynomial_natDegree_le x) (chernRootRelation x)
    · rw [evenRelationSeries_chernRootRelation, oddRelationSeries_chernRootRelation]
      exact root_series_differential_identity x
    · rw [evenRelationSeries_chernRootRelation]
      exact root_series_inverse_identity x
    · exact hwindow
  intro i
  have hdiv : (1 - Polynomial.C (x i) * Polynomial.X) ∣ chernPolynomial x :=
    Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  rw [hC] at hdiv
  have hunit : IsUnit (1 - Polynomial.C (x i) * Polynomial.X) :=
    isUnit_iff_dvd_one.mpr hdiv
  have hdegree := Polynomial.natDegree_eq_zero_of_isUnit hunit
  have hcoeff := Polynomial.coeff_eq_zero_of_natDegree_lt
    (p := 1 - Polynomial.C (x i) * Polynomial.X) (n := 1) (by omega)
  simpa [Polynomial.coeff_sub, Polynomial.coeff_one, Polynomial.coeff_C_mul_X] using hcoeff

end PaperVerification.AlternatingForms
