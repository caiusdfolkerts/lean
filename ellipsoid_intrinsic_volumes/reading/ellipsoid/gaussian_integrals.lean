module

public import Ellipsoid.HomogeneousIntegration
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

@[expose] public section

noncomputable section

open MeasureTheory Set Real
open scoped BigOperators

namespace EllipsoidVerification

theorem integral_gaussian_rpow {b : ℝ} (hb : 0 < b) :
    (∫ x : ℝ, Real.exp (-b * x ^ 2)) = Real.sqrt Real.pi * b ^ (-(1 / 2 : ℝ)) := by
  rw [integral_gaussian, Real.sqrt_div Real.pi_pos.le]
  simp_rw [Real.sqrt_eq_rpow]
  rw [Real.rpow_neg hb.le]
  ring

theorem integral_sq_gaussian_rpow {b : ℝ} (hb : 0 < b) :
    (∫ x : ℝ, x ^ 2 * Real.exp (-b * x ^ 2)) =
      Real.sqrt Real.pi / 2 * b ^ (-(3 / 2 : ℝ)) := by
  let f : ℝ → ℝ := fun x => x ^ 2 * Real.exp (-b * x ^ 2)
  have hi : Integrable f := by
    simpa only [Real.rpow_two] using integrable_rpow_mul_exp_neg_mul_sq hb (by norm_num : -1 < (2 : ℝ))
  have hneg : (∫ x in Iic (0 : ℝ), f x) = ∫ x in Ioi (0 : ℝ), f x := by
    rw [show (∫ x in Iic (0 : ℝ), f x) = ∫ x in Ioi (0 : ℝ), f (-x) by
      simpa using (integral_comp_neg_Ioi 0 f).symm]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp [f]
  have hhalf : (∫ x in Ioi (0 : ℝ), f x) =
      b ^ (-(3 / 2 : ℝ)) * (1 / 2 : ℝ) * Real.Gamma (3 / 2) := by
    convert integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 2)
      (by norm_num) (by norm_num) hb using 1 <;> norm_num [f, Real.rpow_two]
  have hGamma : Real.Gamma (3 / 2 : ℝ) = Real.sqrt Real.pi / 2 := by
    convert Real.Gamma_nat_add_one_add_half 0 using 1 <;> norm_num
  rw [← integral_add_compl (s := Ioi 0) measurableSet_Ioi hi, compl_Ioi, hneg, hhalf, hGamma]
  ring

theorem gaussian_second_factor {b : ℝ} (hb : 0 < b) :
    Real.sqrt Real.pi / 2 * b ^ (-(3 / 2 : ℝ)) =
      ((2 * b)⁻¹) * (Real.sqrt Real.pi * b ^ (-(1 / 2 : ℝ))) := by
  have hp : b ^ (-(3 / 2 : ℝ)) = b⁻¹ * b ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hb]
    congr 1
    ring
  rw [hp]
  field_simp

theorem integral_diagonal_gaussian_coordinate_sq {n : ℕ} (b : Fin n → ℝ)
    (hb : ∀ j, 0 < b j) (i : Fin n) :
    (∫ x : Space n, (x i) ^ 2 * Real.exp (-(∑ j, b j * (x j) ^ 2))) =
      ((Real.sqrt Real.pi) ^ n / 2) * (b i)⁻¹ * ∏ j, (b j) ^ (-(1 / 2 : ℝ)) := by
  let f : (j : Fin n) → ℝ → ℝ := fun j x =>
    (if j = i then x ^ 2 else 1) * Real.exp (-b j * x ^ 2)
  have hpoint (x : Fin n → ℝ) :
      (x i) ^ 2 * Real.exp (-(∑ j, b j * (x j) ^ 2)) = ∏ j, f j (x j) := by
    simp only [f, Finset.prod_mul_distrib, ← Real.exp_sum, Finset.sum_neg_distrib]
    rw [Finset.prod_eq_single i]
    · simp
    · intro j hj hji
      simp [hji]
    · simp
  rw [← (PiLp.volume_preserving_toLp (Fin n)).integral_comp
    (MeasurableEquiv.toLp 2 _).measurableEmbedding]
  simp only [Function.comp_def, PiLp.toLp_apply, hpoint,
    integral_fintype_prod_volume_eq_prod]
  have hf (j : Fin n) : (∫ x, f j x) =
      (if j = i then (2 * b i)⁻¹ else 1) *
        (Real.sqrt Real.pi * (b j) ^ (-(1 / 2 : ℝ))) := by
    by_cases hji : j = i
    · subst j
      simp only [f, if_true]
      rw [integral_sq_gaussian_rpow (hb i), gaussian_second_factor (hb i)]
    · simp only [f, hji, if_false, one_mul]
      exact integral_gaussian_rpow (hb j)
  simp_rw [hf]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp only [Finset.prod_ite_eq', Finset.mem_univ, if_true, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  field_simp

theorem finite_product_rpow {ι : Type*} [Fintype ι] (b : ι → ℝ)
    (hb : ∀ i, 0 ≤ b i) (s : ℝ) :
    (∏ i, b i) ^ s = ∏ i, (b i) ^ s := by
  classical
  have h (S : Finset ι) : (∏ i ∈ S, b i) ^ s = ∏ i ∈ S, (b i) ^ s := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih =>
        rw [Finset.prod_insert hi, Finset.prod_insert hi,
          Real.mul_rpow (hb i) (Finset.prod_nonneg fun j hj => hb j), ih]
  exact h Finset.univ

end EllipsoidVerification
