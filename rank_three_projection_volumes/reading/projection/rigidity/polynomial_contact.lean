module

public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

/-!
# Cubic contact and the normalized midpoint volume deficit

All statements are about actual real polynomials and the usual real square
root. Equality of value and first two derivatives gives the exact factor
X³, then a vanishing deficit after division by t².
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Polynomial Filter
open scoped Topology

namespace RankThreeProjection.Rigidity

theorem X_cube_dvd_sub_of_two_derivatives (P Q : ℝ[X])
    (h0 : P.eval 0 = Q.eval 0)
    (h1 : P.derivative.eval 0 = Q.derivative.eval 0)
    (h2 : P.derivative.derivative.eval 0 = Q.derivative.derivative.eval 0) :
    (X : ℝ[X]) ^ 3 ∣ P - Q := by
  have hc0 : P.coeff 0 = Q.coeff 0 := by
    simpa only [← coeff_zero_eq_eval_zero] using h0
  have hc1 : P.coeff 1 = Q.coeff 1 := by
    simpa only [← coeff_zero_eq_eval_zero, coeff_derivative, Nat.cast_zero,
      zero_add, Nat.cast_one, mul_one] using h1
  have hc2 : P.coeff 2 = Q.coeff 2 := by
    have h := h2
    norm_num only [← coeff_zero_eq_eval_zero, coeff_derivative] at h
    linarith
  apply X_pow_dvd_iff.mpr
  intro i hi
  have hc : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hc with rfl | rfl | rfl <;> simp only [coeff_sub, hc0, hc1, hc2, sub_self]

theorem X_cube_dvd_midpoint_product (P A C : ℝ[X])
    (hA : (X : ℝ[X]) ^ 3 ∣ P - A)
    (hC : (X : ℝ[X]) ^ 3 ∣ P - C) :
    (X : ℝ[X]) ^ 3 ∣ P ^ 2 - A * C := by
  have he : P ^ 2 - A * C = (P - A) * P + A * (P - C) := by ring
  rw [he]
  exact dvd_add (dvd_mul_of_dvd_left hA P) (dvd_mul_of_dvd_right hC A)

theorem tendsto_eval_div_sq_of_X_cube_dvd (P : ℝ[X])
    (hP : (X : ℝ[X]) ^ 3 ∣ P) :
    Tendsto (fun t : ℝ => P.eval t / t ^ 2) (𝓝 0) (𝓝 0) := by
  obtain ⟨R, hR⟩ := hP
  have he : (fun t : ℝ => P.eval t / t ^ 2) = (fun t : ℝ => t * R.eval t) := by
    funext t
    rw [hR, eval_mul, eval_pow, eval_X]
    by_cases ht : t = 0
    · simp [ht]
    · field_simp [ht] <;> ring
  rw [he]
  have hid : Tendsto (fun t : ℝ => t) (𝓝 0) (𝓝 0) := tendsto_id
  simpa only [zero_mul] using hid.mul (R.continuous.tendsto (0 : ℝ))

/-- This limit needs only the exact cubic divisibility and a positive common
volume at zero. It is valid along the full neighborhood filter. -/
theorem midpoint_sqrt_deficit_little_o_sq (P A C : ℝ[X])
    (h0A : P.eval 0 = A.eval 0) (h0C : P.eval 0 = C.eval 0)
    (hpos : 0 < P.eval 0)
    (hdiv : (X : ℝ[X]) ^ 3 ∣ P ^ 2 - A * C) :
    Tendsto (fun t : ℝ =>
      (P.eval t - Real.sqrt (A.eval t * C.eval t)) / t ^ 2) (𝓝 0) (𝓝 0) := by
  let D := P ^ 2 - A * C
  have hD : Tendsto (fun t : ℝ => D.eval t / t ^ 2) (𝓝 0) (𝓝 0) :=
    tendsto_eval_div_sq_of_X_cube_dvd D hdiv
  let denom : ℝ → ℝ := fun t => P.eval t + Real.sqrt (A.eval t * C.eval t)
  have hden : Continuous denom :=
    P.continuous.add (Real.continuous_sqrt.comp (A.continuous.mul C.continuous))
  have hs0 : Real.sqrt (A.eval 0 * C.eval 0) = P.eval 0 := by
    rw [← h0A, ← h0C, Real.sqrt_mul_self hpos.le]
  have hd0 : 0 < denom 0 := by
    dsimp only [denom]
    rw [hs0]
    exact add_pos hpos hpos
  have hprod0 : 0 < A.eval 0 * C.eval 0 := by
    rw [← h0A, ← h0C]
    exact mul_pos hpos hpos
  have hprod : ∀ᶠ t : ℝ in 𝓝 0, 0 < A.eval t * C.eval t :=
    (isOpen_lt continuous_const (A.continuous.mul C.continuous)).mem_nhds hprod0
  have hdenpos : ∀ᶠ t : ℝ in 𝓝 0, 0 < denom t :=
    (isOpen_lt continuous_const hden).mem_nhds hd0
  have he : (fun t : ℝ => (D.eval t / t ^ 2) / denom t) =ᶠ[𝓝 0]
      (fun t : ℝ => (P.eval t - Real.sqrt (A.eval t * C.eval t)) / t ^ 2) := by
    filter_upwards [hprod, hdenpos] with t ht hd
    have hs := Real.sq_sqrt ht.le
    have hfactor : P.eval t ^ 2 - A.eval t * C.eval t =
        (P.eval t - Real.sqrt (A.eval t * C.eval t)) * denom t := by
      dsimp only [denom]
      nlinarith [hs]
    change ((P ^ 2 - A * C).eval t / t ^ 2) / denom t = _
    rw [eval_sub, eval_pow, eval_mul, hfactor]
    by_cases ht0 : t = 0
    · simp [ht0]
    · field_simp [ht0, hd.ne'] <;> ring
  have hquot : Tendsto (fun t : ℝ => (D.eval t / t ^ 2) / denom t)
      (𝓝 0) (𝓝 0) := by
    simpa only [div_eq_mul_inv, zero_mul] using
      hD.mul ((hden.tendsto 0).inv₀ hd0.ne')
  exact Filter.Tendsto.congr' he hquot

end RankThreeProjection.Rigidity

