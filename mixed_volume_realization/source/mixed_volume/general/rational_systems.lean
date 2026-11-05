module

public import mixed_volume.general.automaton_recurrence

/-! Exact finite rational resolvents.  The inverse is the adjugate divided by
its determinant; contraction is proved in the real sup norm and guarantees
that the rational denominator is nonzero. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace MixedVolume.RationalSystems

open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def castMatrix (M : Matrix ι ι ℚ) : Matrix ι ι ℝ := fun i j => (M i j : ℝ)
def castVector (b : ι → ℚ) : ι → ℝ := fun i => (b i : ℝ)

@[simp] theorem castVector_add (b c : ι → ℚ) :
    castVector (b + c) = castVector b + castVector c := by
  funext i
  exact Rat.cast_add _ _

@[simp] theorem castVector_sub (b c : ι → ℚ) :
    castVector (b - c) = castVector b - castVector c := by
  funext i
  exact Rat.cast_sub _ _

@[simp] theorem castVector_zero : castVector (0 : ι → ℚ) = 0 := by
  ext i
  exact Rat.cast_zero

@[simp] theorem cast_mulVec (M : Matrix ι ι ℚ) (b : ι → ℚ) :
    castVector (M *ᵥ b) = castMatrix M *ᵥ castVector b := by
  ext i
  simp only [castVector, castMatrix, Matrix.mulVec, dotProduct, Rat.cast_sum, Rat.cast_mul]

theorem castVector_injective : Function.Injective (castVector : (ι → ℚ) → ι → ℝ) := by
  intro x y h
  funext i
  exact Rat.cast_injective (congrFun h i)

theorem mulVec_norm_le (M : Matrix ι ι ℝ) (r : ℝ) (hr : 0 ≤ r)
    (hrow : ∀ i, (∑ j, |M i j|) ≤ r) (x : ι → ℝ) :
    ‖M *ᵥ x‖ ≤ r * ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hr (norm_nonneg _))).2
  intro i
  calc
    ‖(M *ᵥ x) i‖ ≤ ∑ j, ‖M i j * x j‖ := norm_sum_le _ _
    _ = ∑ j, |M i j| * ‖x j‖ := by simp only [norm_mul, Real.norm_eq_abs]
    _ ≤ ∑ j, |M i j| * ‖x‖ :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
        (norm_le_pi_norm x j) (abs_nonneg _)
    _ = (∑ j, |M i j|) * ‖x‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ r * ‖x‖ := mul_le_mul_of_nonneg_right (hrow i) (norm_nonneg _)

theorem fixedpoint_unique (M : Matrix ι ι ℝ) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hrow : ∀ i, (∑ j, |M i j|) ≤ r) (b x y : ι → ℝ)
    (hx : x = b + M *ᵥ x) (hy : y = b + M *ᵥ y) : x = y := by
  have heq : x - y = M *ᵥ (x - y) := by
    calc
      x - y = (b + M *ᵥ x) - (b + M *ᵥ y) := congrArg₂ (· - ·) hx hy
      _ = M *ᵥ x - M *ᵥ y := by abel
      _ = M *ᵥ (x - y) := (Matrix.mulVec_sub _ _ _).symm
  have h := mulVec_norm_le M r hr hrow (x - y)
  rw [← heq] at h
  have hz : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

theorem rational_det_ne_zero (M : Matrix ι ι ℚ) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hrow : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ r) :
    (1 - M).det ≠ 0 := by
  have hinj : Function.Injective ((1 - M).mulVec : (ι → ℚ) → ι → ℚ) := by
    apply (injective_iff_map_eq_zero (1 - M).mulVecLin).2
    intro x hx
    change (1 - M) *ᵥ x = 0 at hx
    have heq : x = M *ᵥ x := by
      simpa only [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] using hx
    have hre : castVector x = castMatrix M *ᵥ castVector x := by
      simpa only [cast_mulVec] using congrArg castVector heq
    have hzero := fixedpoint_unique (castMatrix M) r hr hr1 hrow 0 (castVector x) 0
      (by simpa only [zero_add] using hre) (by simp)
    apply castVector_injective
    simpa only [castVector_zero] using hzero
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.mulVec_injective_iff_isUnit.mp hinj))

/-- Explicit finite rational arithmetic; no choice of a real fixed point occurs
in the coefficient computation. -/
def rationalSolution (M : Matrix ι ι ℚ) (b : ι → ℚ) : ι → ℚ :=
  ((1 - M).det)⁻¹ • ((1 - M).adjugate *ᵥ b)

theorem rationalSolution_eq (M : Matrix ι ι ℚ) (b : ι → ℚ)
    (hdet : (1 - M).det ≠ 0) :
    rationalSolution M b = b + M *ᵥ rationalSolution M b := by
  have hsolve : (1 - M) *ᵥ rationalSolution M b = b := by
    rw [rationalSolution, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul,
      inv_mul_cancel₀ hdet, one_smul]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hsolve
  exact sub_eq_iff_eq_add.mp hsolve

/-- Any real solution of a rational contractive system is exactly the cast of
its finite rational adjugate solution. -/
theorem real_solution_is_rational (M : Matrix ι ι ℚ) (b : ι → ℚ)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hrow : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ r)
    (x : ι → ℝ) (hx : x = castVector b + castMatrix M *ᵥ x) :
    x = castVector (rationalSolution M b) := by
  apply fixedpoint_unique (castMatrix M) r hr hr1 hrow (castVector b) x _ hx
  have h := congrArg castVector
    (rationalSolution_eq M b (rational_det_ne_zero M r hr hr1 hrow))
  simpa only [castVector_add, cast_mulVec] using h

end MixedVolume.RationalSystems

end
