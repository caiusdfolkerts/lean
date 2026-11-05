module

public import Ellipsoid.DiagonalStability
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Order.Compact

@[expose] public section

noncomputable section

open Matrix Set Filter
open scoped BigOperators Topology

namespace EllipsoidVerification

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def matrixDerivative (A : Matrix ι ι ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  A.toLin'.toContinuousLinearMap

@[simp] theorem matrixDerivative_apply (A : Matrix ι ι ℝ) (x : ι → ℝ) :
    matrixDerivative A x = A *ᵥ x := rfl

def weightedPair (d x y : ι → ℝ) : ℝ := ∑ i, d i * x i * y i

theorem weightedPair_bound (d x y : ι → ℝ) :
    |weightedPair d x y| ≤ (∑ i, |d i|) * ‖x‖ * ‖y‖ := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  rw [abs_mul, abs_mul]
  have hx : |x i| ≤ ‖x‖ := by
    simpa only [Real.norm_eq_abs] using (norm_le_pi_norm x i)
  have hy : |y i| ≤ ‖y‖ := by
    simpa only [Real.norm_eq_abs] using (norm_le_pi_norm y i)
  exact mul_le_mul (mul_le_mul_of_nonneg_left hx (abs_nonneg _)) hy
    (abs_nonneg _) (mul_nonneg (abs_nonneg _) (norm_nonneg _))

theorem weightedPair_matrix (A : Matrix ι ι ℝ) (d x : ι → ℝ) :
    weightedPair d x (A *ᵥ x) = x ⬝ᵥ ((Matrix.diagonal d * A) *ᵥ x) := by
  simp only [weightedPair, ← Matrix.mulVec_mulVec, dotProduct, Matrix.mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem quadratic_uniform_lower {A : Matrix ι ι ℝ}
    (hA : ∀ x : ι → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (A *ᵥ x)) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : ι → ℝ, c * ‖x‖ ^ 2 ≤ x ⬝ᵥ (A *ᵥ x) := by
  have hcont : Continuous (fun x : ι → ℝ => x ⬝ᵥ (A *ᵥ x)) := by
    simp only [dotProduct, Matrix.mulVec]
    fun_prop
  obtain ⟨c, hc, hbound⟩ := (isCompact_sphere (0 : ι → ℝ) 1).exists_forall_le'
    hcont.continuousOn (fun x hx => hA x (by
      intro hx0
      simpa [hx0] using hx))
  refine ⟨c, hc, fun x => ?_⟩
  by_cases hx : x = 0
  · simp [hx]
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hunit : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : ι → ℝ) 1 := by
    simp [Metric.mem_sphere, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hn.le), hn.ne']
  have hb := hbound _ hunit
  simp only [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul] at hb
  have hh := mul_le_mul_of_nonneg_right hb (sq_nonneg ‖x‖)
  convert hh using 1
  field_simp [hn.ne'] <;> ring

/-- At a lower corner, a differentiable map with diagonally stable
derivative cannot return to the lower image orthant arbitrarily nearby. -/
theorem isolated_lower_corner {F : (ι → ℝ) → (ι → ℝ)} {a : ι → ℝ}
    {A : Matrix ι ι ℝ} (hF : HasFDerivAt F (matrixDerivative A) a)
    (hA : DiagonallyStable A) :
    ∀ᶠ x in 𝓝 a, a ≤ x → F x ≤ F a → x = a := by
  obtain ⟨d, hd, hpd⟩ := hA
  obtain ⟨c, hc, hcoerce⟩ := quadratic_uniform_lower
    (fun x hx => quadratic_pos_of_symmetricPart_posDef hpd hx)
  let B : ℝ := max (∑ i, |d i|) 1
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have heps : 0 < c / (2 * B) := div_pos hc (by positivity)
  filter_upwards [hF.isLittleO.def heps] with x hx hax hFx
  by_contra hxa
  let v := x - a
  let e := F x - F a - A *ᵥ v
  have hv : 0 ≤ v := fun i => sub_nonneg.mpr (hax i)
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxa)
  have hnegative : weightedPair d v (F x - F a) ≤ 0 :=
    Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (hd i).le (hv i)) (sub_nonpos.mpr (hFx i))
  have herror : ‖e‖ ≤ c / (2 * B) * ‖v‖ := hx
  have hsplit : weightedPair d v e = weightedPair d v (F x - F a) -
      v ⬝ᵥ ((Matrix.diagonal d * A) *ᵥ v) := by
    rw [← weightedPair_matrix]
    simp only [weightedPair, e, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  have hquad : v ⬝ᵥ ((Matrix.diagonal d * A) *ᵥ v) ≤ |weightedPair d v e| := by
    calc
      v ⬝ᵥ ((Matrix.diagonal d * A) *ᵥ v) ≤ -weightedPair d v e := by
        rw [hsplit]
        linarith
      _ ≤ |weightedPair d v e| := neg_le_abs _
  have hpair : |weightedPair d v e| ≤ B * ‖v‖ * ‖e‖ :=
    (weightedPair_bound d v e).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg v)) (norm_nonneg e))
  have htotal := (hcoerce v).trans (hquad.trans hpair)
  have hupper := mul_le_mul_of_nonneg_left herror (by positivity : 0 ≤ B * ‖v‖)
  have halgebra : B * ‖v‖ * (c / (2 * B) * ‖v‖) = c / 2 * ‖v‖ ^ 2 := by
    field_simp [hB.ne'] <;> ring
  rw [halgebra] at hupper
  have hfinal := htotal.trans hupper
  nlinarith [mul_pos hc (sq_pos_of_pos hvpos)]

end EllipsoidVerification
