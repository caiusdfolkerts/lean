module

public import Mathlib.Analysis.Convex.Body
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring.Basic

/-!
# Dilation control of actual Minkowski rays

A body containing the origin in its interior absorbs every compact comparison
body. If the comparison also contains zero, its nonnegative Minkowski ray is
sandwiched between the original body and a dilation with factor `1 + C * t`.
The estimate includes all nonnegative parameters, and permits comparison
bodies of arbitrary affine dimension.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped Pointwise

namespace RankThreeProjection.Rigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_pos_dilation_containing (K A : ConvexBody E)
    (hK : (0 : E) ∈ interior (K : Set E)) :
    ∃ C : ℝ, 0 < C ∧ A ≤ C • K := by
  obtain ⟨r, hr, hrK⟩ := Metric.mem_nhds_iff.mp
    (mem_interior_iff_mem_nhds.mp hK)
  obtain ⟨R, hR, hRA⟩ := A.isBounded.exists_pos_norm_le
  let C : ℝ := 2 * R / r
  have hC : 0 < C := div_pos (mul_pos (by norm_num) hR) hr
  refine ⟨C, hC, ?_⟩
  intro a ha
  change a ∈ C • (K : Set E)
  refine ⟨C⁻¹ • a, hrK ?_, ?_⟩
  · rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hC)]
    calc
      C⁻¹ * ‖a‖ ≤ C⁻¹ * R :=
        mul_le_mul_of_nonneg_left (hRA a ha) (inv_nonneg.mpr hC.le)
      _ = r / 2 := by
        dsimp [C]
        field_simp [ne_of_gt hR, ne_of_gt hr] <;> ring
      _ < r := half_lt_self hr
  · change C • (C⁻¹ • a) = a
    rw [smul_smul, mul_inv_cancel₀ hC.ne', one_smul]

theorem minkowski_ray_dilation_sandwich (K A : ConvexBody E)
    (hK : (0 : E) ∈ interior (K : Set E)) (hA : (0 : E) ∈ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      K ≤ K + t • A ∧ K + t • A ≤ (1 + C * t) • K := by
  obtain ⟨C, hC, hAC⟩ := exists_pos_dilation_containing K A hK
  refine ⟨C, hC, fun t ht => ⟨?_, ?_⟩⟩
  · intro x hx
    change x ∈ (K : Set E) + t • (A : Set E)
    exact ⟨x, hx, 0, ⟨0, hA, smul_zero _⟩, add_zero x⟩
  · have hsub : K + t • A ≤ K + t • (C • K) := by
      rintro x ⟨k, hk, y, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨k, hk, t • a, ⟨a, hAC ha, rfl⟩, rfl⟩
    have heq : K + t • (C • K) = (1 + C * t) • K := by
      rw [smul_smul]
      apply SetLike.coe_injective
      change (K : Set E) + (t * C) • (K : Set E) =
        (1 + C * t) • (K : Set E)
      calc
        (K : Set E) + (t * C) • (K : Set E) =
            (1 : ℝ) • (K : Set E) + (t * C) • (K : Set E) := by rw [one_smul]
        _ = (1 + t * C) • (K : Set E) :=
          (K.convex.add_smul zero_le_one (mul_nonneg ht hC.le)).symm
        _ = _ := by rw [mul_comm t C]
    exact heq ▸ hsub

end RankThreeProjection.Rigidity
