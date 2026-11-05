module

public import Projection.QuantileDilation
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# A uniform first-order bound for Minkowski-ray quantiles

The same bound works for every unit direction and every probability in (0,1).
Thus domination survives at both probability tails when taking first
variations of expectations. All bodies and quantiles are the actual ones.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped Pointwise RealInnerProductSpace Topology

namespace RankThreeProjection.QuantileStability

theorem tendsto_dilation_power_quotient (C : ℝ) (n : ℕ) :
    Tendsto (fun t : ℝ => ((1 + C * t) ^ n - 1) / t)
      (𝓝[>] 0) (𝓝 ((n : ℝ) * C)) := by
  have hd : HasDerivAt (fun t : ℝ => (1 + C * t) ^ n) ((n : ℝ) * C) 0 := by
    simpa only [id_eq, mul_one, mul_zero, add_zero, one_pow, one_mul] using
      ((((hasDerivAt_id (0 : ℝ)).const_mul C).const_add 1).fun_pow n)
  simpa only [zero_add, mul_zero, add_zero, one_pow, smul_eq_mul,
    div_eq_mul_inv, mul_comm] using hd.tendsto_slope_zero_right

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Uniform domination of the actual first quantile difference quotients.
The comparison body is allowed to have empty interior. -/
theorem uniform_minkowski_quantile_quotient_bound
    (K A : ConvexBody E) (hdim : 2 ≤ Module.finrank ℝ E)
    (hK : (0 : E) ∈ interior (K : Set E)) (hA : (0 : E) ∈ A) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ t : ℝ in 𝓝[>] 0,
      ∀ e : E, ‖e‖ = 1 → ∀ τ ∈ Ioo (0 : ℝ) 1,
        |(heightQuantile ((K + t • A : ConvexBody E) : Set E) e τ -
          heightQuantile (K : Set E) e τ) / t| ≤ B := by
  obtain ⟨C, hC, hsandwich⟩ :=
    RankThreeProjection.Rigidity.minkowski_ray_dilation_sandwich K A hK hA
  obtain ⟨R₀, hR₀, hbound⟩ := K.isBounded.exists_pos_norm_le
  let R : ℝ := R₀ + 1
  have hR : 0 < R := by dsimp [R]; linarith
  have hradius : ∀ x ∈ (K : Set E), ‖x‖ < R := by
    intro x hx
    exact (hbound x hx).trans_lt (by dsimp [R]; linarith)
  let n := Module.finrank ℝ E
  let D : ℝ := (n : ℝ) * C + 1
  let B : ℝ := R * C + 4 * R * D
  have hD : 0 < D := by dsimp [D]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hratio : ∀ᶠ t : ℝ in 𝓝[>] 0,
      ((1 + C * t) ^ n - 1) / t ≤ D := by
    apply ((tendsto_dilation_power_quotient C n).eventually
      (Iio_mem_nhds (show (n : ℝ) * C < D by dsimp [D]; linarith))).mono
    exact fun _ h => h.le
  have hcontinuous : Continuous (fun t : ℝ => (1 + C * t) ^ n) :=
    (continuous_const.add (continuous_const.mul continuous_id)).pow n
  have hpowlim : Tendsto (fun t : ℝ => (1 + C * t) ^ n)
      (𝓝[>] 0) (𝓝 (1 : ℝ)) := by
    simpa only [mul_zero, add_zero, one_pow] using
      hcontinuous.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have hpowsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, (1 + C * t) ^ n ≤ 3 / 2 :=
    (hpowlim.eventually (Iio_mem_nhds (by norm_num : (1 : ℝ) < 3 / 2))).mono
      (fun _ h => h.le)
  have hvolume : volume (K : Set E) ≠ 0 :=
    (Measure.measure_pos_of_nonempty_interior volume ⟨0, hK⟩).ne'
  refine ⟨B, hB, ?_⟩
  filter_upwards [self_mem_nhdsWithin, hratio, hpowsmall] with t ht hquot hp
  change 0 < t at ht
  intro e he τ hτ
  obtain ⟨hleft, hright⟩ := hsandwich t ht.le
  have hlambda : 1 ≤ 1 + C * t := le_add_of_nonneg_right (mul_nonneg hC.le ht.le)
  have hq := heightQuantile_dilation_bound K (K + t • A) he hdim
    hvolume R hradius hlambda hp hleft hright hτ
  rw [abs_div, abs_of_pos ht]
  apply (div_le_iff₀ ht).mpr
  have hpower : (1 + C * t) ^ n - 1 ≤ D * t := (div_le_iff₀ ht).mp hquot
  calc
    _ ≤ R * ((1 + C * t) - 1) + 4 * R * ((1 + C * t) ^ n - 1) := hq
    _ ≤ R * ((1 + C * t) - 1) + 4 * R * (D * t) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hpower (by positivity))
    _ = B * t := by dsimp [B]; ring

end RankThreeProjection.QuantileStability
