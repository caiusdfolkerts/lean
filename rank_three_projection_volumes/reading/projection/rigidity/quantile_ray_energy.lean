module

public import Projection.HeightDensity
public import Projection.QuantileLimit
public import Projection.Rigidity.VolumeDeficit

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory ProbabilityTheory Filter Module
open scoped Pointwise RealInnerProductSpace Topology

namespace RankThreeProjection.QuantileStability
open VolumePolynomials

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem le_minkowski_ray_of_zero_mem (K A : ConvexBody E) (hA : (0 : E) ∈ A) (t : ℝ) :
    K ≤ K + t • A := by
  intro x hx
  refine ⟨x, hx, 0, ⟨0, hA, by simp⟩, by simp⟩

theorem minkowski_ray_volume_ne_zero (K A : ConvexBody E)
    (hK : volume (K : Set E) ≠ 0) (hA : (0 : E) ∈ A) (t : ℝ) :
    volume ((K + t • A : ConvexBody E) : Set E) ≠ 0 :=
  ne_of_gt ((pos_iff_ne_zero.mpr hK).trans_le
    (measure_mono (le_minkowski_ray_of_zero_mem K A hA t)))

theorem exists_common_minkowski_ray_radius (K A C : ConvexBody E) :
    ∃ R : ℝ, 0 < R ∧ ∀ t ∈ Icc (0 : ℝ) 1,
      (∀ x ∈ ((K + t • A : ConvexBody E) : Set E), ‖x‖ < R) ∧
      (∀ x ∈ ((K + t • C : ConvexBody E) : Set E), ‖x‖ < R) := by
  obtain ⟨R₀, hR₀, hK⟩ := K.isCompact.isBounded.exists_pos_norm_le
  obtain ⟨R₁, hR₁, hA⟩ := A.isCompact.isBounded.exists_pos_norm_le
  obtain ⟨R₂, hR₂, hC⟩ := C.isCompact.isBounded.exists_pos_norm_le
  refine ⟨R₀ + R₁ + R₂ + 1, by linarith, ?_⟩
  intro t ht
  have bound (B : ConvexBody E) (R : ℝ) (hB : ∀ x ∈ (B : Set E), ‖x‖ ≤ R)
      (hR : R₀ + R < R₀ + R₁ + R₂ + 1) :
      ∀ x ∈ ((K + t • B : ConvexBody E) : Set E), ‖x‖ < R₀ + R₁ + R₂ + 1 := by
    rintro x ⟨k, hk, z, ⟨b, hb, rfl⟩, rfl⟩
    have hs : ‖t • b‖ ≤ ‖b‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact mul_le_of_le_one_left (norm_nonneg b) ht.2
    exact ((norm_add_le k (t • b)).trans
      (add_le_add (hK k hk) (hs.trans (hB b hb)))).trans_lt hR
  exact ⟨bound A R₁ hA (by linarith), bound C R₂ hC (by linarith)⟩

theorem continuous_minkowski_ray_volume (K A : ConvexBody E) :
    Continuous (fun t : ℝ => volume.real ((K + t • A : ConvexBody E) : Set E)) :=
  (continuous_convexBody_realMeasure volume).comp
    (continuous_const.add (continuous_id.smul continuous_const))

/-- Positive AF equality for the actual repeated background implies that the
squared quantile-slope difference is `o(t²)` on every compact probability
interval. This theorem contains all geometric inputs to that conclusion. -/
theorem actual_quantile_ray_energy_little_o_sq {d : ℕ}
    (K A C : ConvexBody E) (hdim : finrank ℝ E = d + 2)
    (hK : 0 < volume.real (K : Set E)) (hA : (0 : E) ∈ A) (hC : (0 : E) ∈ C)
    (z : ℝ) (hz : 0 < z)
    (hAA : mixedVolume volume (Fin.cons A (Fin.cons A (fun _ : Fin d => K))) = z)
    (hAC : mixedVolume volume (Fin.cons A (Fin.cons C (fun _ : Fin d => K))) = z)
    (hCC : mixedVolume volume (Fin.cons C (Fin.cons C (fun _ : Fin d => K))) = z)
    {e : E} (he : ‖e‖ = 1) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    Tendsto (fun t : ℝ =>
      (∫ τ in Icc a b,
        (heightQuantileSlope ((K + t • C : ConvexBody E) : Set E) e τ -
          heightQuantileSlope ((K + t • A : ConvexBody E) : Set E) e τ) ^ 2) / t ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  have hK0 : volume (K : Set E) ≠ 0 := by
    intro h
    have : volume.real (K : Set E) = 0 := by simp [Measure.real, h]
    exact hK.ne' this
  have hd : 2 ≤ finrank ℝ E := by omega
  obtain ⟨R, hR, hbound⟩ := exists_common_minkowski_ray_radius K A C
  let M : ℝ := 2 * R / min a (1 - b)
  have hM : 0 < M := div_pos (mul_pos zero_lt_two hR) (lt_min ha (sub_pos.mpr hb))
  let c : ℝ → ℝ := fun t => Real.sqrt
    (volume.real ((K + t • A : ConvexBody E) : Set E) *
      volume.real ((K + t • C : ConvexBody E) : Set E))
  let k : ℝ → ℝ := fun t => c t / (8 * M ^ 2)
  let D : ℝ → ℝ := fun t =>
    volume.real ((K + t • Rigidity.minkowskiMidpoint A C : ConvexBody E) : Set E) - c t
  let F : ℝ → ℝ := fun t => ∫ τ in Icc a b,
    (heightQuantileSlope ((K + t • C : ConvexBody E) : Set E) e τ -
      heightQuantileSlope ((K + t • A : ConvexBody E) : Set E) e τ) ^ 2
  have hc : Tendsto c (𝓝[>] 0) (𝓝 (volume.real (K : Set E))) := by
    have h := ((continuous_minkowski_ray_volume K A).mul
      (continuous_minkowski_ray_volume K C)).sqrt.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
    simpa only [c, Pi.mul_def, body_zero_smul, add_zero,
      Real.sqrt_mul_self hK.le] using h
  have hk := hc.div_const (8 * M ^ 2)
  have hk0 : 0 < volume.real (K : Set E) / (8 * M ^ 2) :=
    div_pos hK (mul_pos (by linarith) (sq_pos_of_pos hM))
  have hkpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < k t := hk.eventually (lt_mem_nhds hk0)
  have hD : Tendsto (fun t : ℝ => D t / t ^ 2) (𝓝[>] 0) (𝓝 0) :=
    Rigidity.actual_midpoint_deficit_little_o_sq volume K hdim hK A C z hz hAA hAC hCC
  have hupper : Tendsto (fun t : ℝ => (D t / t ^ 2) / k t) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Pi.div_def, k, zero_div] using hD.div hk hk0.ne'
  have hineq : ∀ᶠ t in 𝓝[>] (0 : ℝ), F t / t ^ 2 ≤ (D t / t ^ 2) / k t := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 from zero_lt_one), hkpos]
      with t ht hkt
    have hAt := minkowski_ray_volume_ne_zero K A hK0 hA t
    have hCt := minkowski_ray_volume_ne_zero K C hK0 hC t
    obtain ⟨hRA, hRC⟩ := hbound t ⟨ht.1.le, ht.2.le⟩
    have hE := convexBody_midpoint_quantile_energy (K + t • A) (K + t • C)
      he hAt hCt M a b hM ha hab hb
      (fun τ hτ => heightQuantileSlope_le_of_radius (K + t • A) he hd hAt R hRA ha hb hτ)
      (fun τ hτ => heightQuantileSlope_le_of_radius (K + t • C) he hd hCt R hRC ha hb hτ)
    rw [← smul_add, ← Rigidity.minkowskiRay_midpoint K A C t ht.1.le] at hE
    have hE' : F t * k t ≤ D t := by
      dsimp only [F, k, D, c]
      simpa only [sub_sq_comm, mul_comm] using hE
    have h := div_le_div_of_nonneg_right ((le_div_iff₀ hkt).mpr hE') (sq_nonneg t)
    convert h using 1 <;> ring
  exact squeeze_zero' (Eventually.of_forall (fun t =>
    div_nonneg (integral_nonneg (fun _ => sq_nonneg _)) (sq_nonneg t))) hineq hupper

end RankThreeProjection.QuantileStability
