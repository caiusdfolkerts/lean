module

public import Projection.Rigidity.QuantileRayEnergy
public import Projection.Rigidity.QuantileRayBound

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory ProbabilityTheory Filter Module
open scoped Pointwise RealInnerProductSpace Topology

namespace RankThreeProjection.QuantileStability
open VolumePolynomials

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The actual centered quantile limit. All geometric energy and tail bounds
are proved from the actual bodies and AF equality. The remaining scalar
parameter `c` is the derivative of the actual directional centroid; the
separate centroid-variation theorem supplies one vector for these parameters
simultaneously in every direction. -/
theorem actual_centered_quantile_L1_limit {d : ℕ}
    (K A C : ConvexBody E) (hdim : finrank ℝ E = d + 2)
    (hK : (0 : E) ∈ interior (K : Set E)) (hA : (0 : E) ∈ A) (hC : (0 : E) ∈ C)
    (z : ℝ) (hz : 0 < z)
    (hAA : mixedVolume volume (Fin.cons A (Fin.cons A (fun _ : Fin d => K))) = z)
    (hAC : mixedVolume volume (Fin.cons A (Fin.cons C (fun _ : Fin d => K))) = z)
    (hCC : mixedVolume volume (Fin.cons C (Fin.cons C (fun _ : Fin d => K))) = z)
    {e : E} (he : ‖e‖ = 1) (c : ℝ)
    (hmean : HasDerivWithinAt (fun t : ℝ =>
      (∫ x, ⟪e, x⟫ ∂volume[|((K + t • C : ConvexBody E) : Set E)]) -
        ∫ x, ⟪e, x⟫ ∂volume[|((K + t • A : ConvexBody E) : Set E)])
      c (Ici 0) 0) :
    Tendsto (fun t : ℝ => ∫ τ in Ioo (0 : ℝ) 1,
      |(heightQuantile ((K + t • C : ConvexBody E) : Set E) e τ -
          heightQuantile ((K + t • A : ConvexBody E) : Set E) e τ) / t - c|)
      (𝓝[>] 0) (𝓝 0) := by
  let U := Ioo (0 : ℝ) 1
  let μ : Measure ℝ := volume.restrict U
  letI : IsProbabilityMeasure μ := ⟨by simp [μ, U, Real.volume_Ioo]⟩
  have hd : 2 ≤ finrank ℝ E := by omega
  have hK0 : volume (K : Set E) ≠ 0 :=
    (Measure.measure_pos_of_nonempty_interior volume ⟨0, hK⟩).ne'
  have hKV : 0 < volume.real (K : Set E) :=
    ENNReal.toReal_pos hK0 K.isCompact.measure_lt_top.ne
  have hAt (t : ℝ) := minkowski_ray_volume_ne_zero K A hK0 hA t
  have hCt (t : ℝ) := minkowski_ray_volume_ne_zero K C hK0 hC t
  let f : ℝ → ℝ → ℝ := fun t τ =>
    heightQuantile ((K + t • C : ConvexBody E) : Set E) e τ -
      heightQuantile ((K + t • A : ConvexBody E) : Set E) e τ
  let v : ℝ → ℝ → ℝ := fun t τ =>
    heightQuantileSlope ((K + t • C : ConvexBody E) : Set E) e τ -
      heightQuantileSlope ((K + t • A : ConvexBody E) : Set E) e τ
  let F : ℝ → ℝ → ℝ := fun t τ => f t τ / t
  have hfderiv (t τ : ℝ) (hτ : τ ∈ U) : HasDerivAt (f t) (v t τ) τ :=
    (hasDerivAt_heightQuantile (K + t • C) he (hCt t) hτ).sub
      (hasDerivAt_heightQuantile (K + t • A) he (hAt t) hτ)
  have hvcont (t : ℝ) : ContinuousOn (v t) U :=
    (continuousOn_heightQuantileSlope (K + t • C) he (hCt t)).sub
      (continuousOn_heightQuantileSlope (K + t • A) he (hAt t))
  have hFcont (t : ℝ) : ContinuousOn (F t) U :=
    ((continuousOn_heightQuantile (K + t • C) he (hCt t)).sub
      (continuousOn_heightQuantile (K + t • A) he (hAt t))).div_const t
  have hosc_interval {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
      Tendsto (fun t : ℝ => (f t b - f t a) / t) (𝓝[>] 0) (𝓝 0) := by
    have hsub : Icc a b ⊆ U := fun τ hτ => ⟨ha.trans_le hτ.1, hτ.2.trans_lt hb⟩
    exact tendsto_scaled_oscillation_of_energy f v hab
      (Eventually.of_forall (fun t τ hτ => hfderiv t τ (hsub hτ)))
      (Eventually.of_forall (fun t => (hvcont t).mono hsub))
      (actual_quantile_ray_energy_little_o_sq K A C hdim hKV hA hC z hz
        hAA hAC hCC he ha hab hb)
  have hhalf : (1 / 2 : ℝ) ∈ U := ⟨by linarith, by linarith⟩
  have hosc_point (τ : ℝ) (hτ : τ ∈ U) :
      Tendsto (fun t : ℝ => F t τ - F t (1 / 2)) (𝓝[>] 0) (𝓝 0) := by
    rcases le_total (1 / 2 : ℝ) τ with h | h
    · have hlim := hosc_interval hhalf.1 h hτ.2
      apply Filter.Tendsto.congr' _ hlim
      exact Eventually.of_forall (fun t => by dsimp [F]; ring)
    · have hlim := (hosc_interval hτ.1 h hhalf.2).neg
      simp only [neg_zero] at hlim
      apply Filter.Tendsto.congr' _ hlim
      exact Eventually.of_forall (fun t => by dsimp [F]; ring)
  obtain ⟨B₁, hB₁, hboundA⟩ := uniform_minkowski_quantile_quotient_bound K A hd hK hA
  obtain ⟨B₂, hB₂, hboundC⟩ := uniform_minkowski_quantile_quotient_bound K C hd hK hC
  have hbound : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ τ ∈ U, ‖F t τ‖ ≤ B₁ + B₂ := by
    filter_upwards [hboundA, hboundC] with t hta htc
    intro τ hτ
    have ha := hta e he τ hτ
    have hc := htc e he τ hτ
    have heq : F t τ =
        (heightQuantile ((K + t • C : ConvexBody E) : Set E) e τ -
          heightQuantile (K : Set E) e τ) / t -
        (heightQuantile ((K + t • A : ConvexBody E) : Set E) e τ -
          heightQuantile (K : Set E) e τ) / t := by
      dsimp [F, f]
      ring
    rw [heq, Real.norm_eq_abs]
    exact (abs_sub _ _).trans (by linarith)
  have hmeanlim : Tendsto (fun t => ∫ τ, F t τ ∂μ) (𝓝[>] (0 : ℝ)) (𝓝 c) := by
    have hzero :
        ((∫ x, ⟪e, x⟫ ∂volume[|((K + (0 : ℝ) • C : ConvexBody E) : Set E)]) -
          ∫ x, ⟪e, x⟫ ∂volume[|((K + (0 : ℝ) • A : ConvexBody E) : Set E)]) = 0 := by
      simp only [body_zero_smul, add_zero, sub_self]
    have hlim := (hasDerivWithinAt_Ici_zero_iff_div hzero).mp hmean
    apply Filter.Tendsto.congr' _ hlim
    apply Eventually.of_forall
    intro t
    change _ = ∫ τ in U,
      (heightQuantile ((K + t • C : ConvexBody E) : Set E) e τ -
        heightQuantile ((K + t • A : ConvexBody E) : Set E) e τ) / t
    rw [integral_div, integral_sub
      (integrableOn_heightQuantile (K + t • C) e (hCt t))
      (integrableOn_heightQuantile (K + t • A) e (hAt t)),
      integral_heightQuantile (K + t • C) e (hCt t),
      integral_heightQuantile (K + t • A) e (hAt t)]
  have hflat := mean_determines_flat_limit μ F (1 / 2) (B₁ + B₂) c
    (Eventually.of_forall (fun t =>
      ((hFcont t).aemeasurable measurableSet_Ioo).aestronglyMeasurable))
    (hbound.mono (fun t ht => by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with τ hτ
      exact ht τ hτ))
    (hbound.mono (fun t ht => ht (1 / 2) hhalf))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with τ hτ
      exact hosc_point τ hτ)
    hmeanlim
  simpa only [μ, U, F, f, Real.norm_eq_abs] using hflat.2.2

end RankThreeProjection.QuantileStability
