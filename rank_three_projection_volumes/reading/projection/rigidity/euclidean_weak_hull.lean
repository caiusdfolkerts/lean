module

public import Projection.Rigidity.QuantileCenteredLimit
public import Projection.Rigidity.CentroidVariation
public import Projection.Rigidity.LipschitzVariation
public import Projection.Rigidity.ProjectedVariation

/-!
# The Euclidean weak hull conclusion

Actual mixed-volume equality gives the centered L¹ limit for every height
quantile. The derivatives of all directional means come from one centroid
vector. Translating one comparison body by the negative of that vector makes
every normalized Lipschitz ridge variation vanish. Fourier uniqueness and
the localized radial formula then give the actual mixed-volume identity for
the convex hull. No rigidity statement is assumed in this assembly.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory ProbabilityTheory Filter Module
open scoped Pointwise RealInnerProductSpace Topology

namespace RankThreeProjection.QuantileStability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Inverse-transform sampling applies to every continuous height test,
including sine and cosine at an arbitrary frequency. -/
theorem integral_heightQuantile_test (K : ConvexBody E) (e : E)
    (hK : volume (K : Set E) ≠ 0) (ψ : ℝ → ℝ) (hψ : Continuous ψ) :
    (∫ τ in Ioo (0 : ℝ) 1, ψ (heightQuantile (K : Set E) e τ)) =
      ∫ x, ψ ⟪e, x⟫ ∂volume[|(K : Set E)] := by
  letI : IsProbabilityMeasure (volume[|(K : Set E)]) :=
    cond_isProbabilityMeasure_of_finite hK K.isCompact.measure_lt_top.ne
  let ν : Measure ℝ := (volume[|(K : Set E)]).map (fun x => ⟪e, x⟫)
  letI : IsProbabilityMeasure ν := inferInstance
  change (∫ τ in Ioo (0 : ℝ) 1, ψ (ν.quantile τ)) = _
  rw [← integral_map (Measure.measurable_quantile ν).aemeasurable
    hψ.aestronglyMeasurable, Measure.map_quantile_volume_Ioo]
  exact integral_map (continuous_const.inner continuous_id).measurable.aemeasurable
    hψ.aestronglyMeasurable

end RankThreeProjection.QuantileStability

namespace OAI.PettyProjection

open VolumePolynomials RankThreeProjection.Rigidity RankThreeProjection.QuantileStability

/-- The weak hull identity for arbitrary origin-containing comparison bodies
and an origin-interior Euclidean reference body. The comparison bodies may
have any dimension. Every hypothesis is an actual mixed-volume equality. -/
theorem euclidean_origin_weak_hull {d : ℕ}
    (K A C : ConvexBody (Space (d + 2)))
    (hK : (0 : Space (d + 2)) ∈ interior (K : Set (Space (d + 2))))
    (hA : (0 : Space (d + 2)) ∈ A) (hC : (0 : Space (d + 2)) ∈ C)
    (a : ℝ) (ha : 0 < a)
    (hAA : mixedVolume volume (Fin.cons A (Fin.cons A (fun _ : Fin d => K))) = a)
    (hAC : mixedVolume volume (Fin.cons A (Fin.cons C (fun _ : Fin d => K))) = a)
    (hCC : mixedVolume volume (Fin.cons C (Fin.cons C (fun _ : Fin d => K))) = a) :
    ∃ w : Space (d + 2),
      mixedVolume volume (Fin.cons (RankThreeProjection.joinBody A (translateBody w C))
        (Fin.cons K (fun _ : Fin d => K))) =
      mixedVolume volume (Fin.cons A (Fin.cons K (fun _ : Fin d => K))) := by
  letI : NeZero (d + 2) := ⟨by omega⟩
  have h0 : (K : Set (Space (d + 2))) ∈ 𝓝 (0 : Space (d + 2)) :=
    mem_interior_iff_mem_nhds.mp hK
  have hK0 : volume (K : Set (Space (d + 2))) ≠ 0 :=
    (Measure.measure_pos_of_mem_nhds volume h0).ne'
  have hdim : finrank ℝ (Space (d + 2)) = d + 2 := finrank_euclideanSpace_fin
  obtain ⟨v, hv⟩ := exists_centroid_difference_derivative K A C h0
  let B : ConvexBody (Space (d + 2)) := translateBody (-v) C
  let μ : ℝ → Measure (Space (d + 2)) := fun t =>
    volume[|((K + t • A : ConvexBody (Space (d + 2))) : Set (Space (d + 2)))]
  let ν : ℝ → Measure (Space (d + 2)) := fun t =>
    volume[|((K + t • B : ConvexBody (Space (d + 2))) : Set (Space (d + 2)))]
  have hAt (t : ℝ) := volume_minkowskiRay_ne_zero K A hK0 t
  have hBt (t : ℝ) := volume_minkowskiRay_ne_zero K B hK0 t
  have hμ (t : ℝ) : IsProbabilityMeasure (μ t) :=
    cond_isProbabilityMeasure_of_finite (hAt t) (K + t • A).isCompact.measure_lt_top.ne
  have hν (t : ℝ) : IsProbabilityMeasure (ν t) :=
    cond_isProbabilityMeasure_of_finite (hBt t) (K + t • B).isCompact.measure_lt_top.ne
  have hunit (e : Space (d + 2)) (he : ‖e‖ = 1)
      (ψ : ℝ → ℝ) (L : NNReal) (hψ : LipschitzWith L ψ) :
      HasDerivWithinAt
        (fun t : ℝ => (∫ x, ψ ⟪e, x⟫ ∂μ t) - ∫ x, ψ ⟪e, x⟫ ∂ν t)
        0 (Ici 0) 0 := by
    let η : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)
    let f : ℝ → ℝ → ℝ := fun t τ =>
      heightQuantile ((K + t • A : ConvexBody (Space (d + 2))) : Set (Space (d + 2))) e τ
    let g : ℝ → ℝ → ℝ := fun t τ =>
      heightQuantile ((K + t • B : ConvexBody (Space (d + 2))) : Set (Space (d + 2))) e τ
    have hf (t : ℝ) : Integrable (f t) η :=
      integrableOn_heightQuantile (K + t • A) e (hAt t)
    have hg (t : ℝ) : Integrable (g t) η :=
      integrableOn_heightQuantile (K + t • B) e (hBt t)
    have hlim := actual_centered_quantile_L1_limit K A C hdim hK hA hC
      a ha hAA hAC hCC he ⟪e, v⟫ (hv e)
    have hL1 : Tendsto (fun t : ℝ => ∫ τ, |(g t τ - f t τ) / t| ∂η)
        (𝓝[>] 0) (𝓝 0) := by
      apply Filter.Tendsto.congr' _ hlim
      filter_upwards [self_mem_nhdsWithin] with t ht
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with τ hτ
      dsimp only [g, f, B]
      rw [heightQuantile_minkowskiRay_sub_translation K C v e hK0 t hτ]
      congr 1
      field_simp [ne_of_gt ht]
      ring
    have hbase : g 0 =ᵐ[η] f 0 := by
      filter_upwards with τ
      simp only [g, f, body_zero_smul, add_zero]
    have hint : ∀ᶠ t in 𝓝[>] (0 : ℝ),
        Integrable (fun τ => ψ (f t τ)) η ∧
          Integrable (fun τ => ψ (g t τ)) η ∧
            Integrable (fun τ => (g t τ - f t τ) / t) η := by
      apply Eventually.of_forall
      intro t
      exact ⟨integrable_lipschitz_test η (hf t) ψ L hψ,
        integrable_lipschitz_test η (hg t) ψ L hψ, ((hg t).sub (hf t)).div_const t⟩
    have hderiv :=
      (hasDerivWithinAt_lipschitz_test_difference_zero η f g ψ L hψ hbase hint hL1).neg
    simp only [Pi.neg_def, neg_zero, neg_sub] at hderiv
    have hfa (t : ℝ) : (∫ τ, ψ (f t τ) ∂η) = ∫ x, ψ ⟪e, x⟫ ∂μ t :=
      integral_heightQuantile_test (K + t • A) e (hAt t) ψ hψ.continuous
    have hgb (t : ℝ) : (∫ τ, ψ (g t τ) ∂η) = ∫ x, ψ ⟪e, x⟫ ∂ν t :=
      integral_heightQuantile_test (K + t • B) e (hBt t) ψ hψ.continuous
    simpa only [hfa, hgb] using hderiv
  obtain ⟨hcos, hsin⟩ := fourier_variations_of_unit_lipschitz_variations μ ν hμ hν hunit
  refine ⟨-v, ?_⟩
  exact weak_hull_of_AF_conditional_ridge_variations K A C h0 a ha hAA hAC hCC (-v)
    hcos hsin

end OAI.PettyProjection
