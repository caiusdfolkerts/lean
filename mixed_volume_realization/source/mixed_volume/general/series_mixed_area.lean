module

public import mixed_volume.general.automaton_recurrence

/-! The mixed-area formula for genuine absolutely convergent segment sums.
The proof passes through finite zonotopes and Hausdorff-volume continuity. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace MixedVolume.SeriesMixedArea

open VolumePolynomials VolumePolynomials.PlanarMixedForm AutomatonWords Set MeasureTheory Filter
open scoped Topology Pointwise BigOperators

abbrev det := PlanarExtrusion.determinant

theorem det_neg_swap (u v : Plane) : det v u = -det u v := by
  dsimp [det, PlanarExtrusion.determinant]
  ring

theorem abs_det_swap (u v : Plane) : |det v u| = |det u v| := by
  rw [det_neg_swap, abs_neg]

theorem twice_mixed_segments (u v : Plane) :
    2 * mixedArea volume (PlanarCorner.segmentBody u) (PlanarCorner.segmentBody v) =
      |det u v| := by
  have h := PlanarCorner.twice_mixedArea_segment (PlanarCorner.segmentBody u) v
  change 2 * mixedArea volume (PlanarCorner.segmentBody u) (PlanarCorner.segmentBody v) =
    volume.real (PlanarExtrusion.determinant v '' PlanarExtrusion.centeredSegment u) at h
  rw [PlanarExtrusion.length_determinant_centeredSegment, abs_det_swap] at h
  exact h

theorem prefixBody_eq_sum (u : ℕ → Plane) (N : ℕ) :
    prefixBody u N = ∑ i ∈ Finset.range N, PlanarCorner.segmentBody (u i) := by
  induction N with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    apply ConvexBody.ext
    exact prefixSeries_zero u
  | succ N ih =>
    rw [Finset.sum_range_succ, ← ih]
    apply ConvexBody.ext
    change prefixSeries u (N + 1) = prefixSeries u N + PlanarExtrusion.centeredSegment (u N)
    rw [prefixSeries_succ, centeredSegment_eq_planar]

theorem twice_mixed_prefix (u v : ℕ → Plane) (M N : ℕ) :
    2 * mixedArea volume (prefixBody u M) (prefixBody v N) =
      ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range N, |det (u i) (v j)| := by
  rw [prefixBody_eq_sum, prefixBody_eq_sum, mixedArea_sum_left]
  simp_rw [mixedArea_sum_right]
  simp only [Finset.mul_sum, twice_mixed_segments]

theorem mixedArea_continuous :
    Continuous (fun p : ConvexBody Plane × ConvexBody Plane => mixedArea volume p.1 p.2) := by
  have hv := continuous_convexBody_realMeasure (volume : Measure Plane)
  have h := (((hv.comp (continuous_fst.add continuous_snd)).sub
    (hv.comp continuous_fst)).sub (hv.comp continuous_snd)).div_const 2
  convert h using 1
  funext p
  have ha := area_add volume PlanarCorner.plane_finrank p.1 p.2
  change mixedArea volume p.1 p.2 =
    (volume.real (↑(p.1 + p.2) : Set Plane) -
      volume.real (↑p.1 : Set Plane) - volume.real (↑p.2 : Set Plane)) / 2
  linarith

theorem abs_det_summable {ι κ : Type*} (u : ι → Plane) (v : κ → Plane)
    (hu : Summable fun i => ‖u i‖) (hv : Summable fun j => ‖v j‖) :
    Summable (fun p : ι × κ => |det (u p.1) (v p.2)|) := by
  have hprod := hu.mul_of_nonneg hv (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  apply (hprod.mul_left 2).of_norm_bounded
  intro p
  simp only [Real.norm_eq_abs, abs_abs]
  simpa only [mul_assoc] using abs_determinant_le_norm (u p.1) (v p.2)

theorem square_partial_tendsto {f : ℕ × ℕ → ℝ} (hf : Summable f) :
    Tendsto (fun N => ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, f (i, j))
      atTop (𝓝 (∑' p, f p)) := by
  have hdiag : Tendsto (fun N : ℕ => (Finset.range N, Finset.range N)) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_finset_range.prodMk tendsto_finset_range
  have hp := tendsto_finsetProd_atTop.comp hdiag
  have h := hf.hasSum.comp hp
  simpa only [Function.comp_def, Finset.sum_product] using h

theorem twice_mixed_nat (u v : ℕ → Plane)
    (hu : Summable fun i => ‖u i‖) (hv : Summable fun j => ‖v j‖) :
    2 * mixedArea volume (VolumePolynomials.segmentSeriesBody u hu)
      (VolumePolynomials.segmentSeriesBody v hv) =
        ∑' i, ∑' j, |det (u i) (v j)| := by
  have hc := (mixedArea_continuous.tendsto
    (VolumePolynomials.segmentSeriesBody u hu, VolumePolynomials.segmentSeriesBody v hv)).comp
      ((prefixBody_tendsto u hu).prodMk_nhds (prefixBody_tendsto v hv))
  have hleft := hc.const_mul 2
  have hsum := abs_det_summable u v hu hv
  have hright := square_partial_tendsto hsum
  have hlimit : 2 * mixedArea volume (VolumePolynomials.segmentSeriesBody u hu)
      (VolumePolynomials.segmentSeriesBody v hv) = ∑' p : ℕ × ℕ, |det (u p.1) (v p.2)| := by
    apply tendsto_nhds_unique _ hright
    simpa only [Function.comp_def, twice_mixed_prefix] using hleft
  rw [hlimit, hsum.tsum_prod]

theorem indexed_nat_eq (u : ℕ → Plane) (hu : Summable fun i => ‖u i‖) :
    IndexedSeries.segmentSeriesBody u hu = VolumePolynomials.segmentSeriesBody u hu := by
  apply ConvexBody.ext
  rfl

theorem reindex_body {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (u : κ → Plane) (hu : Summable fun i => ‖u i‖) :
    IndexedSeries.segmentSeriesBody (fun i => u (e i)) (e.summable_iff.mpr hu) =
      IndexedSeries.segmentSeriesBody u hu := by
  apply SeriesSupport.ext
  intro l
  rw [SeriesSupport.support_series, SeriesSupport.support_series]
  congr 1
  exact e.tsum_eq (fun i => |l (u i)|)

/-- The exact full mixed-area formula, with no assumption that a competing
body is a polygon or has finitely many generators. -/
theorem twice_mixed_indexed {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (e : ℕ ≃ ι) (f : ℕ ≃ κ) (u : ι → Plane) (v : κ → Plane)
    (hu : Summable fun i => ‖u i‖) (hv : Summable fun j => ‖v j‖) :
    2 * mixedArea volume (IndexedSeries.segmentSeriesBody u hu)
      (IndexedSeries.segmentSeriesBody v hv) = ∑' i, ∑' j, |det (u i) (v j)| := by
  rw [← reindex_body e u hu, ← reindex_body f v hv, indexed_nat_eq, indexed_nat_eq,
    twice_mixed_nat]
  calc
    (∑' i : ℕ, ∑' j : ℕ, |det (u (e i)) (v (f j))|) =
        ∑' i : ℕ, ∑' j : κ, |det (u (e i)) (v j)| := by
      apply tsum_congr
      intro i
      exact f.tsum_eq (fun j : κ => |det (u (e i)) (v j)|)
    _ = ∑' i : ι, ∑' j : κ, |det (u i) (v j)| := e.tsum_eq (fun i : ι => ∑' j : κ, |det (u i) (v j)|)

/-- A countable enumeration is used only to transport the proved analytic
limit theorem; no effective coefficient computation depends on this choice. -/
def wordEnumeration {s : ℕ} (hs : 0 < s) : ℕ ≃ Word s := by
  let a : Fin s := ⟨0, hs⟩
  have hinj : Function.Injective (fun n : ℕ => List.replicate n a) := by
    intro n k h
    have hh := congrArg List.length h
    simpa only [List.length_replicate] using hh
  letI : Infinite (Word s) := Infinite.of_injective _ hinj
  exact Classical.choice (inferInstance : Nonempty (ℕ ≃ Word s))

theorem twice_mixed_words {s : ℕ} (hs : 0 < s) (u v : Word s → Plane)
    (hu : Summable fun i => ‖u i‖) (hv : Summable fun j => ‖v j‖) :
    2 * mixedArea volume (IndexedSeries.segmentSeriesBody u hu)
      (IndexedSeries.segmentSeriesBody v hv) = ∑' i, ∑' j, |det (u i) (v j)| :=
  twice_mixed_indexed (wordEnumeration hs) (wordEnumeration hs) u v hu hv

end MixedVolume.SeriesMixedArea

end
