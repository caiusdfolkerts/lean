module

public import VolumePolynomials.MinkowskiSeriesLimits
public import VolumePolynomials.PlanarZonotope
public import VolumePolynomials.BodyContinuity
public import Mathlib.Analysis.Normed.Ring.InfiniteSum

@[expose] public section
noncomputable section

namespace VolumePolynomials

open scoped Topology Pointwise
open Set MeasureTheory Filter

theorem centeredSegment_eq_planar (v : ℝ × ℝ) :
    centeredSegment v = PlanarExtrusion.centeredSegment v := by
  first
  | ext x
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨t, t.property, ht.symm⟩
    · rintro ⟨t, ht, heq⟩
      exact ⟨⟨t, ht⟩, heq.symm⟩

theorem prefixSeries_eq_zonotope (u : ℕ → ℝ × ℝ) (N : ℕ) :
    prefixSeries u N = PlanarExtrusion.zonotope ((List.range N).map u) := by
  first
  | induction N with
    | zero => rw [prefixSeries_zero]; rfl
    | succ N ih =>
        rw [prefixSeries_succ, ih, centeredSegment_eq_planar, PlanarExtrusion.zonotope_range_succ]

theorem prefixBody_area (u : ℕ → ℝ × ℝ) (N : ℕ) :
    volume.real (prefixBody u N : Set (ℝ × ℝ)) =
      ∑ j ∈ Finset.range N, ∑ i ∈ Finset.range j, |PlanarExtrusion.determinant (u i) (u j)| := by
  first
  | change volume.real (prefixSeries u N) = _
    rw [prefixSeries_eq_zonotope, PlanarExtrusion.area_zonotope_range]

theorem abs_determinant_le_norm (p q : ℝ × ℝ) :
    |PlanarExtrusion.determinant p q| ≤ 2 * ‖p‖ * ‖q‖ := by
  first
  | have hpx : |p.1| ≤ ‖p‖ := by
      simpa [Prod.norm_def, Real.norm_eq_abs] using le_max_left ‖p.1‖ ‖p.2‖
    have hpy : |p.2| ≤ ‖p‖ := by
      simpa [Prod.norm_def, Real.norm_eq_abs] using le_max_right ‖p.1‖ ‖p.2‖
    have hqx : |q.1| ≤ ‖q‖ := by
      simpa [Prod.norm_def, Real.norm_eq_abs] using le_max_left ‖q.1‖ ‖q.2‖
    have hqy : |q.2| ≤ ‖q‖ := by
      simpa [Prod.norm_def, Real.norm_eq_abs] using le_max_right ‖q.1‖ ‖q.2‖
    calc
      |PlanarExtrusion.determinant p q| ≤ |p.1 * q.2| + |p.2 * q.1| := by
        simpa only [PlanarExtrusion.determinant, Real.norm_eq_abs] using
          norm_sub_le (p.1 * q.2) (p.2 * q.1)
      _ = |p.1| * |q.2| + |p.2| * |q.1| := by rw [abs_mul, abs_mul]
      _ ≤ ‖p‖ * ‖q‖ + ‖p‖ * ‖q‖ :=
        add_le_add (mul_le_mul hpx hqy (abs_nonneg _) (norm_nonneg _))
          (mul_le_mul hpy hqx (abs_nonneg _) (norm_nonneg _))
      _ = 2 * ‖p‖ * ‖q‖ := by ring

theorem determinant_rows_summable (u : ℕ → ℝ × ℝ) (hu : Summable fun n => ‖u n‖) :
    Summable (fun j => ∑ i ∈ Finset.range j, |PlanarExtrusion.determinant (u i) (u j)|) := by
  first
  | let f : ℕ × ℕ → ℝ := fun p => if p.2 < p.1 then
      |PlanarExtrusion.determinant (u p.2) (u p.1)| else 0
    have hprod := hu.mul_of_nonneg hu (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    have hf : Summable f := by
      apply (hprod.mul_left 2).of_norm_bounded
      intro p
      by_cases hp : p.2 < p.1
      · simp only [f, if_pos hp, Real.norm_eq_abs, abs_abs]
        exact (abs_determinant_le_norm (u p.2) (u p.1)).trans_eq (by ring)
      · simp only [f, if_neg hp, norm_zero]
        positivity
    have hrow (j : ℕ) : ∑' i, f (j, i) =
        ∑ i ∈ Finset.range j, |PlanarExtrusion.determinant (u i) (u j)| := by
      rw [tsum_eq_sum (s := Finset.range j) (by
        intro i hi
        simp only [Finset.mem_range] at hi
        simp [f, hi])]
      apply Finset.sum_congr rfl
      intro i hi
      simp [f, Finset.mem_range.mp hi]
    exact hf.prod.congr hrow

/-- The planar zonotope area formula passes to the actual infinite Minkowski sum by
Hausdorff convergence and continuity of actual Haar volume. -/
theorem area_infinite_segment_series (u : ℕ → ℝ × ℝ) (hu : Summable fun n => ‖u n‖) :
    volume.real (segmentSeriesBody u hu : Set (ℝ × ℝ)) =
      ∑' j, ∑ i ∈ Finset.range j, |PlanarExtrusion.determinant (u i) (u j)| := by
  first
  | have hvol := (continuous_convexBody_realMeasure
      (volume : Measure (ℝ × ℝ))).continuousAt.tendsto.comp (prefixBody_tendsto u hu)
    have hvol' : Tendsto
        (fun N => ∑ j ∈ Finset.range N,
          ∑ i ∈ Finset.range j, |PlanarExtrusion.determinant (u i) (u j)|)
        atTop (𝓝 (volume.real (segmentSeriesBody u hu : Set (ℝ × ℝ)))) := by
      simpa only [Function.comp_def, prefixBody_area] using hvol
    exact tendsto_nhds_unique hvol' (determinant_rows_summable u hu).hasSum.tendsto_sum_nat

end VolumePolynomials
