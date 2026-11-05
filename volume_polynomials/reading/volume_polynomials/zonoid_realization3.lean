module

public import VolumePolynomials.ZonotopePolynomial3
public import VolumePolynomials.MinkowskiSeriesLimits
public import VolumePolynomials.RealizationContinuity

@[expose] public section

/-!
# Volume polynomials for arbitrary summable segment-series tuples in three dimensions

Finite prefixes are actual finite zonotopes. Their homogeneous volume polynomials
pass to the Hausdorff limit through the closed finite-dimensional evaluation
range. No coefficient-series formula, mixed-volume axiom, or general Minkowski
polynomial theorem is assumed.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology Pointwise

namespace VolumePolynomials

theorem prefixSeries_eq_finiteCarrier
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (u : ℕ → E) (N : ℕ) :
    prefixSeries u N = FiniteZonotope.carrier ((List.range N).map u) := by
  first
  | induction N with
    | zero => rw [prefixSeries_zero]; rfl
    | succ N ih =>
        have hsegment : centeredSegment (u N) = FiniteZonotope.segment (u N) :=
          centeredSegment_eq_image (u N)
        rw [prefixSeries_succ, FiniteZonotope.carrier_range_succ, ih, hsegment]

theorem prefixBody_eq_finiteBody (u : ℕ → Space 3) (N : ℕ) :
    prefixBody u N = FiniteZonotope.toBody ((List.range N).map u) := by
  first
  | apply ConvexBody.ext
    exact prefixSeries_eq_finiteCarrier u N

/-- Every finite tuple of summable three-dimensional segment series has a full
homogeneous cubic volume polynomial with the paper's exact geometric semantics. -/
theorem summable_segment_series_realizes {n : ℕ} (u : Fin n → ℕ → Space 3)
    (hu : ∀ i, Summable (fun j => ‖u i j‖)) :
    ∃ c : Coefficients n 3, Realizes (fun i => segmentSeriesBody (u i) (hu i)) c := by
  first
  | apply exists_realizes_of_tendsto (l := (Filter.atTop : Filter ℕ))
      (L := fun (N : ℕ) i => prefixBody (u i) N)
    · exact tendsto_pi_nhds.mpr (fun i => prefixBody_tendsto (u i) (hu i))
    · apply Filter.Eventually.of_forall
      intro N
      simpa only [prefixBody_eq_finiteBody] using
        FiniteZonotope.exists_realizes (fun i => (List.range N).map (u i))

end VolumePolynomials
