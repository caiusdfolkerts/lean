module

public import VolumePolynomials.RadialSectorDecomposition

@[expose] public section
set_option autoImplicit false

/-! # First variation on one fixed old facet cone

The moving body is the actual Minkowski sum. The proof uses the exact radial
endpoint off the lower-dimensional intersections, a uniform polynomial bound,
and dominated convergence. The support maximizer is an actual point of the
added compact body, whose existence follows from compactness.
-/

noncomputable section
open Set Filter MeasureTheory Module
open scoped Pointwise Topology BigOperators

-- The supplied kernel MeasureSpace determines its measurable-space structure.
-- Give that projection priority over the inherited ambient subtype instance.
attribute [local instance 1100] MeasureSpace.toMeasurableSpace

namespace VolumePolynomials.PolytopeConeFirstVariation

open HalfspacePyramids LinearFrame FacetAlmostEverywhere PolytopeRadialGeometry
open RadialSectorDecomposition ClippedConeVolume ConeDerivative

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι]

def movingFrame (l : ι → E →L[ℝ] ℝ) (i : ι) (v : E) (hv : l i v = 1)
    (A : Set E) (t : ℝ) : Set (ℝ × LinearMap.ker (l i).toLinearMap) :=
  continuousEquiv (l i) v hv '' (body l + t • A)

theorem movingFrame_compact (l : ι → E →L[ℝ] ℝ) (i : ι) (v : E)
    (hv : l i v = 1) (hS : IsCompact (body l)) {A : Set E} (hA : IsCompact A)
    (t : ℝ) : IsCompact (movingFrame l i v hv A t) :=
  (hS.add (hA.smul t)).image (continuousEquiv (l i) v hv).continuous

theorem radialSlice_moving_bounds
    (l : ι → E →L[ℝ] ℝ) (i : ι) (v : E) (hv : l i v = 1)
    {A : Set E} (hA0 : (0 : E) ∈ A) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ a ∈ A, l i a ≤ C) (k : ℕ)
    {y : LinearMap.ker (l i).toLinearMap} (hy : y ∈ facetBase l i v)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    1 / ((k + 1 : ℕ) : ℝ) ≤ radialSlice k (1 + C) (movingFrame l i v hv A t) y ∧
      radialSlice k (1 + C) (movingFrame l i v hv A t) y ≤
        (1 + t * C) ^ (k + 1) / ((k + 1 : ℕ) : ℝ) := by
  first
  | have hq := facetBase_point_mem_face l i v hv hy
    constructor
    · simpa only [one_pow] using power_le_radialSlice_of_lower_bound k
        (by norm_num : (0 : ℝ) ≤ 1) (by linarith : (1 : ℝ) ≤ 1 + C)
        (movingFrame l i v hv A t) y (by
          intro r hr hr1
          rw [movingFrame, radialMap_mem_frame_image_iff]
          exact body_subset_add_smul l hA0 t
            ((convex_body l).smul_mem_of_zero_mem (zero_mem_body l) hq.1 ⟨hr, hr1⟩))
    · apply radialSlice_le_power_of_upper_bound k (by positivity)
        (by nlinarith : 1 + t * C ≤ 1 + C)
      intro r hr hrK
      rw [movingFrame, radialMap_mem_frame_image_iff] at hrK
      rcases hrK with ⟨s, hs, z, ⟨a, ha, rfl⟩, heq⟩
      have he := congrArg (l i) heq
      simp only [map_add, map_smul, smul_eq_mul, hq.2, mul_one] at he
      have hb := mul_le_mul_of_nonneg_left (hbound a ha) ht
      linarith [hs i]

theorem radialSlice_moving_zero
    (l : ι → E →L[ℝ] ℝ) (i : ι) (v : E) (hv : l i v = 1)
    {A : Set E} (hA0 : (0 : E) ∈ A) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ a ∈ A, l i a ≤ C) (k : ℕ)
    {y : LinearMap.ker (l i).toLinearMap} (hy : y ∈ facetBase l i v) :
    radialSlice k (1 + C) (movingFrame l i v hv A 0) y = 1 / ((k + 1 : ℕ) : ℝ) := by
  first
  | have h := radialSlice_moving_bounds l i v hv hA0 hC hbound k hy (t := 0)
      le_rfl zero_le_one
    simp only [zero_mul, add_zero, one_pow] at h
    exact le_antisymm h.2 h.1

theorem radialSlice_moving_quotient_bound
    (l : ι → E →L[ℝ] ℝ) (i : ι) (v : E) (hv : l i v = 1)
    {A : Set E} (hA0 : (0 : E) ∈ A) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ a ∈ A, l i a ≤ C) (k : ℕ)
    {y : LinearMap.ker (l i).toLinearMap} (hy : y ∈ facetBase l i v)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    |(radialSlice k (1 + C) (movingFrame l i v hv A t) y -
        radialSlice k (1 + C) (movingFrame l i v hv A 0) y) / t| ≤ C * (1 + C) ^ k := by
  first
  | rw [radialSlice_moving_zero l i v hv hA0 hC hbound k hy]
    have hb := radialSlice_moving_bounds l i v hv hA0 hC hbound k hy ht.le ht1
    rw [abs_of_nonneg (div_nonneg (sub_nonneg.mpr hb.1) ht.le)]
    calc
      (radialSlice k (1 + C) (movingFrame l i v hv A t) y - 1 / ((k + 1 : ℕ) : ℝ)) / t ≤
          ((1 + t * C) ^ (k + 1) / ((k + 1 : ℕ) : ℝ) -
            1 / ((k + 1 : ℕ) : ℝ)) / t :=
        div_le_div_of_nonneg_right (sub_le_sub_right hb.2 _) ht.le
      _ = ((1 + t * C) ^ (k + 1) - 1) / (((k + 1 : ℕ) : ℝ) * t) := by ring
      _ ≤ _ := radialPower_quotient_bound k hC ht ht1

theorem tendsto_radialSlice_moving_quotient
    (l : ι → E →L[ℝ] ℝ) (i : ι) (v : E) (hv : l i v = 1)
    {A : Set E} (hA : Convex ℝ A) (hA0 : (0 : E) ∈ A)
    {a : E} (ha : a ∈ A) (hmax : ∀ x ∈ A, l i x ≤ l i a)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x ∈ A, l i x ≤ C) (k : ℕ)
    {y : LinearMap.ker (l i).toLinearMap} (hy : y ∈ facetBase l i v)
    (hstrict : ∀ j, j ≠ i → l j (v + y.val) < 1) :
    Tendsto (fun t : ℝ =>
      (radialSlice k (1 + C) (movingFrame l i v hv A t) y -
        radialSlice k (1 + C) (movingFrame l i v hv A 0) y) / t)
      (𝓝[>] 0) (𝓝 (l i a)) := by
  first
  | have hc : 0 ≤ l i a := by simpa using hmax 0 hA0
    have hcC : l i a ≤ C := hbound a ha
    have hevent := (eventually_radial_mem_iff l i
      (facetBase_point_mem_face l i v hv hy) hstrict hA hA0 ha hmax).filter_mono
        (nhdsWithin_mono _ Ioi_subset_Ici_self)
    have hlt : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (show ∀ᶠ t : ℝ in 𝓝 0, t < 1 from Iio_mem_nhds zero_lt_one)
    apply (tendsto_radialPower_quotient k (l i a)).congr'
    filter_upwards [hevent, self_mem_nhdsWithin, hlt] with t ht ht0 ht1
    change 0 < t at ht0
    have hlam : 0 ≤ 1 + t * l i a := by positivity
    have hlamR : 1 + t * l i a ≤ 1 + C := by nlinarith
    rw [radialSlice_moving_zero l i v hv hA0 hC hbound k hy,
      radialSlice_eq_power_of_interval k hlam hlamR (movingFrame l i v hv A t) y]
    intro r hr
    rw [movingFrame, radialMap_mem_frame_image_iff]
    exact ht r hr

section Measure

variable [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]

/-- The actual integral over one old facet has right derivative equal to its
support displacement times its actual lower-dimensional Haar measure. -/
theorem tendsto_facet_integral_quotient
    (l : ι → E →L[ℝ] ℝ) (hl : Function.Injective l) (hS : IsCompact (body l))
    (i : ι) (v : E) (hv : l i v = 1)
    {A : Set E} (hAcompact : IsCompact A) (hA : Convex ℝ A) (hA0 : (0 : E) ∈ A)
    {a : E} (ha : a ∈ A) (hmax : ∀ x ∈ A, l i x ≤ l i a)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x ∈ A, l i x ≤ C)
    [MeasureSpace (LinearMap.ker (l i).toLinearMap)]
    [BorelSpace (LinearMap.ker (l i).toLinearMap)]
    [Measure.IsAddHaarMeasure (volume : Measure (LinearMap.ker (l i).toLinearMap))] :
    Tendsto (fun t : ℝ =>
      ((∫ y in facetBase l i v, radialSlice (finrank ℝ (LinearMap.ker (l i).toLinearMap))
          (1 + C) (movingFrame l i v hv A t) y) -
        ∫ y in facetBase l i v, radialSlice (finrank ℝ (LinearMap.ker (l i).toLinearMap))
          (1 + C) (movingFrame l i v hv A 0) y) / t)
      (𝓝[>] 0) (𝓝 (l i a * volume.real (facetBase l i v))) := by
  first
  | let k := finrank ℝ (LinearMap.ker (l i).toLinearMap)
    let B := facetBase l i v
    let μ : Measure (LinearMap.ker (l i).toLinearMap) := volume.restrict B
    let F : ℝ → (LinearMap.ker (l i).toLinearMap) → ℝ :=
      fun t => radialSlice k (1 + C) (movingFrame l i v hv A t)
    have hB := facetBase_compact l hS i v hv
    letI : IsFiniteMeasure μ := ⟨by
      simpa only [μ, B, Measure.restrict_apply_univ] using hB.measure_lt_top⟩
    have hFi (t : ℝ) : Integrable (F t) μ :=
      integrableOn_radialSlice k (by positivity) hB
        (IsCompact.measurableSet (movingFrame_compact l i v hv hS hAcompact t))
    have hbound' : ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ᵐ y ∂μ,
        |(F t y - F 0 y) / t| ≤ C * (1 + C) ^ k := by
      first
      | have hlt : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
          Filter.Eventually.filter_mono nhdsWithin_le_nhds
            (show ∀ᶠ t : ℝ in 𝓝 0, t < 1 from Iio_mem_nhds zero_lt_one)
        filter_upwards [self_mem_nhdsWithin, hlt] with t ht ht1
        filter_upwards [ae_restrict_mem hB.measurableSet] with y hy
        exact radialSlice_moving_quotient_bound l i v hv hA0 hC hbound k hy ht ht1.le
    have hlim : ∀ᵐ y ∂μ, Tendsto (fun t : ℝ => (F t y - F 0 y) / t)
        (𝓝[>] 0) (𝓝 (l i a)) := by
      first
      | filter_upwards [ae_restrict_mem hB.measurableSet,
          ae_strict_other_facets l hl hS i v hv volume] with y hy hstrict
        exact tendsto_radialSlice_moving_quotient l i v hv hA hA0 ha hmax hC hbound k hy hstrict
    have h := tendsto_integral_difference_quotient μ F (fun _ => l i a)
      (C * (1 + C) ^ k) (hFi 0) (Eventually.of_forall hFi) hbound' hlim
    simpa only [F, k, μ, B, integral_const, measureReal_restrict_apply_univ,
      smul_eq_mul, mul_comm] using h

end Measure
end VolumePolynomials.PolytopeConeFirstVariation
