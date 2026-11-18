module

public import VolumePolynomials.PolytopeConeFirstVariation
public import VolumePolynomials.PolytopeFoundation

@[expose] public section
set_option autoImplicit false

/-! # Actual first variation of a finite halfspace polytope

The derivative is proved by summing fixed old facet sectors. Each coefficient
is the actual Haar change-of-frame factor times the actual facet-base measure.
No mixed-volume formula, divergence theorem, or cancellation of moving facet
derivatives is assumed.
-/

noncomputable section
open Set Filter MeasureTheory Module
open scoped Pointwise Topology BigOperators

-- Keep the specified facet measures and their Borel structures on the same
-- measurable space when the facet is presented as an ambient subtype.
attribute [local instance 1100] MeasureSpace.toMeasurableSpace

namespace VolumePolynomials.PolytopeFirstVariation

open HalfspacePyramids LinearFrame FacetAlmostEverywhere PolytopeRadialGeometry
open RadialSectorDecomposition ClippedConeVolume PolytopeConeFirstVariation
open OAI.Paper092

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [Fintype ι]
  [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]

section GivenFacetMeasures

variable (l : ι → E →L[ℝ] ℝ)
  [∀ i, MeasureSpace (LinearMap.ker (l i).toLinearMap)]
  [∀ i, BorelSpace (LinearMap.ker (l i).toLinearMap)]
  [∀ i, Measure.IsAddHaarMeasure (volume : Measure (LinearMap.ker (l i).toLinearMap))]

def facetWeight (i : ι) (v : E) (hv : l i v = 1) : ℝ :=
  (volumeFactor (continuousEquiv (l i) v hv) : ℝ) * volume.real (facetBase l i v)

theorem facetWeight_nonneg (i : ι) (v : E) (hv : l i v = 1) :
    0 ≤ facetWeight l i v hv :=
  mul_nonneg (NNReal.coe_nonneg _) measureReal_nonneg

theorem realVolume_add_smul_translate (S A : Set E) (a : E) (t : ℝ) :
    volume.real (S + t • (({a} : Set E) + A)) = volume.real (S + t • A) := by
  first
  | rw [smul_add, Set.smul_set_singleton,
      show S + (({t • a} : Set E) + t • A) = ({t • a} : Set E) + (S + t • A) by ac_rfl,
      Set.singleton_add]
    simp only [measureReal_def, Set.image_add_left, measure_preimage_add]

theorem sector_volume_identity (hS : IsCompact (body l)) (i : ι)
    (v : E) (hv : l i v = 1) {A : Set E} (hA : IsCompact A)
    {R : ℝ} (hR : 0 ≤ R) (t : ℝ) :
    volume.real ((body l + t • A) ∩ radialTruncation R (face l i)) =
      (volumeFactor (continuousEquiv (l i) v hv) : ℝ) *
        ∫ y in facetBase l i v, radialSlice (finrank ℝ (LinearMap.ker (l i).toLinearMap))
          R (movingFrame l i v hv A t) y := by
  first
  | rw [realVolume_eq_factor_mul_image (continuousEquiv (l i) v hv),
      image_sector_intersection_frame]
    change (volumeFactor (continuousEquiv (l i) v hv) : ℝ) *
      volume.real (clippedCone R (facetBase l i v) (movingFrame l i v hv A t)) = _
    rw [realVolume_clippedCone hR (facetBase_compact l hS i v hv)
      (IsCompact.isClosed (movingFrame_compact l i v hv hS hA t))]

theorem tendsto_sector_volume_quotient
    (hl : Function.Injective l) (hS : IsCompact (body l))
    (i : ι) (v : E) (hv : l i v = 1)
    {A : Set E} (hAcompact : IsCompact A) (hA : Convex ℝ A) (hA0 : (0 : E) ∈ A)
    {a : E} (ha : a ∈ A) (hmax : ∀ x ∈ A, l i x ≤ l i a)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x ∈ A, l i x ≤ C) :
    Tendsto (fun t : ℝ =>
      (volume.real ((body l + t • A) ∩ radialTruncation (1 + C) (face l i)) -
        volume.real ((body l + (0 : ℝ) • A) ∩ radialTruncation (1 + C) (face l i))) / t)
      (𝓝[>] 0) (𝓝 (facetWeight l i v hv * l i a)) := by
  first
  | have h := Filter.Tendsto.const_mul
      (volumeFactor (continuousEquiv (l i) v hv) : ℝ)
      (tendsto_facet_integral_quotient l hl hS i v hv hAcompact hA hA0 ha hmax hC hbound)
    have heq : (volumeFactor (continuousEquiv (l i) v hv) : ℝ) *
        (l i a * volume.real (facetBase l i v)) = facetWeight l i v hv * l i a := by
      first
      | unfold facetWeight
        ring
    rw [heq] at h
    apply h.congr'
    exact Eventually.of_forall fun t => by
      dsimp only
      rw [sector_volume_identity l hS i v hv hAcompact (by positivity) t,
        sector_volume_identity l hS i v hv hAcompact (by positivity) 0]
      ring

/-- First variation for any compact convex added set containing the origin.
All support values on the right are the actual suprema on that set. -/
theorem tendsto_volume_quotient_centered
    (hl : Function.Injective l) (hS : IsCompact (body l))
    (v : ι → E) (hv : ∀ i, l i (v i) = 1)
    {A : Set E} (hAcompact : IsCompact A) (hA : Convex ℝ A) (hA0 : (0 : E) ∈ A) :
    Tendsto (fun t : ℝ => (volume.real (body l + t • A) - volume.real (body l)) / t)
      (𝓝[>] 0)
      (𝓝 (∑ i, facetWeight l i (v i) (hv i) * SupportGeometry.support A (l i))) := by
  first
  | classical
    obtain ⟨C, hC, hbound⟩ := exists_uniform_normal_bound l hAcompact
    choose a ha hsupp using fun i => SupportGeometry.exists_support hAcompact ⟨0, hA0⟩ (l i)
    have hmax (i : ι) (x : E) (hx : x ∈ A) : l i x ≤ l i (a i) := by
      first
      | rw [hsupp i]
        exact SupportGeometry.le_support hAcompact (l i) hx
    let f : ι → ℝ → ℝ := fun i t =>
      volume.real ((body l + t • A) ∩ radialTruncation (1 + C) (face l i))
    have hlim (i : ι) :
        Tendsto (fun t : ℝ => (f i t - f i 0) / t) (𝓝[>] 0)
          (𝓝 (facetWeight l i (v i) (hv i) * SupportGeometry.support A (l i))) := by
      first
      | rw [← hsupp i]
        exact tendsto_sector_volume_quotient l hl hS i (v i) (hv i) hAcompact hA hA0
          (ha i) (hmax i) hC (fun x hx => (le_abs_self _).trans (hbound i x hx))
    have hsum := tendsto_finsetSum Finset.univ (fun i _ => hlim i)
    have hdecomp {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
        volume.real (body l + t • A) = ∑ i, f i t := by
      first
      | apply realVolume_eq_sum_sector_intersections l hl hS (by positivity)
          (hS.add (hAcompact.smul t))
        intro x hx
        apply Iff.mpr (mem_smul_body_iff l (by positivity : 0 < 1 + C) x)
        have hx' := add_smul_subset_smul_body l hC ht
          (fun i a ha => (le_abs_self _).trans (hbound i a ha)) hx
        have hb := Iff.mp (mem_smul_body_iff l (by positivity : 0 < 1 + t * C) x) hx'
        intro i
        exact (hb i).trans (by nlinarith)
    have hzero : body l + (0 : ℝ) • A = body l := by
      first
      | rw [Set.zero_smul_set ⟨0, hA0⟩]
        simp
    have hlt : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (show ∀ᶠ t : ℝ in 𝓝 0, t < 1 from Iio_mem_nhds zero_lt_one)
    apply hsum.congr'
    filter_upwards [self_mem_nhdsWithin, hlt] with t ht ht1
    rw [hdecomp ht.le ht1.le, ← hzero, hdecomp le_rfl zero_le_one,
      ← Finset.sum_sub_distrib, Finset.sum_div]

/-- The balance identity follows from actual translation invariance applied to
the two oppositely oriented segments. It is not an assumed divergence theorem. -/
theorem facet_balance
    (hl : Function.Injective l) (hS : IsCompact (body l))
    (v : ι → E) (hv : ∀ i, l i (v i) = 1) (a : E) :
    (∑ i, facetWeight l i (v i) (hv i) * l i a) = 0 := by
  first
  | have hp := tendsto_volume_quotient_centered l hl hS v hv
      (SupportGeometry.isCompact_segment (0 : E) a) (convex_segment (0 : E) a)
      (left_mem_segment ℝ (0 : E) a)
    have hm := tendsto_volume_quotient_centered l hl hS v hv
      (SupportGeometry.isCompact_segment (0 : E) (-a)) (convex_segment (0 : E) (-a))
      (left_mem_segment ℝ (0 : E) (-a))
    have htranslate : segment ℝ (0 : E) a = ({a} : Set E) + segment ℝ (0 : E) (-a) := by
      first
      | rw [Set.singleton_add]
        change segment ℝ (0 : E) a = a +ᵥ segment ℝ (0 : E) (-a)
        rw [vadd_segment]
        simp only [vadd_eq_add, add_zero, add_neg_cancel]
        exact segment_symm ℝ 0 a
    have hsame (t : ℝ) : volume.real (body l + t • segment ℝ (0 : E) a) =
        volume.real (body l + t • segment ℝ (0 : E) (-a)) := by
      first
      | rw [htranslate, realVolume_add_smul_translate]
    have heq := tendsto_nhds_unique hp (hm.congr' (Eventually.of_forall fun t => by
      dsimp only
      rw [hsame]))
    simp only [SupportGeometry.support_segment, map_zero, map_neg] at heq
    have hmax (x : ℝ) : max 0 x - max 0 (-x) = x := by
      first
      | by_cases hx : 0 ≤ x
        · rw [max_eq_right hx, max_eq_left (neg_nonpos.mpr hx), sub_zero]
        · have hx' : x ≤ 0 := (lt_of_not_ge hx).le
          rw [max_eq_left hx', max_eq_right (neg_nonneg.mpr hx'), zero_sub, neg_neg]
    calc
      (∑ i, facetWeight l i (v i) (hv i) * l i a) =
          ∑ i, facetWeight l i (v i) (hv i) * (max 0 (l i a) - max 0 (-l i a)) := by
        first
        | simp only [hmax]
      _ = (∑ i, facetWeight l i (v i) (hv i) * max 0 (l i a)) -
          ∑ i, facetWeight l i (v i) (hv i) * max 0 (-l i a) := by
        first
        | simp only [mul_sub, Finset.sum_sub_distrib]
      _ = 0 := sub_eq_zero.mpr heq

/-- Full first variation for an arbitrary nonempty compact convex added set.
The support values and Haar facet weights retain their literal meanings. -/
theorem tendsto_volume_quotient
    (hl : Function.Injective l) (hS : IsCompact (body l))
    (v : ι → E) (hv : ∀ i, l i (v i) = 1)
    {A : Set E} (hAcompact : IsCompact A) (hA : Convex ℝ A) (hAne : A.Nonempty) :
    Tendsto (fun t : ℝ => (volume.real (body l + t • A) - volume.real (body l)) / t)
      (𝓝[>] 0)
      (𝓝 (∑ i, facetWeight l i (v i) (hv i) * SupportGeometry.support A (l i))) := by
  first
  | classical
    obtain ⟨a, ha⟩ := hAne
    let A' : Set E := ({-a} : Set E) + A
    have hA'compact : IsCompact A' := isCompact_singleton.add hAcompact
    have hA' : Convex ℝ A' := (convex_singleton (-a)).add hA
    have hA'0 : (0 : E) ∈ A' := ⟨-a, rfl, a, ha, neg_add_cancel a⟩
    have hsupp (i : ι) : SupportGeometry.support A' (l i) =
        -l i a + SupportGeometry.support A (l i) := by
      first
      | dsimp only [A']
        rw [SupportGeometry.support_add isCompact_singleton (singleton_nonempty _)
          hAcompact ⟨a, ha⟩]
        simp [SupportGeometry.support, map_neg]
    have h := tendsto_volume_quotient_centered l hl hS v hv hA'compact hA' hA'0
    have hsum : (∑ i, facetWeight l i (v i) (hv i) * SupportGeometry.support A' (l i)) =
        ∑ i, facetWeight l i (v i) (hv i) * SupportGeometry.support A (l i) := by
      first
      | simp_rw [hsupp, mul_add, mul_neg]
        rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, facet_balance l hl hS v hv a,
          neg_zero, zero_add]
    rw [hsum] at h
    apply h.congr'
    exact Eventually.of_forall fun t => by
      dsimp only
      rw [show A' = ({-a} : Set E) + A from rfl, realVolume_add_smul_translate]

theorem hasDerivWithinAt_volume
    (hl : Function.Injective l) (hS : IsCompact (body l))
    (v : ι → E) (hv : ∀ i, l i (v i) = 1)
    {A : Set E} (hAcompact : IsCompact A) (hA : Convex ℝ A) (hAne : A.Nonempty) :
    HasDerivWithinAt (fun t : ℝ => volume.real (body l + t • A))
      (∑ i, facetWeight l i (v i) (hv i) * SupportGeometry.support A (l i)) (Ioi 0) 0 := by
  first
  | apply (hasDerivWithinAt_iff_tendsto_slope' (self_notMem_Ioi : (0 : ℝ) ∉ Ioi 0)).mpr
    have hzero : body l + (0 : ℝ) • A = body l := by
      first
      | rw [Set.zero_smul_set hAne]
        simp
    change Tendsto (fun t : ℝ => slope (fun s : ℝ => volume.real (body l + s • A)) 0 t) _ _
    simpa only [slope_def_field, hzero, sub_zero] using
      tendsto_volume_quotient l hl hS v hv hAcompact hA hAne

end GivenFacetMeasures

/-- Canonical actual Haar measures on the facet kernels, so the final endpoint
has no unprovided family of lower-dimensional measures as a hypothesis. -/
def canonicalFacetWeight (l : ι → E →L[ℝ] ℝ) (i : ι) (v : E) (hv : l i v = 1) : ℝ :=
  letI : ∀ j, MeasureSpace (LinearMap.ker (l j).toLinearMap) := fun _ => ⟨Measure.addHaar⟩
  letI : ∀ j, Measure.IsAddHaarMeasure (volume : Measure (LinearMap.ker (l j).toLinearMap)) :=
    fun _ => by change Measure.IsAddHaarMeasure Measure.addHaar; infer_instance
  facetWeight l i v hv

theorem canonicalFacetWeight_nonneg (l : ι → E →L[ℝ] ℝ)
    (i : ι) (v : E) (hv : l i v = 1) : 0 ≤ canonicalFacetWeight l i v hv := by
  first
  | letI : ∀ j, MeasureSpace (LinearMap.ker (l j).toLinearMap) := fun _ => ⟨Measure.addHaar⟩
    letI : ∀ j, Measure.IsAddHaarMeasure (volume : Measure (LinearMap.ker (l j).toLinearMap)) :=
      fun _ => by change Measure.IsAddHaarMeasure Measure.addHaar; infer_instance
    exact facetWeight_nonneg l i v hv

theorem firstVariation_coefficient_mono (l : ι → E →L[ℝ] ℝ)
    (v : ι → E) (hv : ∀ i, l i (v i) = 1)
    {A B : Set E} (hA : A.Nonempty) (hB : IsCompact B) (hAB : A ⊆ B) :
    (∑ i, canonicalFacetWeight l i (v i) (hv i) * SupportGeometry.support A (l i)) ≤
      ∑ i, canonicalFacetWeight l i (v i) (hv i) * SupportGeometry.support B (l i) := by
  first
  | apply Finset.sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonneg_left _ (canonicalFacetWeight_nonneg l i (v i) (hv i))
    exact SupportGeometry.support_le hA (l i)
      (fun x hx => SupportGeometry.le_support hB (l i) (hAB hx))

theorem first_variation (l : ι → E →L[ℝ] ℝ)
    (hl : Function.Injective l) (hS : IsCompact (body l))
    (v : ι → E) (hv : ∀ i, l i (v i) = 1)
    {A : Set E} (hAcompact : IsCompact A) (hA : Convex ℝ A) (hAne : A.Nonempty) :
    HasDerivWithinAt (fun t : ℝ => volume.real (body l + t • A))
      (∑ i, canonicalFacetWeight l i (v i) (hv i) * SupportGeometry.support A (l i))
      (Ioi 0) 0 := by
  first
  | letI : ∀ j, MeasureSpace (LinearMap.ker (l j).toLinearMap) := fun _ => ⟨Measure.addHaar⟩
    letI : ∀ j, Measure.IsAddHaarMeasure (volume : Measure (LinearMap.ker (l j).toLinearMap)) :=
      fun _ => by change Measure.IsAddHaarMeasure Measure.addHaar; infer_instance
    exact hasDerivWithinAt_volume l hl hS v hv hAcompact hA hAne

end VolumePolynomials.PolytopeFirstVariation
