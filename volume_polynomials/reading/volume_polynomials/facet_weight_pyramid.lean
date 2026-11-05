module

public import VolumePolynomials.PolytopeFirstVariation
public import VolumePolynomials.PolyhedralSupport
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section
set_option autoImplicit false

/-!
# First variation in fixed, unnormalized facet coordinates

The normalization is justified through actual pyramid volumes. For a facet
at normalized height one, its first-variation weight is the ambient dimension
times its radial pyramid volume. Computing that same pyramid in a fixed
unnormalized frame multiplies the fixed facet weight by its height. The
inverse height in the support function cancels it. Thus no identification of
different kernel measures is assumed or hidden in a change of coordinates.
-/

noncomputable section
open Set MeasureTheory Module
open scoped Pointwise BigOperators

-- Let the explicitly supplied kernel measure choose its Borel measurable
-- structure before the generic measurable-space instance for a subtype.
attribute [local instance 1100] MeasureSpace.toMeasurableSpace

namespace VolumePolynomials.FacetWeightPyramid

open HalfspacePyramids LinearFrame FacetAlmostEverywhere PolytopeFirstVariation
open OAI.Paper092

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [Fintype ι]
  [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]

theorem facetWeight_eq_dimension_mul_pyramid
    (l : ι → E →L[ℝ] ℝ)
    [∀ i, MeasureSpace (LinearMap.ker (l i).toLinearMap)]
    [∀ i, BorelSpace (LinearMap.ker (l i).toLinearMap)]
    [∀ i, Measure.IsAddHaarMeasure (volume : Measure (LinearMap.ker (l i).toLinearMap))]
    (hS : IsCompact (body l)) (i : ι) (v : E) (hv : l i v = 1) :
    facetWeight l i v hv = (finrank ℝ E : ℝ) *
      volume.real (PyramidVolume.radialHull (face l i)) := by
  first
  | have he := PyramidVolume.realVolume_radialHull_of_equiv
      (continuousEquiv (l i) v hv) (face_compact l hS i)
      (fun x hx => (show l i x = 1 from hx.2))
    rw [← facetBase_eq_image l i v hv, abs_one, mul_one,
      finrank_kernel_add_one (l i) v hv] at he
    have hd : (finrank ℝ E : ℝ) ≠ 0 := by
      first
      | have hn : finrank ℝ E ≠ 0 := by
          rw [← finrank_kernel_add_one (l i) v hv]
          omega
        exact_mod_cast hn
    rw [he, facetWeight]
    field_simp [hd]

theorem canonicalFacetWeight_eq_dimension_mul_pyramid
    (l : ι → E →L[ℝ] ℝ) (hS : IsCompact (body l))
    (i : ι) (v : E) (hv : l i v = 1) :
    canonicalFacetWeight l i v hv = (finrank ℝ E : ℝ) *
      volume.real (PyramidVolume.radialHull (face l i)) := by
  first
  | letI : ∀ j, MeasureSpace (LinearMap.ker (l j).toLinearMap) := fun _ => ⟨Measure.addHaar⟩
    letI : ∀ j, Measure.IsAddHaarMeasure (volume : Measure (LinearMap.ker (l j).toLinearMap)) :=
      fun _ => by change Measure.IsAddHaarMeasure Measure.addHaar; infer_instance
    exact facetWeight_eq_dimension_mul_pyramid l hS i v hv

def normalized (u : ι → E →L[ℝ] ℝ) (h : ι → ℝ) (i : ι) : E →L[ℝ] ℝ :=
  (h i)⁻¹ • u i

def fixedFace (u : ι → E →L[ℝ] ℝ) (h : ι → ℝ) (i : ι) : Set E :=
  {x | x ∈ PolyhedralSupport.body u h ∧ u i x = h i}

theorem normalized_body (u : ι → E →L[ℝ] ℝ) (h : ι → ℝ)
    (hp : ∀ i, 0 < h i) : body (normalized u h) = PolyhedralSupport.body u h := by
  first
  | ext x
    apply forall_congr'
    intro i
    change (h i)⁻¹ * u i x ≤ 1 ↔ u i x ≤ h i
    rw [← div_eq_inv_mul, div_le_one (hp i)]

theorem normalized_face (u : ι → E →L[ℝ] ℝ) (h : ι → ℝ)
    (hp : ∀ i, 0 < h i) (i : ι) : face (normalized u h) i = fixedFace u h i := by
  first
  | ext x
    change (x ∈ body (normalized u h) ∧ (h i)⁻¹ * u i x = 1) ↔ _
    rw [normalized_body u h hp, ← div_eq_inv_mul, div_eq_one_iff_eq (hp i).ne']
    rfl

theorem normalized_injective (u : ι → E →L[ℝ] ℝ) (h : ι → ℝ)
    (hp : ∀ i, 0 < h i)
    (hrel : ∀ i j {c : ℝ}, 0 < c → u i = c • u j → i = j) :
    Function.Injective (normalized u h) := by
  first
  | intro i j hij
    apply hrel i j (div_pos (hp i) (hp j))
    have he := congrArg (fun f : E →L[ℝ] ℝ => h i • f) hij
    simpa only [normalized, smul_smul, mul_inv_cancel₀ (hp i).ne', one_smul,
      div_eq_mul_inv] using he

theorem normalized_unit (u : ι → E →L[ℝ] ℝ) (h : ι → ℝ)
    (hp : ∀ i, 0 < h i) (i : ι) (v : E) (hv : u i v = 1) :
    normalized u h i (h i • v) = 1 := by
  first
  | simp only [normalized, ContinuousLinearMap.smul_apply, map_smul, smul_eq_mul,
      hv, mul_one, inv_mul_cancel₀ (hp i).ne', mul_inv_cancel₀ (hp i).ne']

section FixedMeasures

variable (u : ι → E →L[ℝ] ℝ)
  [∀ i, MeasureSpace (LinearMap.ker (u i).toLinearMap)]
  [∀ i, BorelSpace (LinearMap.ker (u i).toLinearMap)]
  [∀ i, Measure.IsAddHaarMeasure (volume : Measure (LinearMap.ker (u i).toLinearMap))]

def fixedFacetBase (h : ι → ℝ) (i : ι) (v : E) (hv : u i v = 1) :
    Set (LinearMap.ker (u i).toLinearMap) :=
  Prod.snd '' (continuousEquiv (u i) v hv '' fixedFace u h i)

def fixedFacetWeight (h : ι → ℝ) (i : ι) (v : E) (hv : u i v = 1) : ℝ :=
  (volumeFactor (continuousEquiv (u i) v hv) : ℝ) * volume.real (fixedFacetBase u h i v hv)

theorem dimension_mul_pyramid_eq_height_mul_weight
    (h : ι → ℝ) (hp : ∀ i, 0 < h i) (hS : IsCompact (PolyhedralSupport.body u h))
    (i : ι) (v : E) (hv : u i v = 1) :
    (finrank ℝ E : ℝ) * volume.real (PyramidVolume.radialHull (fixedFace u h i)) =
      h i * fixedFacetWeight u h i v hv := by
  first
  | have hface : IsCompact (fixedFace u h i) :=
      hS.inter_right (isClosed_eq (u i).continuous continuous_const)
    have he := PyramidVolume.realVolume_radialHull_of_equiv
      (continuousEquiv (u i) v hv) hface (fun x hx => hx.2)
    rw [abs_of_pos (hp i), finrank_kernel_add_one (u i) v hv] at he
    have hd : (finrank ℝ E : ℝ) ≠ 0 := by
      first
      | have hn : finrank ℝ E ≠ 0 := by
          rw [← finrank_kernel_add_one (u i) v hv]
          omega
        exact_mod_cast hn
    rw [he, fixedFacetWeight, fixedFacetBase]
    field_simp [hd]

theorem normalized_weight_mul_support (h : ι → ℝ) (hp : ∀ i, 0 < h i)
    (hS : IsCompact (PolyhedralSupport.body u h)) (i : ι) (v : E) (hv : u i v = 1)
    (A : Set E) :
    canonicalFacetWeight (normalized u h) i (h i • v) (normalized_unit u h hp i v hv) *
      SupportGeometry.support A (normalized u h i) =
        fixedFacetWeight u h i v hv * SupportGeometry.support A (u i) := by
  first
  | have hSn : IsCompact (body (normalized u h)) := by rwa [normalized_body u h hp]
    rw [canonicalFacetWeight_eq_dimension_mul_pyramid (normalized u h) hSn,
      normalized_face u h hp,
      dimension_mul_pyramid_eq_height_mul_weight u h hp hS i v hv]
    have hs : SupportGeometry.support A (normalized u h i) =
        (h i)⁻¹ * SupportGeometry.support A (u i) := by
      first
      | unfold SupportGeometry.support normalized
        rw [show ((h i)⁻¹ • u i) '' A = (h i)⁻¹ • (u i '' A) by
          ext y; simp only [Set.mem_image, Set.mem_smul_set, ContinuousLinearMap.smul_apply];
          constructor
          · rintro ⟨x, hx, rfl⟩; exact ⟨u i x, ⟨x, hx, rfl⟩, rfl⟩
          · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x, hx, rfl⟩]
        simpa only [smul_eq_mul] using
          Real.sSup_smul_of_nonneg (inv_nonneg.mpr (hp i).le) (u i '' A)
    rw [hs]
    field_simp [(hp i).ne']

/-- First variation with arbitrary positive heights and fixed lower-dimensional
kernel spaces. Every weight is a literal frame factor times a literal facet
measure, so it is suitable for exact coefficient comparison. -/
theorem first_variation_fixed_heights
    (h : ι → ℝ) (hp : ∀ i, 0 < h i)
    (hrel : ∀ i j {c : ℝ}, 0 < c → u i = c • u j → i = j)
    (hS : IsCompact (PolyhedralSupport.body u h))
    (v : ι → E) (hv : ∀ i, u i (v i) = 1)
    {A : Set E} (hAc : IsCompact A) (hA : Convex ℝ A) (hAne : A.Nonempty) :
    HasDerivWithinAt (fun t : ℝ => volume.real (PolyhedralSupport.body u h + t • A))
      (∑ i, fixedFacetWeight u h i (v i) (hv i) * SupportGeometry.support A (u i))
      (Ioi 0) 0 := by
  first
  | have hSn : IsCompact (body (normalized u h)) := by rwa [normalized_body u h hp]
    have hd := PolytopeFirstVariation.first_variation (normalized u h)
      (normalized_injective u h hp hrel) hSn (fun i => h i • v i)
      (fun i => normalized_unit u h hp i (v i) (hv i)) hAc hA hAne
    rw [normalized_body u h hp] at hd
    have he : (∑ i, canonicalFacetWeight (normalized u h) i (h i • v i)
        (normalized_unit u h hp i (v i) (hv i)) * SupportGeometry.support A (normalized u h i)) =
        ∑ i, fixedFacetWeight u h i (v i) (hv i) * SupportGeometry.support A (u i) :=
      Finset.sum_congr rfl (fun i _ => normalized_weight_mul_support u h hp hS i (v i) (hv i) A)
    rw [he] at hd
    exact hd

end FixedMeasures
end VolumePolynomials.FacetWeightPyramid
