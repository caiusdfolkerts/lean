module

public import VolumePolynomials.CenteredFacetFamily

@[expose] public section
set_option autoImplicit false

/-!
# Facet-volume decomposition of positive sums of finite convex hulls

Every entry of the decomposition is built from the given bodies: a nonzero
facet functional, its kernel, a genuine additive Haar measure on that kernel,
and the projected exposed faces of the summands. The volume identity follows
from the exact halfspace representation, disjoint radial pyramids, and Fubini.
-/

noncomputable section
open Set MeasureTheory MeasureTheory.Measure Module
open scoped Pointwise BigOperators

namespace VolumePolynomials.PolytopeGeometry

open OAI.Paper092

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)]

def kernelMeasure (l : E →L[ℝ] ℝ) : Measure (LinearMap.ker l.toLinearMap) :=
  Measure.addHaar

instance kernelMeasure_isAddHaarMeasure (l : E →L[ℝ] ℝ) :
    IsAddHaarMeasure (kernelMeasure l) := by
  first
  | unfold kernelMeasure
    infer_instance

def facetConstant (l : E →L[ℝ] ℝ) (v : E) (hv : l v = 1) : ℝ :=
  letI : MeasureSpace (LinearMap.ker l.toLinearMap) := ⟨kernelMeasure l⟩
  letI : IsAddHaarMeasure (volume : Measure (LinearMap.ker l.toLinearMap)) :=
    kernelMeasure_isAddHaarMeasure l
  (LinearFrame.volumeFactor (LinearFrame.continuousEquiv l v hv) : ℝ) /
    ((finrank ℝ (LinearMap.ker l.toLinearMap) + 1 : ℕ) : ℝ)

theorem facetConstant_pos (l : E →L[ℝ] ℝ) (v : E) (hv : l v = 1) :
    0 < facetConstant l v hv := by
  first
  | letI : MeasureSpace (LinearMap.ker l.toLinearMap) := ⟨kernelMeasure l⟩
    letI : IsAddHaarMeasure (volume : Measure (LinearMap.ker l.toLinearMap)) :=
      kernelMeasure_isAddHaarMeasure l
    exact PyramidVolume.frame_pyramid_constant_pos (LinearFrame.continuousEquiv l v hv)

theorem realVolume_radialHull_exposed_sum {ι : Type*} [Fintype ι]
    (K : ι → ConvexBody E) (l : E →L[ℝ] ℝ) (v : E) (hv : l v = 1)
    (t : ι → ℝ) (ht : ∀ j, 0 < t j)
    (hh : 0 ≤ SupportGeometry.support (∑ j, t j • (K j : Set E)) l) :
    volume.real (PyramidVolume.radialHull (l.toExposed (∑ j, t j • (K j : Set E)))) =
      facetConstant l v hv * SupportGeometry.support (∑ j, t j • (K j : Set E)) l *
        (kernelMeasure l).real
          (↑(∑ j, t j • kernelBody (K j) l v hv) : Set (LinearMap.ker l.toLinearMap)) := by
  first
  | letI : MeasureSpace (LinearMap.ker l.toLinearMap) := ⟨kernelMeasure l⟩
    letI : IsAddHaarMeasure (volume : Measure (LinearMap.ker l.toLinearMap)) :=
      kernelMeasure_isAddHaarMeasure l
    have hc : IsCompact (∑ j, t j • (K j : Set E)) := by
      simpa only [coe_sum_body, ConvexBody.coe_smul] using (∑ j, t j • K j).isCompact
    have hn : (∑ j, t j • (K j : Set E)).Nonempty := by
      simpa only [coe_sum_body, ConvexBody.coe_smul] using (∑ j, t j • K j).nonempty
    have he : IsExposed ℝ (∑ j, t j • (K j : Set E))
        (l.toExposed (∑ j, t j • (K j : Set E))) := ContinuousLinearMap.toExposed.isExposed
    have hplane : ∀ x ∈ l.toExposed (∑ j, t j • (K j : Set E)),
        (LinearFrame.continuousEquiv l v hv x).1 =
          SupportGeometry.support (∑ j, t j • (K j : Set E)) l := by
      intro x hx
      rw [exposed_eq_support_level hc hn l] at hx
      exact hx.2
    have h := PyramidVolume.realVolume_radialHull_of_equiv
      (LinearFrame.continuousEquiv l v hv) (he.isCompact hc) hplane
    rw [image_exposed_positive_sum K l v hv t ht, abs_of_nonneg hh] at h
    rw [h]
    change ((_ : ℝ) * _ / _) * (kernelMeasure l).real _ = (_ / _) * _ * _
    ring

theorem FixedFacets.volume_decomposition [Nontrivial E]
    {ι : Type*} [Fintype ι] (K : ι → ConvexBody E)
    (D : FixedFacets (fun j => (K j : Set E)))
    (h0 : ∀ j, (0 : E) ∈ K j)
    (hint : (0 : E) ∈ interior (∑ j, (K j : Set E)))
    (v : Fin D.count → E) (hv : ∀ i, D.normal i (v i) = 1)
    (t : ι → ℝ) (ht : ∀ j, 0 < t j) :
    volume.real (↑(∑ j, t j • K j) : Set E) =
      ∑ i, facetConstant (D.normal i) (v i) (hv i) * D.height t i *
        (kernelMeasure (D.normal i)).real
          (↑(∑ j, t j • kernelBody (K j) (D.normal i) (v i) (hv i)) :
            Set (LinearMap.ker (D.normal i).toLinearMap)) := by
  first
  | have hheight : ∀ i, 0 < D.height t i :=
      D.height_pos (fun j => (K j).isCompact) h0 hint t ht
    have hbody := D.normalized_body t ht hheight
    have hc : IsCompact (HalfspacePyramids.body (D.normalized t)) := by
      rw [hbody]
      simpa only [coe_sum_body, ConvexBody.coe_smul] using (∑ j, t j • K j).isCompact
    rw [coe_sum_body]
    change volume.real (∑ j, t j • (K j : Set E)) = _
    rw [← hbody, HalfspacePyramids.realVolume_body_eq_sum_radialHull
      (D.normalized t) hc (D.normalized_injective t hheight)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [D.normalized_face (fun j => (K j).isCompact) (fun j => (K j).nonempty)
      t ht hheight i]
    have hh : 0 ≤ SupportGeometry.support (∑ j, t j • (K j : Set E)) (D.normal i) := by
      rw [← D.height_eq_support (fun j => (K j).isCompact) (fun j => (K j).nonempty) t ht i]
      exact (hheight i).le
    rw [realVolume_radialHull_exposed_sum K (D.normal i) (v i) (hv i) t ht hh,
      ← D.height_eq_support (fun j => (K j).isCompact) (fun j => (K j).nonempty) t ht i]

/-- The complete geometric data needed by induction on dimension. In
particular, the lower-dimensional bodies and their Haar measures are part of
the constructed data, and the identity concerns actual set volume. -/
structure CenteredDecomposition {n : ℕ} (K : Fin n → ConvexBody E) where
  count : ℕ
  kernel : Fin count → Submodule ℝ E
  lowerBody : ∀ i, Fin n → ConvexBody (kernel i)
  lowerMeasure : ∀ i, Measure (kernel i)
  lowerMeasure_haar : ∀ i, IsAddHaarMeasure (lowerMeasure i)
  lowerBody_finite : ∀ i j, IsFiniteHull (lowerBody i j : Set (kernel i))
  lower_finrank : ∀ i, finrank ℝ (kernel i) + 1 = finrank ℝ E
  constant : Fin count → ℝ
  constant_pos : ∀ i, 0 < constant i
  height : Fin count → Fin n → ℝ
  height_nonneg : ∀ i j, 0 ≤ height i j
  volume_identity : ∀ t : Fin n → ℝ, (∀ j, 0 < t j) →
    volume.real (↑(∑ j, t j • K j) : Set E) =
      ∑ i, constant i * (∑ j, t j * height i j) *
        (lowerMeasure i).real (↑(∑ j, t j • lowerBody i j) : Set (kernel i))

/-- Every centered full-dimensional finite-hull tuple has the exact inductive
volume decomposition, with no simplicity or general-position assumption. -/
theorem exists_centeredDecomposition [Nontrivial E] {n : ℕ}
    (K : Fin n → ConvexBody E) (hK : ∀ j, IsFiniteHull (K j : Set E))
    (h0 : ∀ j, (0 : E) ∈ K j)
    (hint : (0 : E) ∈ interior (∑ j, (K j : Set E))) :
    Nonempty (CenteredDecomposition K) := by
  first
  | classical
    obtain ⟨D⟩ := exists_fixedFacets (fun j => (K j : Set E)) hK
      (fun j => (K j).nonempty) ⟨0, hint⟩
    choose v hv using fun i => LinearFrame.exists_unit_value (D.normal i) (D.normal_ne_zero i)
    refine ⟨{
      count := D.count
      kernel := fun i => LinearMap.ker (D.normal i).toLinearMap
      lowerBody := fun i j => kernelBody (K j) (D.normal i) (v i) (hv i)
      lowerMeasure := fun i => kernelMeasure (D.normal i)
      lowerMeasure_haar := fun i => inferInstance
      lowerBody_finite := fun i j => kernelBody_isFiniteHull (K j) (hK j) _ _ _
      lower_finrank := fun i => LinearFrame.finrank_kernel_add_one (D.normal i) (v i) (hv i)
      constant := fun i => facetConstant (D.normal i) (v i) (hv i)
      constant_pos := fun i => facetConstant_pos (D.normal i) (v i) (hv i)
      height := D.heightCoefficient
      height_nonneg := D.heightCoefficient_nonneg (fun j => (K j).isCompact) h0
      volume_identity := fun t ht => D.volume_decomposition K h0 hint v hv t ht
    }⟩

end VolumePolynomials.PolytopeGeometry
