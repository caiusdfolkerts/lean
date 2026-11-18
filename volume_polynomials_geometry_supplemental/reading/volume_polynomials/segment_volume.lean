module
public import VolumePolynomials.BodyFrames
public import VolumePolynomials.LinearFrame
public import VolumePolynomials.ExtrusionTransport
public import Mathlib.Tactic.Positivity

@[expose] public section
noncomputable section

/-!
# Affine dependence of volume on a segment summand

The interval-fiber extrusion theorem gives affine dependence on every
nonnegative segment length in every ambient dimension. The coordinate frame
is constructed from a nonzero coordinate of the segment vector. Uniqueness of
Haar measure supplies its proved volume factor, which cancels from the final
identity. Translated and degenerate segments are included.
-/

open Set MeasureTheory
open scoped Pointwise

namespace VolumePolynomials

theorem smul_segment_zero_eq_parameter_image {d : ℕ} (v : Space d) {r : ℝ}
    (hr : 0 ≤ r) :
    r • segment ℝ 0 v = (fun s : ℝ => s • v) '' Icc 0 r := by
  rw [segment_eq_image]
  simp only [smul_zero, zero_add]
  rw [← Set.image_smul, Set.image_image]
  have hf : (fun s : ℝ => r • (s • v)) =
      (fun s : ℝ => s • v) ∘ (fun s : ℝ => s * r) := by
    funext s
    simp only [Function.comp_apply, smul_smul, mul_comm]
  rw [hf, Set.image_comp, image_mul_right_Icc zero_le_one hr]
  simp only [zero_mul, one_mul]

theorem realVolume_add_segment_parameter_affine {d : ℕ}
    {C : Set (Space d)} (hC : IsCompact C) (hc : Convex ℝ C) (v : Space d)
    {r : ℝ} (hr : 0 ≤ r) :
    volume.real (C + (fun s : ℝ => s • v) '' Icc 0 r) =
      volume.real C + r *
        (volume.real (C + (fun s : ℝ => s • v) '' Icc 0 1) - volume.real C) := by
  by_cases hv0 : v = 0
  · subst v
    have hne : (Icc (0 : ℝ) r).Nonempty := ⟨0, le_rfl, hr⟩
    have hne1 : (Icc (0 : ℝ) 1).Nonempty := ⟨0, le_rfl, zero_le_one⟩
    simp only [smul_zero, hne.image_const (0 : Space d), hne1.image_const (0 : Space d),
      Set.add_singleton, add_zero, Set.image_id', sub_self, mul_zero, add_zero]
  · obtain ⟨i, hi⟩ : ∃ i : Fin d, v i ≠ 0 := by
      by_contra h
      apply hv0
      funext i
      exact not_not.mp (fun hi => h ⟨i, hi⟩)
    let l : Space d →L[ℝ] ℝ := (v i)⁻¹ • ContinuousLinearMap.proj i
    have hlv : l v = 1 := by simp [l, hi]
    let E := LinearMap.ker l.toLinearMap
    letI : MeasureSpace E := ⟨Measure.addHaar⟩
    letI : Measure.IsAddHaarMeasure (volume : Measure E) := by
      change Measure.IsAddHaarMeasure (Measure.addHaar : Measure E)
      infer_instance
    let T : Space d ≃L[ℝ] ℝ × E := LinearFrame.continuousEquiv l v hlv
    have hTv : T v = (1, 0) := by
      apply Prod.ext
      · exact hlv
      · apply Subtype.ext
        change v - l v • v = 0
        simp only [hlv, one_smul, sub_self]
    let J : ℝ := LinearFrame.volumeFactor T
    let A : ℝ := volume.real (T '' C)
    let B : ℝ := volume.real (PlanarExtrusion.projection (T '' C))
    have hformula (t : ℝ) (ht : 0 ≤ t) :
        volume.real (C + (fun s : ℝ => s • v) '' Icc 0 t) = J * (A + t * B) := by
      rw [LinearFrame.realVolume_eq_factor_mul_image T,
        Set.image_add T, ProductExtrusion.image_origin_segment T hTv]
      rw [PlanarExtrusion.realVolume_add_horizontal (hC.image T.continuous)
        (hc.linear_image T.toLinearMap) ht]
    have hbase : volume.real C = J * A :=
      LinearFrame.realVolume_eq_factor_mul_image T C
    rw [hformula r hr, hformula 1 zero_le_one, hbase]
    ring

theorem bodyVolume_add_smul_originSegment {d : ℕ} (L : Body d) (v : Space d)
    {r : ℝ} (hr : 0 ≤ r) :
    bodyVolume (L + r • segmentBody 0 v) = bodyVolume L + r *
      (bodyVolume (L + segmentBody 0 v) - bodyVolume L) := by
  change volume.real ((L : Set (Space d)) + r • segment ℝ 0 v) = _
  rw [smul_segment_zero_eq_parameter_image v hr]
  have h := realVolume_add_segment_parameter_affine L.isCompact L.convex v hr
  have hone : segment ℝ (0 : Space d) v = (fun s : ℝ => s • v) '' Icc 0 1 := by
    simp only [segment_eq_image, smul_zero, zero_add]
  simpa only [bodyVolume, ConvexBody.coe_add, coe_segmentBody, hone] using h

/-- No centering, nondegeneracy or full-dimensionality hypothesis is needed. -/
theorem bodyVolume_add_smul_segment {d : ℕ} (L : Body d) (a b : Space d)
    {r : ℝ} (hr : 0 ≤ r) :
    bodyVolume (L + r • segmentBody a b) = bodyVolume L + r *
      (bodyVolume (L + segmentBody a b) - bodyVolume L) := by
  have hseg : segmentBody a b = translateBody a (segmentBody 0 (b - a)) := by
    rw [translate_segmentBody]
    congr 1 <;> abel
  have htranslate (t : ℝ) :
      L + t • translateBody a (segmentBody 0 (b - a)) =
        translateBody (t • a) (L + t • segmentBody 0 (b - a)) := by
    simp only [translateBody, smul_add, ← pointBody_smul]
    ac_rfl
  rw [hseg, htranslate, bodyVolume_translate]
  have hone : L + translateBody a (segmentBody 0 (b - a)) =
      translateBody a (L + segmentBody 0 (b - a)) := by
    simpa only [one_smul] using htranslate 1
  rw [hone, bodyVolume_translate]
  exact bodyVolume_add_smul_originSegment L (b - a) hr

theorem bodyVolume_segment_second_difference {d : ℕ} (K L : Body d)
    (hK : ∃ a b : Space d, (K : Set (Space d)) = segment ℝ a b) :
    bodyVolume (L + (2 : ℝ) • K) - 2 * bodyVolume (L + K) + bodyVolume L = 0 := by
  obtain ⟨a, b, hK⟩ := hK
  have hbody := body_eq_segmentBody hK
  rw [hbody, bodyVolume_add_smul_segment L a b (by norm_num)]
  ring

end VolumePolynomials
