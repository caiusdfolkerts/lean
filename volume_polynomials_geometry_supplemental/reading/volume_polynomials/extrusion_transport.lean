module

public import VolumePolynomials.PlanarExtrusion
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Extrusion in volume-preserving product coordinates

This transports the interval-fiber theorem across an actual continuous linear
equivalence preserving the specified measures. It is suitable for the rational
quotient coordinates in Section 7. No relation between a coordinate determinant
and two differently represented spaces is left implicit.
-/

noncomputable section
open Set MeasureTheory
open scoped Pointwise

namespace VolumePolynomials.ProductExtrusion

open PlanarExtrusion

variable {F E : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasureSpace F] [BorelSpace F]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E]
  [SecondCountableTopology E] [IsLocallyFiniteMeasure (volume : Measure E)]

theorem realVolume_image_of_measurePreserving
    (T : F ≃L[ℝ] (ℝ × E)) (hT : MeasurePreserving T volume volume) (S : Set F) :
    volume.real (T '' S) = volume.real S := by
  have h := hT.measure_preimage_emb T.toHomeomorph.measurableEmbedding (T '' S)
  rw [Set.preimage_image_eq S T.injective] at h
  exact congrArg ENNReal.toReal h.symm

theorem image_origin_segment (T : F ≃L[ℝ] (ℝ × E)) {v : F}
    (hv : T v = (1, 0)) (t : ℝ) :
    T '' ((fun s : ℝ => s • v) '' Icc 0 t) = horizontal t := by
  rw [Set.image_image]
  ext p
  constructor
  · rintro ⟨s, hs, hsp⟩
    have heq : (s, (0 : E)) = p := by
      simpa only [Function.comp_apply, map_smul, hv, Prod.smul_mk,
        smul_eq_mul, mul_one, smul_zero] using hsp
    rw [← heq]
    exact ⟨hs, rfl⟩
  · rintro ⟨hp, hp0⟩
    refine ⟨p.1, hp, ?_⟩
    change p.2 = 0 at hp0
    simp only [Function.comp_apply, map_smul, hv, Prod.smul_mk,
      smul_eq_mul, mul_one, smul_zero]
    exact Prod.ext rfl hp0.symm

theorem image_origin_segment_nonneg (T : F ≃L[ℝ] (ℝ × E)) {v : F} {c : ℝ}
    (hv : T v = (c, 0)) (hc : 0 ≤ c) {t : ℝ} (ht : 0 ≤ t) :
    T '' ((fun s : ℝ => s • v) '' Icc 0 t) = horizontal (t * c) := by
  have himage : T '' ((fun s : ℝ => s • v) '' Icc 0 t) =
      (fun a : ℝ => (a, (0 : E))) '' ((fun s : ℝ => s * c) '' Icc 0 t) := by
    rw [Set.image_image, Set.image_image]
    congr 1
    funext s
    simp only [Function.comp_apply, map_smul, hv, Prod.smul_mk,
      smul_eq_mul, smul_zero]
  rw [himage, image_mul_right_Icc ht hc]
  simp only [zero_mul]
  ext ⟨x, y⟩
  constructor
  · rintro ⟨s, hs, heq⟩
    rw [← heq]
    exact ⟨hs, rfl⟩
  · rintro ⟨hx, hy⟩
    change y = 0 at hy
    subst y
    exact ⟨x, hx, rfl⟩

/-- The axial component may have any nonnegative length. -/
theorem realVolume_add_origin_segment_nonneg
    (T : F ≃L[ℝ] (ℝ × E)) (hT : MeasurePreserving T volume volume)
    {C : Set F} (hC : IsCompact C) (hc : Convex ℝ C) {v : F} {c : ℝ}
    (hv : T v = (c, 0)) (hc0 : 0 ≤ c) {t : ℝ} (ht : 0 ≤ t) :
    volume.real (C + (fun s : ℝ => s • v) '' Icc 0 t) =
      volume.real C + (t * c) * volume.real (projection (T '' C)) := by
  calc
    volume.real (C + (fun s : ℝ => s • v) '' Icc 0 t) =
        volume.real (T '' (C + (fun s : ℝ => s • v) '' Icc 0 t)) :=
      (realVolume_image_of_measurePreserving T hT _).symm
    _ = volume.real (T '' C + horizontal (t * c)) := by
      rw [Set.image_add T, image_origin_segment_nonneg T hv hc0 ht]
    _ = volume.real (T '' C) + (t * c) * volume.real (projection (T '' C)) :=
      realVolume_add_horizontal (hC.image T.continuous) (hc.linear_image T.toLinearMap)
        (mul_nonneg ht hc0)
    _ = volume.real C + (t * c) * volume.real (projection (T '' C)) := by
      rw [realVolume_image_of_measurePreserving T hT]

/-- Extrusion by an arbitrary nonnegative interval in a volume-preserving frame. -/
theorem realVolume_add_origin_segment
    (T : F ≃L[ℝ] (ℝ × E)) (hT : MeasurePreserving T volume volume)
    {C : Set F} (hC : IsCompact C) (hc : Convex ℝ C) {v : F}
    (hv : T v = (1, 0)) {t : ℝ} (ht : 0 ≤ t) :
    volume.real (C + (fun s : ℝ => s • v) '' Icc 0 t) =
      volume.real C + t * volume.real (projection (T '' C)) := by
  calc
    volume.real (C + (fun s : ℝ => s • v) '' Icc 0 t) =
        volume.real (T '' (C + (fun s : ℝ => s • v) '' Icc 0 t)) :=
      (realVolume_image_of_measurePreserving T hT _).symm
    _ = volume.real (T '' C + horizontal t) := by
      rw [Set.image_add T, image_origin_segment T hv]
    _ = volume.real (T '' C) + t * volume.real (projection (T '' C)) :=
      realVolume_add_horizontal (hC.image T.continuous) (hc.linear_image T.toLinearMap) ht
    _ = volume.real C + t * volume.real (projection (T '' C)) := by
      rw [realVolume_image_of_measurePreserving T hT]

theorem centered_segment_eq_singleton_add_origin (v : F) :
    (fun s : ℝ => s • v) '' Icc (-(1 / 2 : ℝ)) (1 / 2) =
      {(-(1 / 2 : ℝ)) • v} + (fun s : ℝ => s • v) '' Icc 0 1 := by
  ext x
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨(-(1 / 2 : ℝ)) • v, rfl, (s + 1 / 2) • v, ?_, ?_⟩
    · exact ⟨s + 1 / 2, ⟨by linarith [hs.1], by linarith [hs.2]⟩, rfl⟩
    · change (-(1 / 2 : ℝ)) • v + (s + 1 / 2) • v = s • v
      rw [← add_smul]
      congr 1
      ring
  · rintro ⟨a, ha, b, ⟨s, hs, rfl⟩, rfl⟩
    change a = (-(1 / 2 : ℝ)) • v at ha
    subst a
    refine ⟨s - 1 / 2, ⟨by linarith [hs.1], by linarith [hs.2]⟩, ?_⟩
    change (s - 1 / 2) • v = (-(1 / 2 : ℝ)) • v + s • v
    rw [← add_smul]
    congr 1
    ring

theorem realVolume_add_centered_segment_nonneg
    [Measure.IsAddLeftInvariant (volume : Measure F)]
    (T : F ≃L[ℝ] (ℝ × E)) (hT : MeasurePreserving T volume volume)
    {C : Set F} (hC : IsCompact C) (hc : Convex ℝ C) {v : F} {c : ℝ}
    (hv : T v = (c, 0)) (hc0 : 0 ≤ c) :
    volume.real (C + (fun s : ℝ => s • v) '' Icc (-(1 / 2 : ℝ)) (1 / 2)) =
      volume.real C + c * volume.real (projection (T '' C)) := by
  rw [centered_segment_eq_singleton_add_origin, ← add_assoc, add_comm C, add_assoc]
  rw [Set.singleton_add]
  simp only [measureReal_def, Set.image_add_left, measure_preimage_add]
  simpa only [one_mul, measureReal_def] using
    realVolume_add_origin_segment_nonneg T hT hC hc hv hc0 (by norm_num : (0 : ℝ) ≤ 1)

/-- The centered-segment form used for the three quotient projections in Section 7. -/
theorem realVolume_add_centered_segment
    [Measure.IsAddLeftInvariant (volume : Measure F)]
    (T : F ≃L[ℝ] (ℝ × E)) (hT : MeasurePreserving T volume volume)
    {C : Set F} (hC : IsCompact C) (hc : Convex ℝ C) {v : F}
    (hv : T v = (1, 0)) :
    volume.real (C + (fun s : ℝ => s • v) '' Icc (-(1 / 2 : ℝ)) (1 / 2)) =
      volume.real C + volume.real (projection (T '' C)) := by
  rw [centered_segment_eq_singleton_add_origin, ← add_assoc, add_comm C, add_assoc]
  rw [Set.singleton_add]
  simp only [measureReal_def, Set.image_add_left, measure_preimage_add]
  simpa only [one_mul, measureReal_def] using
    realVolume_add_origin_segment T hT hC hc hv (by norm_num : (0 : ℝ) ≤ 1)

end VolumePolynomials.ProductExtrusion
