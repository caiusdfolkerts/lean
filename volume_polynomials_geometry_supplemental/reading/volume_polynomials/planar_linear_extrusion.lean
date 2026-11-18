module

public import VolumePolynomials.PlanarExtrusion
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.LinearAlgebra.Basis.Fin
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Abel

@[expose] public section

/-!
# Extrusion in an arbitrary planar direction

The determinant-coordinate version avoids normalization by the Euclidean
length of the direction. The area increment is the one-dimensional Lebesgue
measure of the image under `x ↦ det(v,x)`. It follows from the horizontal
fiber theorem by a determinant-one linear change of coordinates.
-/

noncomputable section
open Set MeasureTheory Module
open scoped Pointwise ENNReal

namespace VolumePolynomials.PlanarExtrusion

abbrev Plane := ℝ × ℝ

instance plane_volume_isAddHaarMeasure : Measure.IsAddHaarMeasure (volume : Measure Plane) := by
  rw [Measure.volume_eq_prod]
  infer_instance

/-- The standard oriented planar determinant. -/
def determinant (v x : Plane) : ℝ := v.1 * x.2 - v.2 * x.1

/-- The closed segment from the origin to `v`. -/
def originSegment (v : Plane) : Set Plane := (fun s : ℝ => s • v) '' Icc 0 1

/-- The length-one centered parameter interval in direction `v`. -/
def centeredSegment (v : Plane) : Set Plane :=
  (fun s : ℝ => s • v) '' Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)

/-- The linear map with columns `v` and `w`. -/
def frameMap (v w : Plane) : Plane →ₗ[ℝ] Plane where
  toFun p := p.1 • v + p.2 • w
  map_add' := by
    intro x y
    simp only [Prod.fst_add, Prod.snd_add, add_smul]
    abel
  map_smul' := by
    intro a x
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_smul, smul_add,
      RingHom.id_apply]

theorem frameMap_det (v w : Plane) : LinearMap.det (frameMap v w) = determinant v w := by
  rw [← LinearMap.det_toMatrix (Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Basis.coe_finTwoProd_repr, frameMap, determinant, mul_comm]

theorem exists_unit_frame {v : Plane} (hv : v ≠ 0) :
    ∃ w : Plane, determinant v w = 1 := by
  by_cases h : v.1 = 0
  · have h₂ : v.2 ≠ 0 := by
      intro hz
      apply hv
      exact Prod.ext h hz
    refine ⟨(-(v.2)⁻¹, 0), ?_⟩
    simp [determinant, h, h₂]
  · refine ⟨(0, (v.1)⁻¹), ?_⟩
    simp [determinant, h]

/-- A determinant-one frame is an actual linear equivalence. -/
def frameEquiv (v w : Plane) (hw : determinant v w = 1) : Plane ≃ₗ[ℝ] Plane :=
  (frameMap v w).equivOfDetNeZero (by rw [frameMap_det, hw]; exact one_ne_zero)

@[simp] theorem frameEquiv_apply (v w : Plane) (hw : determinant v w = 1) (x : Plane) :
    frameEquiv v w hw x = x.1 • v + x.2 • w := rfl

theorem frameEquiv_det (v w : Plane) (hw : determinant v w = 1) :
    LinearMap.det (frameEquiv v w hw : Plane →ₗ[ℝ] Plane) = 1 := by
  change LinearMap.det (frameMap v w) = 1
  rw [frameMap_det, hw]

theorem determinant_frame (v w : Plane) (hw : determinant v w = 1) (x : Plane) :
    determinant v (frameEquiv v w hw x) = x.2 := by
  rw [frameEquiv_apply]
  have h : determinant v (x.1 • v + x.2 • w) = x.2 * determinant v w := by
    simp only [determinant, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add,
      smul_eq_mul]
    ring
  rw [h, hw, mul_one]

theorem inverse_frame_snd (v w : Plane) (hw : determinant v w = 1) (x : Plane) :
    ((frameEquiv v w hw).symm x).2 = determinant v x := by
  simpa only [LinearEquiv.apply_symm_apply] using
    (determinant_frame v w hw ((frameEquiv v w hw).symm x)).symm

theorem frame_image_horizontal (v w : Plane) (hw : determinant v w = 1) :
    frameEquiv v w hw '' horizontal 1 = originSegment v := by
  ext x
  constructor
  · rintro ⟨⟨s, z⟩, ⟨hs, hz⟩, rfl⟩
    change z = 0 at hz
    subst z
    refine ⟨s, hs, ?_⟩
    simp
  · rintro ⟨s, hs, rfl⟩
    refine ⟨(s, 0), ⟨hs, rfl⟩, ?_⟩
    simp

theorem area_image_linear (f : Plane →ₗ[ℝ] Plane) (C : Set Plane) :
    volume.real (f '' C) = |LinearMap.det f| * volume.real C := by
  simp only [measureReal_def]
  rw [Measure.addHaar_image_linearMap volume f C, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _)]

/-- Transport of the horizontal extrusion theorem by a determinant-one map. -/
theorem area_add_linear_horizontal
    {C : Set Plane} (hC : IsCompact C) (hc : Convex ℝ C)
    (e : Plane ≃ₗ[ℝ] Plane) (he : LinearMap.det (e : Plane →ₗ[ℝ] Plane) = 1)
    {t : ℝ} (ht : 0 ≤ t) :
    volume.real (C + e '' horizontal t) =
      volume.real C + t * volume.real (projection (e.symm '' C)) := by
  let D : Set Plane := e.symm '' C
  have hD : IsCompact D := hC.image e.symm.toContinuousLinearEquiv.continuous
  have hcD : Convex ℝ D := hc.linear_image (e.symm : Plane →ₗ[ℝ] Plane)
  have hDC : e '' D = C := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, hzx⟩
      have hz' : z = x := by simpa only [LinearEquiv.apply_symm_apply] using hzx
      exact hz' ▸ hz
    · intro hx
      exact ⟨e.symm x, ⟨x, hx, rfl⟩, e.apply_symm_apply x⟩
  have hsum : e '' (D + horizontal t) = C + e '' horizontal t := by
    rw [Set.image_add e, hDC]
  have harea : ∀ S : Set Plane, volume.real (e '' S) = volume.real S := by
    intro S
    simpa [he] using area_image_linear (e : Plane →ₗ[ℝ] Plane) S
  calc
    volume.real (C + e '' horizontal t) = volume.real (D + horizontal t) := by
      rw [← hsum, harea]
    _ = volume.real D + t * volume.real (projection D) := area_add_horizontal hD hcD ht
    _ = volume.real C + t * volume.real (projection D) := by
      rw [← harea D, hDC]

/-- Arbitrary-direction planar extrusion, including the zero direction. -/
theorem area_add_originSegment {C : Set Plane} (hC : IsCompact C) (hc : Convex ℝ C)
    (v : Plane) :
    volume.real (C + originSegment v) =
      volume.real C + volume.real (determinant v '' C) := by
  by_cases hv : v = 0
  · subst v
    have hseg : originSegment (0 : Plane) = {0} := by
      simp [originSegment]
    have hproj : volume.real (determinant (0 : Plane) '' C) = 0 := by
      have hsub : determinant (0 : Plane) '' C ⊆ {0} := by
        rintro x ⟨y, hy, rfl⟩
        simp [determinant]
      have hm : volume (determinant (0 : Plane) '' C) = 0 :=
        measure_mono_null hsub (measure_singleton 0)
      simp [measureReal_def, hm]
    simp [hseg, hproj, Set.singleton_zero]
  · obtain ⟨w, hw⟩ := exists_unit_frame hv
    have hproj : projection ((frameEquiv v w hw).symm '' C) = determinant v '' C := by
      rw [projection, Set.image_image]
      congr 1
      funext x
      exact inverse_frame_snd v w hw x
    have h := area_add_linear_horizontal hC hc (frameEquiv v w hw)
      (frameEquiv_det v w hw) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [frame_image_horizontal, hproj, one_mul] using h

theorem centeredSegment_eq_translate (v : Plane) :
    centeredSegment v = {(-(1 / 2 : ℝ)) • v} + originSegment v := by
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

/-- Centering a segment changes no area; this is the zonotope-ready form. -/
theorem area_add_centeredSegment {C : Set Plane} (hC : IsCompact C) (hc : Convex ℝ C)
    (v : Plane) :
    volume.real (C + centeredSegment v) =
      volume.real C + volume.real (determinant v '' C) := by
  rw [centeredSegment_eq_translate, ← add_assoc, add_comm C, add_assoc]
  rw [Set.singleton_add]
  simp only [measureReal_def, Set.image_add_left, measure_preimage_add]
  simpa only [measureReal_def] using area_add_originSegment hC hc v

end VolumePolynomials.PlanarExtrusion
