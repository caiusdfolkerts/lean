module

public import VolumePolynomials.PlanarMixedForm
public import VolumePolynomials.PlanarZonotope

@[expose] public section
set_option autoImplicit false

/-! # The universal planar corner inequality

This proves equation (4.6) for actual compact convex planar sets, including
degenerate sets. The proof uses the actual mixed-area form and coordinate
segment extrusion. The width-zero formal differences lie in a negative
orthogonal hyperplane, where ordinary Cauchy--Schwarz applies.
-/

noncomputable section
open Set MeasureTheory Module LinearMap
open scoped BigOperators Pointwise

namespace VolumePolynomials

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem bilinear_corner_inequality (B : LinearMap.BilinForm ℝ V)
    (hB : ∀ x y, B x y = B y x) (e : V)
    (hneg : ∀ x, B x e = 0 → B x x ≤ 0)
    (s t p q : V) (hss : B s s = 0) (htt : B t t = 0)
    (hst : 2 * B s t = 1) (w h w' h' : ℝ)
    (hps : 2 * B p s = h) (hpt : 2 * B p t = w)
    (hqs : 2 * B q s = h') (hqt : 2 * B q t = w') :
    2 * B p q ≥ w * h' + h * w' -
      2 * Real.sqrt ((w * h - B p p) * (w' * h' - B q q)) := by
  first
  | let r := s + t
    let x := w • s + h • t - p
    let y := w' • s + h' • t - q
    have hst' : B s t = 1 / 2 := by linarith
    have hps' : B p s = h / 2 := by linarith
    have hpt' : B p t = w / 2 := by linarith
    have hqs' : B q s = h' / 2 := by linarith
    have hqt' : B q t = w' / 2 := by linarith
    have hts : B t s = 1 / 2 := (hB t s).trans hst'
    have hsp : B s p = h / 2 := (hB s p).trans hps'
    have htp : B t p = w / 2 := (hB t p).trans hpt'
    have hsq : B s q = h' / 2 := (hB s q).trans hqs'
    have htq : B t q = w' / 2 := (hB t q).trans hqt'
    have hrr : B r r = 1 := by
      first
      | simp only [r, LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right, hss, htt, hst', hts]
        norm_num
    have hxr : B x r = 0 := by
      first
      | simp only [x, r, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
          LinearMap.BilinForm.smul_left, hss, htt, hst', hts, hps', hpt']
        ring
    have hyr : B y r = 0 := by
      first
      | simp only [y, r, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
          LinearMap.BilinForm.smul_left, hss, htt, hst', hts, hqs', hqt']
        ring
    have hxx : B x x = B p p - w * h := by
      first
      | simp only [x, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right, LinearMap.BilinForm.add_left,
          LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
          hss, htt, hst', hts, hsp, htp, hps', hpt']
        ring
    have hyy : B y y = B q q - w' * h' := by
      first
      | simp only [y, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right, LinearMap.BilinForm.add_left,
          LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
          hss, htt, hst', hts, hsq, htq, hqs', hqt']
        ring
    have hxy : B x y = B p q - (w * h' + h * w') / 2 := by
      first
      | simp only [x, y, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right, LinearMap.BilinForm.add_left,
          LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
          hss, htt, hst', hts, hsq, htq, hps', hpt']
        ring
    have hnegR : ∀ z, B z r = 0 → B z z ≤ 0 := fun z hz =>
      bilinear_nonpos_on_positive_orthogonal B hB e hneg (by rw [hrr]; norm_num) hz
    have hcs := bilinear_negative_cauchy_schwarz B hB r hnegR x y hxr hyr
    rw [hxx, hyy, hxy] at hcs
    have hcs' : (B p q - (w * h' + h * w') / 2) ^ 2 ≤
        (w * h - B p p) * (w' * h' - B q q) := by nlinarith
    have hsqrt := Real.sqrt_le_sqrt hcs'
    rw [Real.sqrt_sq_eq_abs] at hsqrt
    have hlo := (neg_le_neg hsqrt).trans
      (neg_abs_le (B p q - (w * h' + h * w') / 2))
    linarith

end VolumePolynomials

namespace VolumePolynomials.PlanarCorner

open PlanarExtrusion PlanarMixedForm

def segmentBody (v : Plane) : ConvexBody Plane where
  carrier := centeredSegment v
  convex' := centeredSegment_convex v
  isCompact' := centeredSegment_compact v
  nonempty' := ⟨0, zero_mem_centeredSegment v⟩

def unitX : ConvexBody Plane := segmentBody (1, 0)
def unitY : ConvexBody Plane := segmentBody (0, 1)

/-- Literal Lebesgue length of the horizontal projection. -/
def width (P : ConvexBody Plane) : ℝ := volume.real (Prod.fst '' (P : Set Plane))

/-- Literal Lebesgue length of the vertical projection. -/
def height (P : ConvexBody Plane) : ℝ := volume.real (Prod.snd '' (P : Set Plane))

theorem plane_finrank : finrank ℝ Plane = 2 := by simp [Plane]

theorem area_segmentBody (v : Plane) : volume.real (segmentBody v : Set Plane) = 0 := by
  first
  | change volume.real (centeredSegment v) = 0
    simpa only [zonotope_singleton, pairArea, List.map_nil,
      List.sum_nil, add_zero] using area_zonotope [v]

theorem twice_mixedArea_segment (P : ConvexBody Plane) (v : Plane) :
    2 * mixedArea volume P (segmentBody v) = volume.real (determinant v '' (P : Set Plane)) := by
  first
  | have h := area_add_centeredSegment P.isCompact P.convex v
    have hp := area_add volume plane_finrank P (segmentBody v)
    rw [area_segmentBody, add_zero] at hp
    change volume.real ((P + segmentBody v : ConvexBody Plane) : Set Plane) = _ at h
    linarith

theorem twice_mixedArea_unitX (P : ConvexBody Plane) :
    2 * mixedArea volume P unitX = height P := by
  first
  | have hd : determinant (1, 0) = Prod.snd := by
      funext x
      simp [determinant]
    rw [unitX, twice_mixedArea_segment, hd]
    rfl

theorem twice_mixedArea_unitY (P : ConvexBody Plane) :
    2 * mixedArea volume P unitY = width P := by
  first
  | rw [unitY, twice_mixedArea_segment]
    have himage : determinant (0, 1) '' (P : Set Plane) =
        (fun r : ℝ => (-1) * r) '' (Prod.fst '' (P : Set Plane)) := by
      first
      | rw [Set.image_image]
        congr 1
        funext x
        simp [determinant]
    rw [himage, length_image_mul]
    norm_num [width]

theorem twice_mixedArea_axes : 2 * mixedArea volume unitX unitY = 1 := by
  first
  | rw [mixedArea_symm, unitX, twice_mixedArea_segment]
    change volume.real (determinant (1, 0) '' centeredSegment (0, 1)) = 1
    rw [length_determinant_centeredSegment]
    norm_num [determinant]

/-- Equation (4.6), with no nondegeneracy, polygonality, or normalization
assumption. All areas and widths retain their ordinary geometric meanings. -/
theorem mixedArea_corner_inequality (P Q : ConvexBody Plane) :
    2 * mixedArea volume P Q ≥ width P * height Q + height P * width Q -
      2 * Real.sqrt ((width P * height P - volume.real (P : Set Plane)) *
        (width Q * height Q - volume.real (Q : Set Plane))) := by
  first
  | let K : Fin 4 → ConvexBody Plane := ![P, Q, unitX, unitY]
    let B := form volume K
    let p : Fin 4 → ℝ := Pi.single 0 1
    let q : Fin 4 → ℝ := Pi.single 1 1
    let s : Fin 4 → ℝ := Pi.single 2 1
    let t : Fin 4 → ℝ := Pi.single 3 1
    have hK0 : K 0 = P := rfl
    have hK1 : K 1 = Q := rfl
    have hK2 : K 2 = unitX := rfl
    have hK3 : K 3 = unitY := rfl
    have hentry : 0 < mixedArea volume (K 2) (K 3) := by
      first
      | change 0 < mixedArea volume unitX unitY
        linarith [twice_mixedArea_axes]
    have hpositive := form_one_positive_of_entry volume K 2 3 hentry
    have hneg : ∀ x, B x (fun _ => 1) = 0 → B x x ≤ 0 :=
      form_nonpositive_on_orthogonal volume plane_finrank K hpositive
    have hss : B s s = 0 := by
      first
      | simp only [B, s, form_single, hK2]
        rw [mixedArea_diagonal volume plane_finrank, unitX, area_segmentBody]
    have htt : B t t = 0 := by
      first
      | simp only [B, t, form_single, hK3]
        rw [mixedArea_diagonal volume plane_finrank, unitY, area_segmentBody]
    have hst : 2 * B s t = 1 := by
      first
      | simpa only [B, s, t, form_single, hK2, hK3]
          using twice_mixedArea_axes
    have hps : 2 * B p s = height P := by
      first
      | simpa only [B, p, s, form_single, hK0, hK2]
          using twice_mixedArea_unitX P
    have hpt : 2 * B p t = width P := by
      first
      | simpa only [B, p, t, form_single, hK0, hK3]
          using twice_mixedArea_unitY P
    have hqs : 2 * B q s = height Q := by
      first
      | simpa only [B, q, s, form_single, hK1, hK2]
          using twice_mixedArea_unitX Q
    have hqt : 2 * B q t = width Q := by
      first
      | simpa only [B, q, t, form_single, hK1, hK3]
          using twice_mixedArea_unitY Q
    have h := bilinear_corner_inequality B (form_symmetric volume K) (fun _ => 1)
      hneg s t p q hss htt hst (width P) (height P) (width Q) (height Q) hps hpt hqs hqt
    simpa only [B, p, q, form_single, hK0, hK1,
      mixedArea_diagonal volume plane_finrank] using h

end VolumePolynomials.PlanarCorner
