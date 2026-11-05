module

public import VolumePolynomials.PlanarCornerInequality
public import VolumePolynomials.FinitePolytope
public import Mathlib.Tactic.FieldSimp

@[expose] public section
set_option autoImplicit false

/-! # The actual optimizer in equation (4.15)

The body is a Minkowski sum of the specified planar body and two coordinate
segments. Its projection widths, Lebesgue area and mixed area are computed
exactly. No corner-measure representation is assumed.
-/

noncomputable section
open Set MeasureTheory Module
open scoped Pointwise

namespace VolumePolynomials.PlanarCorner

open PlanarExtrusion PlanarMixedForm

theorem unit_width_lower_bound (A Q : ConvexBody Plane) {s a q : ℝ}
    (hAw : width A = 1) (hAh : height A = s) (hAa : volume.real (A : Set Plane) = a)
    (hQw : width Q = 1) (hQh : height Q = 1) (hQa : volume.real (Q : Set Plane) = q) :
    2 * mixedArea volume A Q ≥ 1 + s - 2 * Real.sqrt ((s - a) * (1 - q)) := by
  first
  | simpa only [hAw, hAh, hAa, hQw, hQh, hQa, one_mul, mul_one] using
      mixedArea_corner_inequality A Q

theorem width_add (A B : ConvexBody Plane) : width (A + B) = width A + width B := by
  first
  | have h := twice_mixedArea_unitY (A + B)
    rw [mixedArea_add_left] at h
    linarith [twice_mixedArea_unitY A, twice_mixedArea_unitY B]

theorem height_add (A B : ConvexBody Plane) : height (A + B) = height A + height B := by
  first
  | have h := twice_mixedArea_unitX (A + B)
    rw [mixedArea_add_left] at h
    linarith [twice_mixedArea_unitX A, twice_mixedArea_unitX B]

theorem width_smul (A : ConvexBody Plane) {r : ℝ} (hr : 0 ≤ r) :
    width (r • A) = r * width A := by
  first
  | have h := twice_mixedArea_unitY (r • A)
    rw [mixedArea_smul_left volume _ _ hr] at h
    nlinarith [twice_mixedArea_unitY A]

theorem height_smul (A : ConvexBody Plane) {r : ℝ} (hr : 0 ≤ r) :
    height (r • A) = r * height A := by
  first
  | have h := twice_mixedArea_unitX (r • A)
    rw [mixedArea_smul_left volume _ _ hr] at h
    nlinarith [twice_mixedArea_unitX A]

theorem width_translate (P : ConvexBody Plane) (v : Plane) :
    width (translateBody v P) = width P := by
  first
  | have h := mixedArea_translate_right volume unitY P v
    rw [mixedArea_symm volume unitY, mixedArea_symm volume unitY] at h
    linarith [twice_mixedArea_unitY (translateBody v P), twice_mixedArea_unitY P]

theorem height_translate (P : ConvexBody Plane) (v : Plane) :
    height (translateBody v P) = height P := by
  first
  | have h := mixedArea_translate_right volume unitX P v
    rw [mixedArea_symm volume unitX, mixedArea_symm volume unitX] at h
    linarith [twice_mixedArea_unitX (translateBody v P), twice_mixedArea_unitX P]

@[simp] theorem width_unitX : width unitX = 1 := by
  first
  | rw [← twice_mixedArea_unitY, twice_mixedArea_axes]

@[simp] theorem height_unitY : height unitY = 1 := by
  first
  | rw [← twice_mixedArea_unitX, mixedArea_symm, twice_mixedArea_axes]

@[simp] theorem width_unitY : width unitY = 0 := by
  first
  | rw [← twice_mixedArea_unitY, mixedArea_diagonal volume plane_finrank,
      unitY, area_segmentBody, mul_zero]

@[simp] theorem height_unitX : height unitX = 0 := by
  first
  | rw [← twice_mixedArea_unitX, mixedArea_diagonal volume plane_finrank,
      unitX, area_segmentBody, mul_zero]

theorem area_smul (A : ConvexBody Plane) {r : ℝ} (hr : 0 ≤ r) :
    volume.real ((r • A : ConvexBody Plane) : Set Plane) = r ^ 2 * volume.real (A : Set Plane) := by
  first
  | simpa only [plane_finrank] using haar_real_smul_body volume A hr

theorem area_add_scaled_unitX (A : ConvexBody Plane) {r : ℝ} (hr : 0 ≤ r) :
    volume.real ((A + r • unitX : ConvexBody Plane) : Set Plane) =
      volume.real (A : Set Plane) + r * height A := by
  first
  | rw [area_add volume plane_finrank, mixedArea_smul_right volume _ _ hr,
      area_smul _ hr, unitX, area_segmentBody, mul_zero, add_zero]
    have h := twice_mixedArea_unitX A
    change 2 * mixedArea volume A (segmentBody (1, 0)) = height A at h
    nlinarith

theorem area_add_scaled_unitY (A : ConvexBody Plane) {r : ℝ} (hr : 0 ≤ r) :
    volume.real ((A + r • unitY : ConvexBody Plane) : Set Plane) =
      volume.real (A : Set Plane) + r * width A := by
  first
  | rw [area_add volume plane_finrank, mixedArea_smul_right volume _ _ hr,
      area_smul _ hr, unitY, area_segmentBody, mul_zero, add_zero]
    have h := twice_mixedArea_unitY A
    change 2 * mixedArea volume A (segmentBody (0, 1)) = width A at h
    nlinarith

def optimizerBody (Q : ConvexBody Plane) (s lam : ℝ) : ConvexBody Plane :=
  lam • Q + (1 - lam) • unitX + (s - lam) • unitY

theorem segmentBody_finiteHull (v : Plane) :
    PolytopeGeometry.IsFiniteHull (segmentBody v : Set Plane) := by
  first
  | have hI : PolytopeGeometry.IsFiniteHull (Icc (-(1 / 2 : ℝ)) (1 / 2)) := by
      first
      | refine ⟨{-(1 / 2 : ℝ), 1 / 2}, (Set.finite_singleton _).insert _, ?_⟩
        rw [convexHull_pair, segment_eq_Icc (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2)]
    exact hI.linear_image (LinearMap.toSpanSingleton ℝ Plane v)

theorem optimizerBody_finiteHull (Q : ConvexBody Plane) (s lam : ℝ)
    (hQ : PolytopeGeometry.IsFiniteHull (Q : Set Plane)) :
    PolytopeGeometry.IsFiniteHull (optimizerBody Q s lam : Set Plane) :=
  ((hQ.smul lam).add ((segmentBody_finiteHull (1, 0)).smul (1 - lam))).add
    ((segmentBody_finiteHull (0, 1)).smul (s - lam))

theorem optimizerBody_widths (Q : ConvexBody Plane) {s lam : ℝ}
    (hQw : width Q = 1) (hQh : height Q = 1)
    (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1) (hlams : lam ≤ s) :
    width (optimizerBody Q s lam) = 1 ∧ height (optimizerBody Q s lam) = s := by
  first
  | have ha : 0 ≤ 1 - lam := sub_nonneg.mpr hlam1
    have hb : 0 ≤ s - lam := sub_nonneg.mpr hlams
    simp only [optimizerBody, width_add, height_add, width_smul _ hlam,
      width_smul _ ha, width_smul _ hb, height_smul _ hlam, height_smul _ ha,
      height_smul _ hb, width_unitX, width_unitY, height_unitX, height_unitY, hQw, hQh]
    constructor <;> ring

theorem optimizerBody_area (Q : ConvexBody Plane) {s lam : ℝ}
    (hQw : width Q = 1) (hQh : height Q = 1)
    (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1) (hlams : lam ≤ s) :
    volume.real (optimizerBody Q s lam : Set Plane) =
      s - lam ^ 2 * (1 - volume.real (Q : Set Plane)) := by
  first
  | have ha : 0 ≤ 1 - lam := sub_nonneg.mpr hlam1
    have hb : 0 ≤ s - lam := sub_nonneg.mpr hlams
    rw [optimizerBody, area_add_scaled_unitY _ hb, area_add_scaled_unitX _ ha,
      area_smul _ hlam, height_smul _ hlam, width_add,
      width_smul _ hlam, width_smul _ ha, width_unitX, hQw, hQh]
    ring

theorem optimizerBody_mixedArea (Q : ConvexBody Plane) {s lam : ℝ}
    (hQw : width Q = 1) (hQh : height Q = 1)
    (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1) (hlams : lam ≤ s) :
    2 * mixedArea volume (optimizerBody Q s lam) Q =
      1 + s - 2 * lam * (1 - volume.real (Q : Set Plane)) := by
  first
  | have ha : 0 ≤ 1 - lam := sub_nonneg.mpr hlam1
    have hb : 0 ≤ s - lam := sub_nonneg.mpr hlams
    have hx : 2 * mixedArea volume unitX Q = 1 := by
      first
      | rw [mixedArea_symm, twice_mixedArea_unitX, hQh]
    have hy : 2 * mixedArea volume unitY Q = 1 := by
      first
      | rw [mixedArea_symm, twice_mixedArea_unitY, hQw]
    rw [optimizerBody, mixedArea_add_left, mixedArea_add_left,
      mixedArea_smul_left volume _ _ hlam, mixedArea_smul_left volume _ _ ha,
      mixedArea_smul_left volume _ _ hb, mixedArea_diagonal volume plane_finrank]
    nlinarith

/-- The geometric content of Lemma4.4 after the interaction body is known:
its lower bound holds for every actual A, and the stated body attains it whenever
the square-root scale fits both requested widths. -/
theorem optimizer_attains (Q : ConvexBody Plane) {s a : ℝ}
    (hQw : width Q = 1) (hQh : height Q = 1)
    (hq : volume.real (Q : Set Plane) < 1) (ha : a ≤ s)
    (hfit : Real.sqrt ((s - a) / (1 - volume.real (Q : Set Plane))) ≤ min 1 s) :
    ∃ A : ConvexBody Plane, width A = 1 ∧ height A = s ∧
      volume.real (A : Set Plane) = a ∧
      2 * mixedArea volume A Q =
        1 + s - 2 * Real.sqrt ((s - a) * (1 - volume.real (Q : Set Plane))) := by
  first
  | let lam := Real.sqrt ((s - a) / (1 - volume.real (Q : Set Plane)))
    have hlam : 0 ≤ lam := Real.sqrt_nonneg _
    have hlam1 : lam ≤ 1 := hfit.trans (min_le_left _ _)
    have hlams : lam ≤ s := hfit.trans (min_le_right _ _)
    have hden : 0 < 1 - volume.real (Q : Set Plane) := sub_pos.mpr hq
    have hsq : lam ^ 2 = (s - a) / (1 - volume.real (Q : Set Plane)) :=
      Real.sq_sqrt (div_nonneg (sub_nonneg.mpr ha) hden.le)
    have hprod : lam ^ 2 * (1 - volume.real (Q : Set Plane)) = s - a := by
      first
      | rw [hsq, div_mul_cancel₀ _ hden.ne']
    have hroot : lam * (1 - volume.real (Q : Set Plane)) =
        Real.sqrt ((s - a) * (1 - volume.real (Q : Set Plane))) := by
      first
      | have hnonneg : 0 ≤ lam * (1 - volume.real (Q : Set Plane)) := mul_nonneg hlam hden.le
        have hpower : (lam * (1 - volume.real (Q : Set Plane))) ^ 2 =
            (s - a) * (1 - volume.real (Q : Set Plane)) := by
          nlinarith [congrArg (fun z : ℝ => z * (1 - volume.real (Q : Set Plane))) hprod]
        rw [← hpower, Real.sqrt_sq hnonneg]
    obtain ⟨hw, hh⟩ := optimizerBody_widths Q hQw hQh hlam hlam1 hlams
    refine ⟨optimizerBody Q s lam, hw, hh, ?_, ?_⟩
    · rw [optimizerBody_area Q hQw hQh hlam hlam1 hlams, hprod]
      ring
    · rw [optimizerBody_mixedArea Q hQw hQh hlam hlam1 hlams]
      nlinarith [hroot]

theorem optimizer_attains_finiteHull (Q : ConvexBody Plane) {s a : ℝ}
    (hQpoly : PolytopeGeometry.IsFiniteHull (Q : Set Plane))
    (hQw : width Q = 1) (hQh : height Q = 1)
    (hq : volume.real (Q : Set Plane) < 1) (ha : a ≤ s)
    (hfit : Real.sqrt ((s - a) / (1 - volume.real (Q : Set Plane))) ≤ min 1 s) :
    ∃ A : ConvexBody Plane, width A = 1 ∧ height A = s ∧
      volume.real (A : Set Plane) = a ∧
      2 * mixedArea volume A Q =
        1 + s - 2 * Real.sqrt ((s - a) * (1 - volume.real (Q : Set Plane))) ∧
      PolytopeGeometry.IsFiniteHull (A : Set Plane) := by
  first
  | let lam := Real.sqrt ((s - a) / (1 - volume.real (Q : Set Plane)))
    have hlam : 0 ≤ lam := Real.sqrt_nonneg _
    have hlam1 : lam ≤ 1 := hfit.trans (min_le_left _ _)
    have hlams : lam ≤ s := hfit.trans (min_le_right _ _)
    have hden : 0 < 1 - volume.real (Q : Set Plane) := sub_pos.mpr hq
    have hsq : lam ^ 2 = (s - a) / (1 - volume.real (Q : Set Plane)) :=
      Real.sq_sqrt (div_nonneg (sub_nonneg.mpr ha) hden.le)
    have hprod : lam ^ 2 * (1 - volume.real (Q : Set Plane)) = s - a := by
      first
      | rw [hsq, div_mul_cancel₀ _ hden.ne']
    have hroot : lam * (1 - volume.real (Q : Set Plane)) =
        Real.sqrt ((s - a) * (1 - volume.real (Q : Set Plane))) := by
      first
      | have hn : 0 ≤ lam * (1 - volume.real (Q : Set Plane)) := mul_nonneg hlam hden.le
        have hp : (lam * (1 - volume.real (Q : Set Plane))) ^ 2 =
            (s - a) * (1 - volume.real (Q : Set Plane)) := by
          nlinarith [congrArg (fun z : ℝ => z * (1 - volume.real (Q : Set Plane))) hprod]
        rw [← hp, Real.sqrt_sq hn]
    obtain ⟨hw, hh⟩ := optimizerBody_widths Q hQw hQh hlam hlam1 hlams
    refine ⟨optimizerBody Q s lam, hw, hh, ?_, ?_, optimizerBody_finiteHull Q s lam hQpoly⟩
    · rw [optimizerBody_area Q hQw hQh hlam hlam1 hlams, hprod]
      ring
    · rw [optimizerBody_mixedArea Q hQw hQh hlam hlam1 hlams]
      nlinarith [hroot]

end VolumePolynomials.PlanarCorner
