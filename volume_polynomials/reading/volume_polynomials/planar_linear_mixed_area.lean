module

public import VolumePolynomials.RightTriangleFormula

@[expose] public section
set_option autoImplicit false

/-! # Linear changes of planar mixed area and right triangles -/

noncomputable section
open Set MeasureTheory Module
open scoped Pointwise BigOperators

namespace VolumePolynomials.PlanarEdges

open PlanarExtrusion PlanarMixedForm PlanarCorner OAI.Paper092

theorem area_mapBody (L : Plane →L[ℝ] Plane) (P : ConvexBody Plane) :
    volume.real (mapBody L P : Set Plane) =
      |LinearMap.det L.toLinearMap| * volume.real (P : Set Plane) := by
  first
  | have h := congrArg ENNReal.toReal
      (Measure.addHaar_image_linearMap (volume : Measure Plane) L.toLinearMap (P : Set Plane))
    simpa only [coe_mapBody, ContinuousLinearMap.coe_coe, measureReal_def, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (abs_nonneg _)] using h

theorem mixedArea_mapBody (L : Plane →L[ℝ] Plane) (P Q : ConvexBody Plane) :
    mixedArea volume (mapBody L P) (mapBody L Q) =
      |LinearMap.det L.toLinearMap| * mixedArea volume P Q := by
  first
  | have h := area_add volume plane_finrank (mapBody L P) (mapBody L Q)
    rw [← mapBody_add, area_mapBody, area_mapBody, area_mapBody,
      area_add volume plane_finrank] at h
    nlinarith

def diagonalLinear (a b : ℝ) : Plane →L[ℝ] Plane :=
  (frameMap (a, 0) (0, b)).toContinuousLinearMap

@[simp] theorem diagonalLinear_apply (a b : ℝ) (x : Plane) :
    diagonalLinear a b x = (a * x.1, b * x.2) := by
  first
  | change x.1 • ((a, 0) : Plane) + x.2 • ((0, b) : Plane) = _
    ext <;> simp [mul_comm]

@[simp] theorem diagonalLinear_det (a b : ℝ) :
    LinearMap.det (diagonalLinear a b).toLinearMap = a * b := by
  first
  | change LinearMap.det (frameMap (a, 0) (0, b)) = _
    rw [frameMap_det]
    simp [determinant]

def diagonalEquiv (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : Plane ≃L[ℝ] Plane :=
  ((diagonalLinear a b).toLinearMap.equivOfDetNeZero
    (by rw [diagonalLinear_det]; exact mul_ne_zero ha hb)).toContinuousLinearEquiv

@[simp] theorem diagonalEquiv_apply (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (x : Plane) :
    diagonalEquiv a b ha hb x = (a * x.1, b * x.2) := diagonalLinear_apply a b x

theorem diagonalEquiv_toContinuousLinearMap (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (diagonalEquiv a b ha hb).toContinuousLinearMap = diagonalLinear a b := by
  first
  | apply ContinuousLinearMap.ext
    intro x
    rfl

theorem diagonalEquiv_symm_apply (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (x : Plane) :
    (diagonalEquiv a b ha hb).symm x = (x.1 / a, x.2 / b) := by
  first
  | apply (diagonalEquiv a b ha hb).injective
    rw [ContinuousLinearEquiv.apply_symm_apply, diagonalEquiv_apply]
    ext <;> simp [ha, hb, mul_div_cancel₀, mul_comm]

theorem width_map_diagonal (a b : ℝ) (P : ConvexBody Plane) :
    width (mapBody (diagonalLinear a b) P) = |a| * width P := by
  first
  | have he : Prod.fst '' (mapBody (diagonalLinear a b) P : Set Plane) =
        (fun x : ℝ => a * x) '' (Prod.fst '' (P : Set Plane)) := by
      simp only [coe_mapBody, Set.image_image]
      congr 1
      funext x
      simp only [Function.comp_apply, diagonalLinear_apply]
    rw [width, he, length_image_mul]
    rfl

theorem height_map_diagonal (a b : ℝ) (P : ConvexBody Plane) :
    height (mapBody (diagonalLinear a b) P) = |b| * height P := by
  first
  | have he : Prod.snd '' (mapBody (diagonalLinear a b) P : Set Plane) =
        (fun x : ℝ => b * x) '' (Prod.snd '' (P : Set Plane)) := by
      simp only [coe_mapBody, Set.image_image]
      congr 1
      funext x
      simp only [Function.comp_apply, diagonalLinear_apply]
    rw [height, he, length_image_mul]
    rfl

theorem support_mapBody (L : Plane →L[ℝ] Plane) (P : ConvexBody Plane)
    (l : Plane →L[ℝ] ℝ) :
    SupportGeometry.support (mapBody L P : Set Plane) l =
      SupportGeometry.support (P : Set Plane) (l.comp L) := by
  first
  | simp only [SupportGeometry.support, coe_mapBody, Set.image_image]
    rfl

theorem support_inverse_diagonal (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (P : ConvexBody Plane) (e : Plane) :
    |a * b| * SupportGeometry.support
        (mapBody (diagonalEquiv a b ha hb).symm.toContinuousLinearMap P : Set Plane) (normal e) =
      SupportGeometry.support (P : Set Plane)
        (normal (|a * b| / b * e.1, |a * b| / a * e.2)) := by
  first
  | rw [support_mapBody, ← support_smul_functional _ _ (abs_nonneg _)]
    congr 1
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, diagonalEquiv_symm_apply, normal_apply, smul_eq_mul]
    field_simp [ha, hb] <;> ring

def rightTriangle (a b : ℝ) : ConvexBody Plane := mapBody (diagonalLinear a b) unitTriangle

@[simp] theorem rightTriangle_width (a b : ℝ) : width (rightTriangle a b) = |a| := by
  first
  | rw [rightTriangle, width_map_diagonal, width_unitTriangle, mul_one]

@[simp] theorem rightTriangle_height (a b : ℝ) : height (rightTriangle a b) = |b| := by
  first
  | rw [rightTriangle, height_map_diagonal, height_unitTriangle, mul_one]

theorem rightTriangle_finiteHull (a b : ℝ) :
    PolytopeGeometry.IsFiniteHull (rightTriangle a b : Set Plane) :=
  unitTriangle_finiteHull.linear_image (diagonalLinear a b).toLinearMap

theorem rightTriangle_support (a b : ℝ) (l : Plane →L[ℝ] ℝ) :
    SupportGeometry.support (rightTriangle a b : Set Plane) l =
      max 0 (max (a * l (1, 0)) (b * l (0, 1))) := by
  first
  | let M := max 0 (max (a * l (1, 0)) (b * l (0, 1)))
    have hM0 : 0 ≤ M := le_max_left _ _
    have hMa : a * l (1, 0) ≤ M := (le_max_left _ _).trans (le_max_right _ _)
    have hMb : b * l (0, 1) ≤ M := (le_max_right _ _).trans (le_max_right _ _)
    apply le_antisymm
    · apply SupportGeometry.support_le (rightTriangle a b).nonempty l
      rintro x ⟨y, hy, rfl⟩
      rw [diagonalLinear_apply, functional_coordinates]
      have h1 := mul_le_mul_of_nonneg_left hMa hy.1
      have h2 := mul_le_mul_of_nonneg_left hMb hy.2.1
      have hsum := mul_le_mul_of_nonneg_right hy.2.2 hM0
      change _ ≤ M
      nlinarith
    · apply max_le
      · have hx : (0 : Plane) ∈ rightTriangle a b :=
          ⟨0, ⟨le_rfl, le_rfl, by norm_num⟩, by simp⟩
        simpa only [map_zero] using SupportGeometry.le_support (rightTriangle a b).isCompact l hx
      · apply max_le
        · have hx : ((a, 0) : Plane) ∈ rightTriangle a b :=
            ⟨(1, 0), ⟨zero_le_one, le_rfl, by norm_num⟩, by simp⟩
          have h := SupportGeometry.le_support (rightTriangle a b).isCompact l hx
          simpa only [functional_coordinates l (a, 0), zero_mul, add_zero] using h
        · have hx : ((0, b) : Plane) ∈ rightTriangle a b :=
            ⟨(0, 1), ⟨le_rfl, zero_le_one, by norm_num⟩, by simp⟩
          have h := SupportGeometry.le_support (rightTriangle a b).isCompact l hx
          simpa only [functional_coordinates l (0, b), zero_mul, zero_add] using h

theorem rightTriangle_mixedArea (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (A : ConvexBody Plane) :
    2 * mixedArea volume A (rightTriangle a b) =
      SupportGeometry.support (A : Set Plane) (normal (0, -(|a * b| / a))) +
      SupportGeometry.support (A : Set Plane) (normal (|a * b| / b, 0)) +
      SupportGeometry.support (A : Set Plane) (normal (-(|a * b| / b), |a * b| / a)) := by
  first
  | let T := diagonalEquiv a b ha hb
    let A' := mapBody T.symm.toContinuousLinearMap A
    have hA : mapBody T.toContinuousLinearMap A' = A := by
      apply ConvexBody.ext
      simp only [A', coe_mapBody, Set.image_image]
      change (fun x => T (T.symm x)) '' (A : Set Plane) = (A : Set Plane)
      ext x
      constructor
      · rintro ⟨y, hy, he⟩
        have hyx : y = x := by simpa only [ContinuousLinearEquiv.apply_symm_apply] using he
        exact hyx ▸ hy
      · intro hx
        exact ⟨x, hx, T.apply_symm_apply x⟩
    have h := mixedArea_mapBody T.toContinuousLinearMap A' unitTriangle
    rw [hA, show T.toContinuousLinearMap = diagonalLinear a b from
        diagonalEquiv_toContinuousLinearMap a b ha hb, diagonalLinear_det] at h
    change mixedArea volume A (rightTriangle a b) = |a * b| * mixedArea volume A' unitTriangle at h
    have hf := unitTriangle_mixedArea A'
    have h0 := support_inverse_diagonal a b ha hb A (0, -1)
    have h1 := support_inverse_diagonal a b ha hb A (1, 0)
    have h2 := support_inverse_diagonal a b ha hb A (-1, 1)
    simp only [mul_zero, mul_one, mul_neg_one] at h0 h1 h2
    change |a * b| * SupportGeometry.support (A' : Set Plane) (normal (0, -1)) = _ at h0
    change |a * b| * SupportGeometry.support (A' : Set Plane) (normal (1, 0)) = _ at h1
    change |a * b| * SupportGeometry.support (A' : Set Plane) (normal (-1, 1)) = _ at h2
    nlinarith [congrArg (fun z : ℝ => |a * b| * z) hf]

end VolumePolynomials.PlanarEdges
