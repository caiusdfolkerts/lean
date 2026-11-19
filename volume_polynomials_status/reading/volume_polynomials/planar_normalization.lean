module

public import VolumePolynomials.MixedVolumeTransport
public import VolumePolynomials.CrossPlaneMixedVolume
public import VolumePolynomials.GeneralInteractionBody
public import Mathlib.LinearAlgebra.Determinant

@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# Normalizing the six repeated coefficients

The scalar `M` is the actual positive factor from the coordinate Jacobian
and the volume of the quotient projection. The six equations retain that
factor. One diagonal map normalizes all three bodies simultaneously, and
its determinant gives the exact transformation of the triple mixed volume.
-/

open Set MeasureTheory Module
open scoped Pointwise BigOperators

namespace VolumePolynomials.PlanarInteraction

open PlanarExtrusion PlanarMixedForm PlanarCorner PlanarEdges

def diagonalSpace (l a c : ℝ) : Space →L[ℝ] Space :=
  (l • ContinuousLinearMap.id ℝ ℝ).prodMap (diagonalLinear a c)

@[simp] theorem diagonalSpace_apply (l a c : ℝ) (p : Space) :
    diagonalSpace l a c p = (l * p.1, (a * p.2.1, c * p.2.2)) := by
  first
  | change (l * p.1, diagonalLinear a c p.2) = _
    rw [diagonalLinear_apply]

@[simp] theorem diagonalSpace_det (l a c : ℝ) :
    LinearMap.det (diagonalSpace l a c).toLinearMap = l * (a * c) := by
  first
  | change LinearMap.det ((l • LinearMap.id : ℝ →ₗ[ℝ] ℝ).prodMap
      (diagonalLinear a c).toLinearMap) = _
    rw [LinearMap.det_prodMap, diagonalLinear_det]
    simp

theorem diagonalSpace_XY (l a c : ℝ) (A : ConvexBody Plane) :
    mapBody (diagonalSpace l a c) (mapBody embedXY A) =
      mapBody embedXY (mapBody (diagonalLinear a c) A) := by
  first
  | apply ConvexBody.ext
    simp only [coe_mapBody, Set.image_image]
    congr 1
    funext p
    simp only [Function.comp_apply, diagonalSpace_apply, diagonalLinear_apply, embedXY]
    simp

theorem diagonalSpace_YZ (l a c : ℝ) (B : ConvexBody Plane) :
    mapBody (diagonalSpace l a c) (mapBody embedYZ B) =
      mapBody embedYZ (mapBody (diagonalLinear c l) B) := by
  first
  | apply ConvexBody.ext
    simp only [coe_mapBody, Set.image_image]
    congr 1
    funext p
    simp only [Function.comp_apply, diagonalSpace_apply, diagonalLinear_apply, embedYZ]
    simp

theorem diagonalSpace_XZ (l a c : ℝ) (C : ConvexBody Plane) :
    mapBody (diagonalSpace l a c) (mapBody embedXZ C) =
      mapBody embedXZ (mapBody (diagonalLinear a l) C) := by
  first
  | apply ConvexBody.ext
    simp only [coe_mapBody, Set.image_image]
    congr 1
    funext p
    simp only [Function.comp_apply, diagonalSpace_apply, diagonalLinear_apply, embedXZ]
    simp

/-- Determinant transport for the three distinct coordinate planes,
including singular diagonal maps. -/
theorem triple_diagonal (l a c : ℝ) (A B C : ConvexBody Plane) :
    triple (mapBody (diagonalLinear a c) A)
      (mapBody (diagonalLinear c l) B) (mapBody (diagonalLinear a l) C) =
      |l * (a * c)| * triple A B C := by
  first
  | have h := mixedVolume_map_linear volume (diagonalSpace l a c)
      ![mapBody embedXY A, mapBody embedYZ B, mapBody embedXZ C]
    have heq : (fun i : Fin 3 => mapBody (diagonalSpace l a c)
        (![mapBody embedXY A, mapBody embedYZ B, mapBody embedXZ C] i)) =
        ![mapBody embedXY (mapBody (diagonalLinear a c) A),
          mapBody embedYZ (mapBody (diagonalLinear c l) B),
          mapBody embedXZ (mapBody (diagonalLinear a l) C)] := by
      first
      | funext i
        fin_cases i
        · exact diagonalSpace_XY l a c A
        · exact diagonalSpace_YZ l a c B
        · exact diagonalSpace_XZ l a c C
    simpa only [heq, diagonalSpace_det, triple, mixed3] using h

def normalizeA (a c : ℝ) (A : ConvexBody Plane) : ConvexBody Plane :=
  mapBody (diagonalLinear a⁻¹ c⁻¹) A

def normalizeB (c l : ℝ) (B : ConvexBody Plane) : ConvexBody Plane :=
  mapBody (diagonalLinear c⁻¹ l⁻¹) B

def normalizeC (a l : ℝ) (C : ConvexBody Plane) : ConvexBody Plane :=
  mapBody (diagonalLinear a⁻¹ l⁻¹) C

/-- These are literal coefficient equalities, with no abstract mixed-volume
operation. In the lifted case `τ` is the mean fiber area and `κ = cₖ`.
In the cubic case `τ = area A` and `κ = 1`. -/
structure RepeatedCoefficientData (α s z κ : ℝ) where
  A : ConvexBody Plane
  B : ConvexBody Plane
  C : ConvexBody Plane
  M : ℝ
  τ : ℝ
  M_pos : 0 < M
  τ_nonneg : 0 ≤ τ
  AAB : M * τ * height B = 3 * κ * α
  AAC : M * τ * height C = 3 * κ * α
  BBA : M * volume.real (B : Set Plane) * width A = 3
  BBC : M * volume.real (B : Set Plane) * width C = 3
  CCA : M * volume.real (C : Set Plane) * height A = 3 * s
  CCB : M * volume.real (C : Set Plane) * width B = 3
  area_lower : τ / κ ≤ volume.real (A : Set Plane)
  ABC : M * (6 * triple A B C) = 6 * z

structure NormalizedPlanarData (α s z : ℝ) where
  A : ConvexBody Plane
  B : ConvexBody Plane
  C : ConvexBody Plane
  T : ℝ
  T_pos : 0 < T
  A_width : width A = 1
  A_height : height A = s
  A_area : α * T ≤ volume.real (A : Set Plane)
  B_width : width B = 1
  B_height : height B = 1
  C_width : width C = 1
  C_height : height C = 1
  B_area : volume.real (B : Set Plane) = T
  C_area : volume.real (C : Set Plane) = T
  triple_value : 6 * triple A B C = 2 * T * z

theorem RepeatedCoefficientData.positive_factors {α s z κ : ℝ}
    (D : RepeatedCoefficientData α s z κ) (hα : 0 < α) (hκ : 0 < κ) :
    0 < width D.A ∧ 0 < width D.B ∧ 0 < height D.B ∧ 0 < D.τ := by
  first
  | have ha : 0 < width D.A := by
      first
      | by_contra! h
        have hz : width D.A = 0 := le_antisymm h measureReal_nonneg
        have he := D.BBA
        rw [hz, mul_zero] at he
        norm_num at he
    have hc : 0 < width D.B := by
      first
      | by_contra! h
        have hz : width D.B = 0 := le_antisymm h measureReal_nonneg
        have he := D.CCB
        rw [hz, mul_zero] at he
        norm_num at he
    have hτ : 0 < D.τ := by
      first
      | by_contra! h
        have hz : D.τ = 0 := le_antisymm h D.τ_nonneg
        have he := D.AAB
        rw [hz, mul_zero, zero_mul] at he
        have : 0 < 3 * κ * α := by positivity
        linarith
    have hl : 0 < height D.B := by
      first
      | by_contra! h
        have hz : height D.B = 0 := le_antisymm h measureReal_nonneg
        have he := D.AAB
        rw [hz, mul_zero] at he
        have : 0 < 3 * κ * α := by positivity
        linarith
    exact ⟨ha, hc, hl, hτ⟩

theorem RepeatedCoefficientData.width_relations {α s z κ : ℝ}
    (D : RepeatedCoefficientData α s z κ) (hα : 0 < α) (hκ : 0 < κ) :
    height D.C = height D.B ∧ width D.C = width D.A ∧ height D.A = s * width D.B := by
  first
  | obtain ⟨ha, hc, hl, hτ⟩ := D.positive_factors hα hκ
    have hB : D.M * volume.real (D.B : Set Plane) ≠ 0 := by
      first
      | intro h
        have he := D.BBA
        rw [h, zero_mul] at he
        norm_num at he
    have hC : D.M * volume.real (D.C : Set Plane) ≠ 0 := by
      first
      | intro h
        have he := D.CCB
        rw [h, zero_mul] at he
        norm_num at he
    refine ⟨mul_left_cancel₀ (mul_ne_zero D.M_pos.ne' hτ.ne')
      (D.AAC.trans D.AAB.symm), mul_left_cancel₀ hB (D.BBC.trans D.BBA.symm), ?_⟩
    apply mul_left_cancel₀ hC
    calc
      _ = 3 * s := D.CCA
      _ = s * (D.M * volume.real (D.C : Set Plane) * width D.B) := by rw [D.CCB]; ring
      _ = _ := by ring

def normalizationScale {α s z κ : ℝ} (D : RepeatedCoefficientData α s z κ) : ℝ :=
  3 / (D.M * width D.A * width D.B * height D.B)

theorem normalizationScale_pos {α s z κ : ℝ}
    (D : RepeatedCoefficientData α s z κ) (hα : 0 < α) (hκ : 0 < κ) :
    0 < normalizationScale D := by
  first
  | obtain ⟨ha, hc, hl, _⟩ := D.positive_factors hα hκ
    exact div_pos (by norm_num) (mul_pos (mul_pos (mul_pos D.M_pos ha) hc) hl)

theorem RepeatedCoefficientData.normalized_area_identities {α s z κ : ℝ}
    (D : RepeatedCoefficientData α s z κ) (hα : 0 < α) (hκ : 0 < κ) :
    volume.real (normalizeB (width D.B) (height D.B) D.B : Set Plane) = normalizationScale D ∧
    volume.real (normalizeC (width D.A) (height D.B) D.C : Set Plane) = normalizationScale D ∧
    D.τ / κ / (width D.A * width D.B) = α * normalizationScale D := by
  first
  | obtain ⟨ha, hc, hl, hτ⟩ := D.positive_factors hα hκ
    have hBa := D.BBA
    have hCb := D.CCB
    have hAa := D.AAB
    constructor
    · rw [normalizeB, area_mapBody, diagonalLinear_det,
        abs_of_pos (mul_pos (inv_pos.mpr hc) (inv_pos.mpr hl))]
      unfold normalizationScale
      field_simp [D.M_pos.ne', ha.ne', hc.ne', hl.ne']
      nlinarith [congrArg (fun x : ℝ => x * height D.B * width D.B) hBa]
    constructor
    · rw [normalizeC, area_mapBody, diagonalLinear_det,
        abs_of_pos (mul_pos (inv_pos.mpr ha) (inv_pos.mpr hl))]
      unfold normalizationScale
      field_simp [D.M_pos.ne', ha.ne', hc.ne', hl.ne']
      nlinarith [congrArg (fun x : ℝ => x * height D.B * width D.A) hCb]
    · unfold normalizationScale
      field_simp [D.M_pos.ne', ha.ne', hc.ne', hl.ne', hκ.ne']
      nlinarith [congrArg (fun x : ℝ => x * width D.A * width D.B) hAa]

/-- The same diagonal normalization proves the cubic statement and the
averaged higher-dimensional statement, without discarding its Jacobian. -/
def RepeatedCoefficientData.normalize {α s z κ : ℝ}
    (D : RepeatedCoefficientData α s z κ) (hα : 0 < α) (hκ : 0 < κ) :
    NormalizedPlanarData α s z := by
  first
  | obtain ⟨ha, hc, hl, hτ⟩ := D.positive_factors hα hκ
    obtain ⟨hf, he, hb⟩ := D.width_relations hα hκ
    obtain ⟨hBa, hCa, hAa⟩ := D.normalized_area_identities hα hκ
    refine ⟨normalizeA (width D.A) (width D.B) D.A,
      normalizeB (width D.B) (height D.B) D.B,
      normalizeC (width D.A) (height D.B) D.C,
      normalizationScale D, normalizationScale_pos D hα hκ, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      hBa, hCa, ?_⟩
    · rw [normalizeA, width_map_diagonal, abs_of_pos (inv_pos.mpr ha), inv_mul_cancel₀ ha.ne']
    · rw [normalizeA, height_map_diagonal, abs_of_pos (inv_pos.mpr hc), hb]
      field_simp [hc.ne']
    · rw [normalizeA, area_mapBody, diagonalLinear_det,
        abs_of_pos (mul_pos (inv_pos.mpr ha) (inv_pos.mpr hc)), ← hAa]
      have h := div_le_div_of_nonneg_right D.area_lower (mul_pos ha hc).le
      simpa only [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc] using h
    · rw [normalizeB, width_map_diagonal, abs_of_pos (inv_pos.mpr hc), inv_mul_cancel₀ hc.ne']
    · rw [normalizeB, height_map_diagonal, abs_of_pos (inv_pos.mpr hl), inv_mul_cancel₀ hl.ne']
    · rw [normalizeC, width_map_diagonal, abs_of_pos (inv_pos.mpr ha), he, inv_mul_cancel₀ ha.ne']
    · rw [normalizeC, height_map_diagonal, abs_of_pos (inv_pos.mpr hl), hf, inv_mul_cancel₀ hl.ne']
    · rw [normalizeA, normalizeB, normalizeC, triple_diagonal,
        abs_of_pos (mul_pos (inv_pos.mpr hl) (mul_pos (inv_pos.mpr ha) (inv_pos.mpr hc)))]
      unfold normalizationScale
      have habc := D.ABC
      field_simp [D.M_pos.ne', ha.ne', hc.ne', hl.ne']
      nlinarith [congrArg (fun x : ℝ => x * width D.A * width D.B * height D.B) habc]

theorem RepeatedCoefficientData.normalize_area_eq {α s z κ : ℝ}
    (D : RepeatedCoefficientData α s z κ) (hα : 0 < α) (hκ : 0 < κ)
    (harea : volume.real (D.A : Set Plane) = D.τ / κ) :
    volume.real ((D.normalize hα hκ).A : Set Plane) = α * (D.normalize hα hκ).T := by
  first
  | obtain ⟨ha, hc, hl, _⟩ := D.positive_factors hα hκ
    change volume.real (normalizeA (width D.A) (width D.B) D.A : Set Plane) =
      α * normalizationScale D
    rw [normalizeA, area_mapBody, diagonalLinear_det,
      abs_of_pos (mul_pos (inv_pos.mpr ha) (inv_pos.mpr hc)), harea,
      ← (D.normalized_area_identities hα hκ).2.2]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

end VolumePolynomials.PlanarInteraction
