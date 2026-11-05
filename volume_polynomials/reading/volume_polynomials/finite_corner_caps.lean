module

public import VolumePolynomials.HalfZonotopeCaps
public import Mathlib.Algebra.BigOperators.Ring.List

@[expose] public section
set_option autoImplicit false

/-! # The exact corner deficit of a finite half-zonotope cap -/

noncomputable section
open Set MeasureTheory
open scoped Pointwise

namespace VolumePolynomials.HalfZonotope

open PlanarExtrusion

def cornerInteraction (v w : Plane) : ℝ :=
  min (v.1 * (-w.2)) (w.1 * (-v.2))

def cornerEnergy : List Plane → ℝ
  | [] => 0
  | v :: vs => cornerEnergy vs + v.1 * (-v.2) +
      2 * (vs.map (cornerInteraction v)).sum

theorem abs_sub_add_two_min (a b : ℝ) : |a - b| + 2 * min a b = a + b := by
  first
  | rcases le_total a b with hab | hba
    · rw [min_eq_left hab, abs_of_nonpos (sub_nonpos.mpr hab)]
      ring
    · rw [min_eq_right hba, abs_of_nonneg (sub_nonneg.mpr hba)]
      ring

theorem pair_corner_identity (v w : Plane) :
    |determinant v w| + 2 * cornerInteraction v w =
      v.1 * (-w.2) + w.1 * (-v.2) := by
  first
  | have h := abs_sub_add_two_min (v.1 * (-w.2)) (w.1 * (-v.2))
    have he : v.1 * (-w.2) - w.1 * (-v.2) = -determinant v w := by
      first
      | simp only [determinant]
        ring
    rw [he, abs_neg] at h
    exact h

theorem sum_pair_corner_identity (v : Plane) (vs : List Plane) :
    (vs.map (fun w => |determinant v w|)).sum +
        2 * (vs.map (cornerInteraction v)).sum =
      v.1 * (-vs.sum.2) + vs.sum.1 * (-v.2) := by
  first
  | induction vs with
    | nil => simp
    | cons w vs ih =>
        have hp := pair_corner_identity v w
        simp only [List.map_cons, List.sum_cons, Prod.fst_add, Prod.snd_add]
        nlinarith

/-- The full rectangle product is the sum of the zonotope area and the
double corner energy. This is an exact finite algebraic identity. -/
theorem pairArea_add_cornerEnergy (vs : List Plane) :
    pairArea vs + cornerEnergy vs = vs.sum.1 * (-vs.sum.2) := by
  first
  | induction vs with
    | nil => simp [pairArea, cornerEnergy]
    | cons v vs ih =>
        have hc := sum_pair_corner_identity v vs
        simp only [pairArea, cornerEnergy, List.sum_cons, Prod.fst_add, Prod.snd_add]
        nlinarith

/-- The area identity is proved for the actual cap defined by a halfspace cut. -/
theorem area_cap_eq_rectangle_sub_cornerEnergy (vs : List Plane) :
    volume.real (cap vs) = (vs.sum.1 * (-vs.sum.2) - cornerEnergy vs) / 2 := by
  first
  | rw [area_cap]
    linarith [pairArea_add_cornerEnergy vs]

theorem area_unit_cap {vs : List Plane} (hsum : vs.sum = (1, -1)) :
    volume.real (cap vs) = 1 / 2 - cornerEnergy vs / 2 := by
  first
  | rw [area_cap_eq_rectangle_sub_cornerEnergy, hsum]
    norm_num
    ring

theorem cornerInteraction_nonneg {v w : Plane}
    (hv : 0 ≤ v.1 ∧ v.2 ≤ 0) (hw : 0 ≤ w.1 ∧ w.2 ≤ 0) :
    0 ≤ cornerInteraction v w :=
  le_min (mul_nonneg hv.1 (neg_nonneg.mpr hw.2))
    (mul_nonneg hw.1 (neg_nonneg.mpr hv.2))

theorem cornerEnergy_nonneg {vs : List Plane}
    (hvs : ∀ v ∈ vs, 0 ≤ v.1 ∧ v.2 ≤ 0) : 0 ≤ cornerEnergy vs := by
  first
  | induction vs with
    | nil => rfl
    | cons v vs ih =>
        have hv := hvs v List.mem_cons_self
        have ht := fun w hw => hvs w (List.mem_cons_of_mem v hw)
        have hs : 0 ≤ (vs.map (cornerInteraction v)).sum := by
          first
          | apply List.sum_nonneg
            intro x hx
            obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
            exact cornerInteraction_nonneg hv (ht w hw)
        dsimp only [cornerEnergy]
        exact add_nonneg (add_nonneg (ih ht) (mul_nonneg hv.1 (neg_nonneg.mpr hv.2)))
          (mul_nonneg (by norm_num) hs)

theorem cornerInteraction_smul (t : ℝ) (v w : Plane) :
    cornerInteraction (t • v) (t • w) = t ^ 2 * cornerInteraction v w := by
  first
  | simp only [cornerInteraction, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    have h₁ : t * v.1 * -(t * w.2) = t ^ 2 * (v.1 * (-w.2)) := by ring
    have h₂ : t * w.1 * -(t * v.2) = t ^ 2 * (w.1 * (-v.2)) := by ring
    rw [h₁, h₂, ← mul_min_of_nonneg _ _ (sq_nonneg t)]

theorem cornerEnergy_smul (t : ℝ) (vs : List Plane) :
    cornerEnergy (vs.map (fun v => t • v)) = t ^ 2 * cornerEnergy vs := by
  first
  | induction vs with
    | nil => simp [cornerEnergy]
    | cons v vs ih =>
        simp only [List.map_cons, cornerEnergy, ih, Prod.smul_fst, Prod.smul_snd,
          smul_eq_mul, List.map_map, Function.comp_def, cornerInteraction_smul]
        rw [List.sum_map_mul_left]
        ring

theorem cornerEnergy_cons_horizontal {r : ℝ} (hr : 0 ≤ r) {vs : List Plane}
    (hvs : ∀ v ∈ vs, 0 ≤ v.1 ∧ v.2 ≤ 0) :
    cornerEnergy ((r, 0) :: vs) = cornerEnergy vs := by
  first
  | have hs : (vs.map (cornerInteraction (r, 0))).sum = 0 := by
      first
      | apply List.sum_eq_zero
        intro x hx
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
        simp only [cornerInteraction, neg_zero, mul_zero]
        exact min_eq_right (mul_nonneg hr (neg_nonneg.mpr (hvs v hv).2))
    simp [cornerEnergy, hs]

theorem cornerEnergy_cons_vertical {r : ℝ} (hr : 0 ≤ r) {vs : List Plane}
    (hvs : ∀ v ∈ vs, 0 ≤ v.1 ∧ v.2 ≤ 0) :
    cornerEnergy ((0, -r) :: vs) = cornerEnergy vs := by
  first
  | have hs : (vs.map (cornerInteraction (0, -r))).sum = 0 := by
      first
      | apply List.sum_eq_zero
        intro x hx
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
        simp only [cornerInteraction, zero_mul, neg_neg]
        exact min_eq_left (mul_nonneg (hvs v hv).1 hr)
    simp [cornerEnergy, hs]

/-- Adding the two axis directions restores widths while preserving the
quadratic scaling of the genuine area deficit. -/
def interpolatedGenerators (t : ℝ) (vs : List Plane) : List Plane :=
  (1 - t, 0) :: (0, -(1 - t)) :: vs.map (fun v => t • v)

theorem interpolatedGenerators_signed {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {vs : List Plane} (hvs : ∀ v ∈ vs, 0 ≤ v.1 ∧ v.2 ≤ 0) :
    ∀ v ∈ interpolatedGenerators t vs, 0 ≤ v.1 ∧ v.2 ≤ 0 := by
  first
  | intro v hv
    simp only [interpolatedGenerators, List.mem_cons, List.mem_map] at hv
    rcases hv with rfl | rfl | ⟨w, hw, rfl⟩
    · exact ⟨sub_nonneg.mpr ht.2, le_rfl⟩
    · exact ⟨le_rfl, neg_nonpos.mpr (sub_nonneg.mpr ht.2)⟩
    · exact ⟨mul_nonneg ht.1 (hvs w hw).1,
        mul_nonpos_of_nonneg_of_nonpos ht.1 (hvs w hw).2⟩

theorem interpolatedGenerators_sum (t : ℝ) {vs : List Plane}
    (hsum : vs.sum = (1, -1)) : (interpolatedGenerators t vs).sum = (1, -1) := by
  first
  | simp only [interpolatedGenerators, List.sum_cons, ← List.smul_sum, hsum]
    ext <;> simp <;> ring

theorem cornerEnergy_interpolated {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {vs : List Plane} (hvs : ∀ v ∈ vs, 0 ≤ v.1 ∧ v.2 ≤ 0) :
    cornerEnergy (interpolatedGenerators t vs) = t ^ 2 * cornerEnergy vs := by
  first
  | have hm : ∀ w ∈ vs.map (fun v => t • v), 0 ≤ w.1 ∧ w.2 ≤ 0 := by
      first
      | intro w hw
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
        exact ⟨mul_nonneg ht.1 (hvs v hv).1,
          mul_nonpos_of_nonneg_of_nonpos ht.1 (hvs v hv).2⟩
    unfold interpolatedGenerators
    rw [cornerEnergy_cons_horizontal (sub_nonneg.mpr ht.2),
      cornerEnergy_cons_vertical (sub_nonneg.mpr ht.2) hm, cornerEnergy_smul]
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact ⟨le_rfl, neg_nonpos.mpr (sub_nonneg.mpr ht.2)⟩
    · exact hm v hv

theorem area_interpolated_cap {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {vs : List Plane} (hvs : ∀ v ∈ vs, 0 ≤ v.1 ∧ v.2 ≤ 0)
    (hsum : vs.sum = (1, -1)) :
    volume.real (cap (interpolatedGenerators t vs)) =
      1 / 2 - t ^ 2 * (1 / 2 - volume.real (cap vs)) := by
  first
  | rw [area_unit_cap (interpolatedGenerators_sum t hsum), area_unit_cap hsum,
      cornerEnergy_interpolated ht hvs]
    ring

end VolumePolynomials.HalfZonotope
