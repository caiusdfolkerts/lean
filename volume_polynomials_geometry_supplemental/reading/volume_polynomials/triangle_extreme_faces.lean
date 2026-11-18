module

public import VolumePolynomials.MixedAreaDetermination

@[expose] public section
set_option autoImplicit false

/-! # Extreme coordinate segments of the literal edge triangles -/

noncomputable section
open Set MeasureTheory
open scoped Pointwise BigOperators

namespace VolumePolynomials.PlanarEdges

open PlanarExtrusion PlanarMixedForm PlanarCorner OAI.Paper092

theorem rightTriangle_zero (a b : ℝ) : (0 : Plane) ∈ rightTriangle a b := by
  first
  | exact ⟨0, by norm_num [mem_unitTriangle], by simp⟩

theorem rightTriangle_axisX {a b x : ℝ} (hx : min 0 a ≤ x ∧ x ≤ max 0 a) :
    (x, 0) ∈ rightTriangle a b := by
  first
  | by_cases ha : a = 0
    · have hx' : 0 ≤ x ∧ x ≤ 0 := by simpa [ha] using hx
      have hx0 : x = 0 := le_antisymm hx'.2 hx'.1
      subst x
      exact rightTriangle_zero a b
    have ht : 0 ≤ x / a ∧ x / a ≤ 1 := by
      first
      | rcases lt_or_gt_of_ne ha with ha | ha
        · have hx' : a ≤ x ∧ x ≤ 0 := by simpa [min_eq_right ha.le, max_eq_left ha.le] using hx
          exact ⟨div_nonneg_of_nonpos hx'.2 ha.le, (div_le_one_of_neg ha).mpr hx'.1⟩
        · have hx' : 0 ≤ x ∧ x ≤ a := by simpa [min_eq_left ha.le, max_eq_right ha.le] using hx
          exact ⟨div_nonneg hx'.1 ha.le, (div_le_one ha).mpr hx'.2⟩
    refine ⟨(x / a, 0), (mem_unitTriangle _).mpr ⟨ht.1, le_rfl, by simpa using ht.2⟩, ?_⟩
    ext <;> simp only [diagonalLinear_apply, Prod.fst, Prod.snd, mul_zero] <;> field_simp [ha]

theorem rightTriangle_axisY {a b y : ℝ} (hy : min 0 b ≤ y ∧ y ≤ max 0 b) :
    (0, y) ∈ rightTriangle a b := by
  first
  | by_cases hb : b = 0
    · have hy' : 0 ≤ y ∧ y ≤ 0 := by simpa [hb] using hy
      have hy0 : y = 0 := le_antisymm hy'.2 hy'.1
      subst y
      exact rightTriangle_zero a b
    have ht : 0 ≤ y / b ∧ y / b ≤ 1 := by
      first
      | rcases lt_or_gt_of_ne hb with hb | hb
        · have hy' : b ≤ y ∧ y ≤ 0 := by simpa [min_eq_right hb.le, max_eq_left hb.le] using hy
          exact ⟨div_nonneg_of_nonpos hy'.2 hb.le, (div_le_one_of_neg hb).mpr hy'.1⟩
        · have hy' : 0 ≤ y ∧ y ≤ b := by simpa [min_eq_left hb.le, max_eq_right hb.le] using hy
          exact ⟨div_nonneg hy'.1 hb.le, (div_le_one hb).mpr hy'.2⟩
    refine ⟨(0, y / b), (mem_unitTriangle _).mpr ⟨le_rfl, ht.1, by simpa using ht.2⟩, ?_⟩
    ext <;> simp only [diagonalLinear_apply, Prod.fst, Prod.snd, mul_zero] <;> field_simp [hb]

theorem rightTriangle_bounds (a b : ℝ) {p : Plane} (hp : p ∈ rightTriangle a b) :
    (min 0 a ≤ p.1 ∧ p.1 ≤ max 0 a) ∧ (min 0 b ≤ p.2 ∧ p.2 ≤ max 0 b) := by
  first
  | obtain ⟨q, hq, rfl⟩ := hp
    have hq := (mem_unitTriangle q).mp hq
    have hqx : q.1 ≤ 1 := by linarith [hq.2.1, hq.2.2]
    have hqy : q.2 ≤ 1 := by linarith [hq.1, hq.2.2]
    simp only [diagonalLinear_apply]
    constructor
    · rcases le_total 0 a with ha | ha
      · rw [min_eq_left ha, max_eq_right ha]
        exact ⟨mul_nonneg ha hq.1, (mul_le_mul_of_nonneg_left hqx ha).trans_eq (mul_one a)⟩
      · rw [min_eq_right ha, max_eq_left ha]
        exact ⟨by nlinarith [mul_le_mul_of_nonpos_left hqx ha], mul_nonpos_of_nonpos_of_nonneg ha hq.1⟩
    · rcases le_total 0 b with hb | hb
      · rw [min_eq_left hb, max_eq_right hb]
        exact ⟨mul_nonneg hb hq.2.1, (mul_le_mul_of_nonneg_left hqy hb).trans_eq (mul_one b)⟩
      · rw [min_eq_right hb, max_eq_left hb]
        exact ⟨by nlinarith [mul_le_mul_of_nonpos_left hqy hb], mul_nonpos_of_nonpos_of_nonneg hb hq.2.1⟩

theorem max_sub_min_eq_abs (a : ℝ) : max 0 a - min 0 a = |a| := by
  first
  | rcases le_total 0 a with ha | ha
    · rw [max_eq_right ha, min_eq_left ha, abs_of_nonneg ha]
      ring
    · rw [max_eq_left ha, min_eq_right ha, abs_of_nonpos ha]
      ring

theorem rightTriangle_bottom_segment (a b r : ℝ) (hr : 0 ≤ r) (hra : r ≤ |a|)
    (hrb : b < 0 → r = 0) :
    ∃ x : ℝ, (x, min 0 b) ∈ rightTriangle a b ∧ (x + r, min 0 b) ∈ rightTriangle a b := by
  first
  | by_cases hb : 0 ≤ b
    · rw [min_eq_left hb]
      refine ⟨min 0 a, rightTriangle_axisX ⟨le_rfl, min_le_max⟩, ?_⟩
      apply rightTriangle_axisX
      constructor
      · linarith
      · linarith [max_sub_min_eq_abs a]
    · have hr0 := hrb (lt_of_not_ge hb)
      simp only [hr0, add_zero]
      exact ⟨0, rightTriangle_axisY ⟨le_rfl, min_le_max⟩,
        rightTriangle_axisY ⟨le_rfl, min_le_max⟩⟩

theorem rightTriangle_top_segment (a b r : ℝ) (hr : 0 ≤ r) (hra : r ≤ |a|)
    (hrb : 0 < b → r = 0) :
    ∃ x : ℝ, (x, max 0 b) ∈ rightTriangle a b ∧ (x + r, max 0 b) ∈ rightTriangle a b := by
  first
  | by_cases hb : b ≤ 0
    · rw [max_eq_left hb]
      refine ⟨min 0 a, rightTriangle_axisX ⟨le_rfl, min_le_max⟩, ?_⟩
      apply rightTriangle_axisX
      constructor
      · linarith
      · linarith [max_sub_min_eq_abs a]
    · have hr0 := hrb (lt_of_not_ge hb)
      simp only [hr0, add_zero]
      exact ⟨0, rightTriangle_axisY ⟨min_le_max, le_rfl⟩,
        rightTriangle_axisY ⟨min_le_max, le_rfl⟩⟩

theorem rightTriangle_left_segment (a b r : ℝ) (hr : 0 ≤ r) (hrb : r ≤ |b|)
    (hra : a < 0 → r = 0) :
    ∃ y : ℝ, (min 0 a, y) ∈ rightTriangle a b ∧ (min 0 a, y + r) ∈ rightTriangle a b := by
  first
  | by_cases ha : 0 ≤ a
    · rw [min_eq_left ha]
      refine ⟨min 0 b, rightTriangle_axisY ⟨le_rfl, min_le_max⟩, ?_⟩
      apply rightTriangle_axisY
      constructor
      · linarith
      · linarith [max_sub_min_eq_abs b]
    · have hr0 := hra (lt_of_not_ge ha)
      simp only [hr0, add_zero]
      exact ⟨0, rightTriangle_axisX ⟨le_rfl, min_le_max⟩,
        rightTriangle_axisX ⟨le_rfl, min_le_max⟩⟩

theorem rightTriangle_right_segment (a b r : ℝ) (hr : 0 ≤ r) (hrb : r ≤ |b|)
    (hra : 0 < a → r = 0) :
    ∃ y : ℝ, (max 0 a, y) ∈ rightTriangle a b ∧ (max 0 a, y + r) ∈ rightTriangle a b := by
  first
  | by_cases ha : a ≤ 0
    · rw [max_eq_left ha]
      refine ⟨min 0 b, rightTriangle_axisY ⟨le_rfl, min_le_max⟩, ?_⟩
      apply rightTriangle_axisY
      constructor
      · linarith
      · linarith [max_sub_min_eq_abs b]
    · have hr0 := hra (lt_of_not_ge ha)
      simp only [hr0, add_zero]
      exact ⟨0, rightTriangle_axisX ⟨min_le_max, le_rfl⟩,
        rightTriangle_axisX ⟨min_le_max, le_rfl⟩⟩

theorem triangleFromEdge_extreme_segments (e : Plane) :
    (∃ x : ℝ, (x, min 0 (-orientation e * e.2)) ∈ triangleFromEdge e ∧
      (x + max (-e.1) 0, min 0 (-orientation e * e.2)) ∈ triangleFromEdge e) ∧
    (∃ x : ℝ, (x, max 0 (-orientation e * e.2)) ∈ triangleFromEdge e ∧
      (x + max e.1 0, max 0 (-orientation e * e.2)) ∈ triangleFromEdge e) ∧
    (∃ y : ℝ, (min 0 (orientation e * e.1), y) ∈ triangleFromEdge e ∧
      (min 0 (orientation e * e.1), y + max e.2 0) ∈ triangleFromEdge e) ∧
    (∃ y : ℝ, (max 0 (orientation e * e.1), y) ∈ triangleFromEdge e ∧
      (max 0 (orientation e * e.1), y + max (-e.2) 0) ∈ triangleFromEdge e) := by
  first
  | have ha : |orientation e * e.1| = |e.1| := by rw [abs_mul, abs_orientation, one_mul]
    have hb : |-orientation e * e.2| = |e.2| := by rw [abs_mul, abs_neg, abs_orientation, one_mul]
    have hxy : (-orientation e * e.2) * e.1 ≤ 0 := by
      first
      | have h := orientation_mul_product e
        nlinarith [abs_nonneg (e.1 * e.2)]
    have hyx : (orientation e * e.1) * e.2 ≥ 0 := by
      first
      | have h := orientation_mul_product e
        nlinarith [abs_nonneg (e.1 * e.2)]
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply rightTriangle_bottom_segment _ _ _ (le_max_right _ _)
      · rw [ha]
        exact max_le (neg_le_abs _) (abs_nonneg _)
      · intro hneg
        apply max_eq_right
        have hx : 0 ≤ e.1 := by nlinarith
        exact neg_nonpos.mpr hx
    · apply rightTriangle_top_segment _ _ _ (le_max_right _ _)
      · rw [ha]
        exact max_le (le_abs_self _) (abs_nonneg _)
      · intro hpos
        apply max_eq_right
        nlinarith
    · apply rightTriangle_left_segment _ _ _ (le_max_right _ _)
      · rw [hb]
        exact max_le (le_abs_self _) (abs_nonneg _)
      · intro hneg
        apply max_eq_right
        nlinarith
    · apply rightTriangle_right_segment _ _ _ (le_max_right _ _)
      · rw [hb]
        exact max_le (neg_le_abs _) (abs_nonneg _)
      · intro hpos
        apply max_eq_right
        have hy : 0 ≤ e.2 := by nlinarith
        exact neg_nonpos.mpr hy

end VolumePolynomials.PlanarEdges
