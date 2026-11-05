module

public import VolumePolynomials.AxisFunctionals

@[expose] public section
set_option autoImplicit false

/-! # The six actual halfspaces of a sum of two right triangles -/

noncomputable section
open Set MeasureTheory Matrix
open scoped Pointwise BigOperators

namespace VolumePolynomials.PlanarInteraction

open PlanarExtrusion PlanarMixedForm PlanarCorner PlanarEdges OAI.Paper092

theorem mem_rightTriangle_quotients {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (p : Plane) :
    p ∈ rightTriangle a b ↔ 0 ≤ p.1 / a ∧ 0 ≤ p.2 / b ∧ p.1 / a + p.2 / b ≤ 1 := by
  first
  | constructor
    · rintro ⟨q, hq, rfl⟩
      simpa only [diagonalLinear_apply, mul_div_cancel_left₀ _ ha,
        mul_div_cancel_left₀ _ hb] using (mem_unitTriangle q).mp hq
    · intro hp
      refine ⟨(p.1 / a, p.2 / b), (mem_unitTriangle _).mpr hp, ?_⟩
      ext <;> simp only [diagonalLinear_apply, Prod.fst, Prod.snd] <;> field_simp [ha, hb]

theorem mem_rightTriangle_slice {a b x z : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (x, z) ∈ rightTriangle a b ↔
      0 ≤ x / a ∧ x / a ≤ 1 ∧
        min b 0 * (1 - x / a) ≤ z ∧ z ≤ max b 0 * (1 - x / a) := by
  first
  | rw [mem_rightTriangle_quotients ha hb]
    rcases lt_or_gt_of_ne hb with hb | hb
    · rw [min_eq_left hb.le, max_eq_right hb.le, zero_mul]
      constructor
      · rintro ⟨hx, hz, hsum⟩
        have hzu : z / b ≤ 1 - x / a := by linarith
        have hlo := (div_le_iff_of_neg hb).mp hzu
        have hhi := (le_div_iff_of_neg hb).mp hz
        exact ⟨hx, by linarith, by nlinarith, by simpa using hhi⟩
      · rintro ⟨hx, hxu, hlo, hhi⟩
        have hz : 0 ≤ z / b := (le_div_iff_of_neg hb).mpr (by simpa using hhi)
        have hzu : z / b ≤ 1 - x / a := (div_le_iff_of_neg hb).mpr (by nlinarith)
        exact ⟨hx, hz, by linarith⟩
    · rw [min_eq_right hb.le, max_eq_left hb.le, zero_mul]
      constructor
      · rintro ⟨hx, hz, hsum⟩
        have hzu : z / b ≤ 1 - x / a := by linarith
        have hlo := (le_div_iff₀ hb).mp hz
        have hhi := (div_le_iff₀ hb).mp hzu
        exact ⟨hx, by linarith, by simpa using hlo, by nlinarith⟩
      · rintro ⟨hx, hxu, hlo, hhi⟩
        have hz : 0 ≤ z / b := (le_div_iff₀ hb).mpr (by simpa using hlo)
        have hzu : z / b ≤ 1 - x / a := (div_le_iff₀ hb).mpr (by nlinarith)
        exact ⟨hx, hz, by linarith⟩

def trianglePlaneSum (a b c d : ℝ) : ConvexBody Space :=
  mapBody embedYZ (rightTriangle a b) + mapBody embedXZ (rightTriangle c d)

theorem mem_trianglePlaneSum {a b c d : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (p : Space) :
    p ∈ trianglePlaneSum a b c d ↔
      (0 ≤ p.2.1 / c ∧ p.2.1 / c ≤ 1) ∧
      (0 ≤ p.2.2 / a ∧ p.2.2 / a ≤ 1) ∧
      min b 0 * (1 - p.2.2 / a) + min d 0 * (1 - p.2.1 / c) ≤ p.1 ∧
      p.1 ≤ max b 0 * (1 - p.2.2 / a) + max d 0 * (1 - p.2.1 / c) := by
  first
  | constructor
    · rintro ⟨u, ⟨u', hu, rfl⟩, v, ⟨v', hv, rfl⟩, he⟩
      have hx : v'.1 = p.2.1 := by simpa [embedYZ, embedXZ] using congrArg (fun q : Space => q.2.1) he
      have hy : u'.1 = p.2.2 := by simpa [embedYZ, embedXZ] using congrArg (fun q : Space => q.2.2) he
      have hz : u'.2 + v'.2 = p.1 := by simpa [embedYZ, embedXZ] using congrArg Prod.fst he
      have hB := (mem_rightTriangle_slice ha hb).mp hu
      have hC := (mem_rightTriangle_slice hc hd).mp hv
      rw [hx] at hC
      rw [hy] at hB
      exact ⟨⟨hC.1, hC.2.1⟩, ⟨hB.1, hB.2.1⟩,
        by linarith [hB.2.2.1, hC.2.2.1], by linarith [hB.2.2.2, hC.2.2.2]⟩
    · rintro ⟨hx, hy, hlo, hhi⟩
      have hB : min b 0 * (1 - p.2.2 / a) ≤ max b 0 * (1 - p.2.2 / a) :=
        mul_le_mul_of_nonneg_right min_le_max (sub_nonneg.mpr hy.2)
      have hC : min d 0 * (1 - p.2.1 / c) ≤ max d 0 * (1 - p.2.1 / c) :=
        mul_le_mul_of_nonneg_right min_le_max (sub_nonneg.mpr hx.2)
      have hmem : p.1 ∈ Icc (min b 0 * (1 - p.2.2 / a)) (max b 0 * (1 - p.2.2 / a)) +
          Icc (min d 0 * (1 - p.2.1 / c)) (max d 0 * (1 - p.2.1 / c)) := by
        first
        | rw [Icc_add_Icc hB hC]
          exact ⟨hlo, hhi⟩
      obtain ⟨zB, hzB, zC, hzC, hz⟩ := hmem
      refine ⟨embedYZ (p.2.2, zB), ⟨(p.2.2, zB), ?_, rfl⟩,
        embedXZ (p.2.1, zC), ⟨(p.2.1, zC), ?_, rfl⟩, ?_⟩
      · exact (mem_rightTriangle_slice ha hb).mpr ⟨hy.1, hy.2, hzB.1, hzB.2⟩
      · exact (mem_rightTriangle_slice hc hd).mpr ⟨hx.1, hx.2, hzC.1, hzC.2⟩
      · ext <;> simp [embedYZ, embedXZ, hz]

def zCoord : Space →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ Plane
def xCoord : Space →L[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
  (ContinuousLinearMap.snd ℝ ℝ Plane)
def yCoord : Space →L[ℝ] ℝ := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp
  (ContinuousLinearMap.snd ℝ ℝ Plane)

def prismCenter (a b c d : ℝ) : Space := ((b + d) / 3, (c / 3, a / 3))
def prismHalfHeight (b d : ℝ) : ℝ := (|b| + |d|) / 3

def upperPrismNormal (a b c d : ℝ) : Space →L[ℝ] ℝ :=
  zCoord + (max d 0 / c) • xCoord + (max b 0 / a) • yCoord

def lowerPrismNormal (a b c d : ℝ) : Space →L[ℝ] ℝ :=
  -zCoord - (min d 0 / c) • xCoord - (min b 0 / a) • yCoord

def prismNormals (a b c d : ℝ) : Fin 6 → Space →L[ℝ] ℝ :=
  ![(-3 / c) • xCoord, (3 / (2 * c)) • xCoord,
    (-3 / a) • yCoord, (3 / (2 * a)) • yCoord,
    (prismHalfHeight b d)⁻¹ • upperPrismNormal a b c d,
    (prismHalfHeight b d)⁻¹ • lowerPrismNormal a b c d]

theorem prismHalfHeight_positive {b d : ℝ} (hb : b ≠ 0) : 0 < prismHalfHeight b d := by
  first
  | unfold prismHalfHeight
    positivity

theorem upperPrismNormal_center {a b c d : ℝ} (ha : a ≠ 0) (hc : c ≠ 0) :
    upperPrismNormal a b c d (prismCenter a b c d) = max b 0 + max d 0 - prismHalfHeight b d := by
  first
  | have hb := twice_positive_part b
    have hd := twice_positive_part d
    simp only [upperPrismNormal, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, prismCenter, zCoord, xCoord, yCoord, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
    have hb' : max b 0 / a * (a / 3) = max b 0 / 3 := by field_simp [ha] <;> ring
    have hd' : max d 0 / c * (c / 3) = max d 0 / 3 := by field_simp [hc] <;> ring
    rw [hb', hd']
    dsimp only [prismHalfHeight]
    linarith

theorem lowerPrismNormal_center {a b c d : ℝ} (ha : a ≠ 0) (hc : c ≠ 0) :
    lowerPrismNormal a b c d (prismCenter a b c d) = -min b 0 - min d 0 - prismHalfHeight b d := by
  first
  | have hb : b - 2 * min b 0 = |b| := by
      first
      | rcases le_total b 0 with hb | hb
        · rw [min_eq_left hb, abs_of_nonpos hb] <;> ring
        · rw [min_eq_right hb, abs_of_nonneg hb] <;> ring
    have hd : d - 2 * min d 0 = |d| := by
      first
      | rcases le_total d 0 with hd | hd
        · rw [min_eq_left hd, abs_of_nonpos hd] <;> ring
        · rw [min_eq_right hd, abs_of_nonneg hd] <;> ring
    simp only [lowerPrismNormal, ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, prismCenter, zCoord, xCoord, yCoord,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
    have hb' : min b 0 / a * (a / 3) = min b 0 / 3 := by field_simp [ha] <;> ring
    have hd' : min d 0 / c * (c / 3) = min d 0 / 3 := by field_simp [hc] <;> ring
    rw [hb', hd']
    dsimp only [prismHalfHeight]
    linarith

theorem prism_halfspace_body {a b c d : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    HalfspacePyramids.body (prismNormals a b c d) =
      (translateBody (-prismCenter a b c d) (trianglePlaneSum a b c d) : Set Space) := by
  first
  | have hH := prismHalfHeight_positive (d := d) hb
    ext p
    change (∀ i : Fin 6, prismNormals a b c d i p ≤ 1) ↔
      p ∈ translateBody (-prismCenter a b c d) (trianglePlaneSum a b c d)
    rw [mem_translateBody]
    have hp : p - -prismCenter a b c d = p + prismCenter a b c d := by abel
    rw [hp, mem_trianglePlaneSum ha hb hc hd]
    have hx : (p.2.1 + c / 3) / c = p.2.1 / c + 1 / 3 := by field_simp [hc] <;> ring
    have hy : (p.2.2 + a / 3) / a = p.2.2 / a + 1 / 3 := by field_simp [ha] <;> ring
    have hupper := upperPrismNormal_center (b := b) (d := d) ha hc
    have hlower := lowerPrismNormal_center (b := b) (d := d) ha hc
    have hU : upperPrismNormal a b c d (p + prismCenter a b c d) =
        p.1 + max d 0 / c * p.2.1 + max b 0 / a * p.2.2 +
          (max b 0 + max d 0 - prismHalfHeight b d) := by
      first
      | rw [map_add, hupper]
        rfl
    have hL : lowerPrismNormal a b c d (p + prismCenter a b c d) =
        -p.1 - min d 0 / c * p.2.1 - min b 0 / a * p.2.2 +
          (-min b 0 - min d 0 - prismHalfHeight b d) := by
      first
      | rw [map_add, hlower]
        rfl
    simp only [Fin.forall_fin_succ, Fin.forall_fin_zero, prismNormals,
      Matrix.cons_val_zero, Matrix.cons_val_succ, ContinuousLinearMap.smul_apply,
      smul_eq_mul, upperPrismNormal, lowerPrismNormal, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply, zCoord, xCoord, yCoord,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      Prod.fst_add, Prod.snd_add, prismCenter] at *
    rw [hx, hy]
    have heX : (-3 / c) * p.2.1 = -3 * (p.2.1 / c) := by ring
    have heX' : (3 / (2 * c)) * p.2.1 = (3 / 2) * (p.2.1 / c) := by field_simp [hc] <;> ring
    have heY : (-3 / a) * p.2.2 = -3 * (p.2.2 / a) := by ring
    have heY' : (3 / (2 * a)) * p.2.2 = (3 / 2) * (p.2.2 / a) := by field_simp [ha] <;> ring
    rw [heX, heX', heY, heY', ← div_eq_inv_mul, ← div_eq_inv_mul,
      div_le_one hH, div_le_one hH]
    have hca (r : ℝ) : r / a * (a / 3) = r / 3 := by field_simp [ha] <;> ring
    have hcc (r : ℝ) : r / c * (c / 3) = r / 3 := by field_simp [hc] <;> ring
    rw [hca, hcc] at hupper hlower
    simp only [div_eq_mul_inv] at *
    constructor
    · rintro ⟨h0, h1, h2, h3, h4, h5, _⟩
      refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ?_, ?_⟩ <;>
        nlinarith [hU, hL]
    · rintro ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩, hlo, hhi⟩
      refine ⟨by linarith, by linarith, by linarith, by linarith, ?_, ?_, trivial⟩ <;>
        nlinarith [hU, hL]

end VolumePolynomials.PlanarInteraction
