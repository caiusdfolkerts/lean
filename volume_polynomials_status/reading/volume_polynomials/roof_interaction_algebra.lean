module

public import VolumePolynomials.TripleAlgebra

@[expose] public section
set_option autoImplicit false

/-! # The exact non-axis vector contributed by the two roof facets -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators Pointwise

namespace VolumePolynomials.PlanarInteraction

open PlanarExtrusion PlanarMixedForm PlanarCorner PlanarEdges OAI.Paper092

def upperRoofEdge (a b c d : ℝ) : Plane :=
  (-|a| * |c| * max b 0 / a, |a| * |c| * max d 0 / c)

def lowerRoofEdge (a b c d : ℝ) : Plane :=
  (|a| * |c| * min b 0 / a, -|a| * |c| * min d 0 / c)

def upperProductEdge (b c : Plane) : Plane :=
  (if b.1 < 0 then -|c.1| * b.2 else 0, if c.1 < 0 then |b.1| * c.2 else 0)

def lowerProductEdge (b c : Plane) : Plane :=
  (if 0 < b.1 then -|c.1| * b.2 else 0, if 0 < c.1 then |b.1| * c.2 else 0)

theorem oriented_vertical_ratios {e : Plane} (hx : e.1 ≠ 0) (hy : e.2 ≠ 0) :
    |e.1| * max (-orientation e * e.2) 0 / (orientation e * e.1) =
      (if e.1 < 0 then e.2 else 0) ∧
    |e.1| * min (-orientation e * e.2) 0 / (orientation e * e.1) =
      (if 0 < e.1 then -e.2 else 0) := by
  first
  | have hprod : (-orientation e * e.2) * e.1 < 0 := by
      first
      | have h := orientation_mul_product e
        have hp := abs_pos.mpr (mul_ne_zero hx hy)
        nlinarith
    have hk := orientation_ne_zero e
    rcases lt_or_gt_of_ne hx with hx' | hx'
    · have hb : 0 < -orientation e * e.2 := by
        first
        | by_contra h
          have hn := mul_nonneg_of_nonpos_of_nonpos (le_of_not_gt h) hx'.le
          linarith
      rw [max_eq_left hb.le, min_eq_right hb.le, abs_of_neg hx',
        if_pos hx', if_neg (not_lt_of_ge hx'.le)]
      constructor
      · field_simp [hk, hx] <;> ring
      · simp
    · have hb : -orientation e * e.2 < 0 := by
        first
        | by_contra h
          have hn := mul_nonneg (le_of_not_gt h) hx'.le
          linarith
      rw [max_eq_right hb.le, min_eq_left hb.le, abs_of_pos hx',
        if_neg (not_lt_of_ge hx'.le), if_pos hx']
      constructor
      · simp
      · field_simp [hk, hx] <;> ring

theorem upperRoofEdge_oriented {b c : Plane}
    (hb1 : b.1 ≠ 0) (hb2 : b.2 ≠ 0) (hc1 : c.1 ≠ 0) (hc2 : c.2 ≠ 0) :
    upperRoofEdge (orientation b * b.1) (-orientation b * b.2)
      (orientation c * c.1) (-orientation c * c.2) = upperProductEdge b c := by
  first
  | have hb := (oriented_vertical_ratios hb1 hb2).1
    have hc := (oriented_vertical_ratios hc1 hc2).1
    have hab : |orientation b * b.1| = |b.1| := by rw [abs_mul, abs_orientation, one_mul]
    have hac : |orientation c * c.1| = |c.1| := by rw [abs_mul, abs_orientation, one_mul]
    apply Prod.ext
    · change -|orientation b * b.1| * |orientation c * c.1| *
        max (-orientation b * b.2) 0 / (orientation b * b.1) = _
      rw [hab, hac]
      calc
        _ = -|c.1| * (|b.1| * max (-orientation b * b.2) 0 / (orientation b * b.1)) := by ring
        _ = _ := by rw [hb]; split_ifs with h <;> simp [upperProductEdge, h]
    · change |orientation b * b.1| * |orientation c * c.1| *
        max (-orientation c * c.2) 0 / (orientation c * c.1) = _
      rw [hab, hac]
      calc
        _ = |b.1| * (|c.1| * max (-orientation c * c.2) 0 / (orientation c * c.1)) := by ring
        _ = _ := by rw [hc]; split_ifs with h <;> simp [upperProductEdge, h]

theorem lowerRoofEdge_oriented {b c : Plane}
    (hb1 : b.1 ≠ 0) (hb2 : b.2 ≠ 0) (hc1 : c.1 ≠ 0) (hc2 : c.2 ≠ 0) :
    lowerRoofEdge (orientation b * b.1) (-orientation b * b.2)
      (orientation c * c.1) (-orientation c * c.2) = lowerProductEdge b c := by
  first
  | have hb := (oriented_vertical_ratios hb1 hb2).2
    have hc := (oriented_vertical_ratios hc1 hc2).2
    have hab : |orientation b * b.1| = |b.1| := by rw [abs_mul, abs_orientation, one_mul]
    have hac : |orientation c * c.1| = |c.1| := by rw [abs_mul, abs_orientation, one_mul]
    apply Prod.ext
    · change |orientation b * b.1| * |orientation c * c.1| *
        min (-orientation b * b.2) 0 / (orientation b * b.1) = _
      rw [hab, hac]
      calc
        _ = |c.1| * (|b.1| * min (-orientation b * b.2) 0 / (orientation b * b.1)) := by ring
        _ = _ := by rw [hb]; split_ifs with h <;> simp [lowerProductEdge, h] <;> ring
    · change -|orientation b * b.1| * |orientation c * c.1| *
        min (-orientation c * c.2) 0 / (orientation c * c.1) = _
      rw [hab, hac]
      calc
        _ = -|b.1| * (|c.1| * min (-orientation c * c.2) 0 / (orientation c * c.1)) := by ring
        _ = _ := by rw [hc]; split_ifs with h <;> simp [lowerProductEdge, h] <;> ring

theorem roof_product_axis_equivalent {b c : Plane} (hb : b.1 ≠ 0) (hc : c.1 ≠ 0) :
    AxisEquivalent (fun A => SupportGeometry.support (A : Set Plane) (normal (upperProductEdge b c)) +
      SupportGeometry.support (A : Set Plane) (normal (lowerProductEdge b c)))
      (fun A => SupportGeometry.support (A : Set Plane) (normal (interactionEdge b c))) := by
  first
  | rcases lt_or_gt_of_ne hb with hb | hb <;> rcases lt_or_gt_of_ne hc with hc | hc
    · have hq := mul_pos_of_neg_of_neg hb hc
      have hup : upperProductEdge b c = interactionEdge b c := by
        first
        | simp [upperProductEdge, interactionEdge, hb, hc, hq]
      have hlo : lowerProductEdge b c = 0 := by
        first
        | simp [lowerProductEdge, not_lt_of_ge hb.le, not_lt_of_ge hc.le]
      rw [hup, hlo]
      simpa only [normal_zero, support_zero, add_zero, sub_self, AxisEquivalent] using AxisFunctional.zero
    · have hq : ¬0 < b.1 * c.1 := not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg hb.le hc.le)
      have hu : (upperProductEdge b c).2 = 0 := by simp [upperProductEdge, not_lt_of_ge hc.le]
      have hl : (lowerProductEdge b c).1 = 0 := by simp [lowerProductEdge, not_lt_of_ge hb.le]
      have h := (axisFunctional_support_normal (Or.inr hu)).add (axisFunctional_support_normal (Or.inl hl))
      simpa only [AxisEquivalent, interactionEdge, if_neg hq, normal_zero, support_zero, sub_zero] using h
    · have hq : ¬0 < b.1 * c.1 := not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hb.le hc.le)
      have hu : (upperProductEdge b c).1 = 0 := by simp [upperProductEdge, not_lt_of_ge hb.le]
      have hl : (lowerProductEdge b c).2 = 0 := by simp [lowerProductEdge, not_lt_of_ge hc.le]
      have h := (axisFunctional_support_normal (Or.inl hu)).add (axisFunctional_support_normal (Or.inr hl))
      simpa only [AxisEquivalent, interactionEdge, if_neg hq, normal_zero, support_zero, sub_zero] using h
    · have hq := mul_pos hb hc
      have hup : upperProductEdge b c = 0 := by
        first
        | simp [upperProductEdge, not_lt_of_ge hb.le, not_lt_of_ge hc.le]
      have hlo : lowerProductEdge b c = interactionEdge b c := by
        first
        | simp [lowerProductEdge, interactionEdge, hb, hc, hq]
      rw [hup, hlo]
      simpa only [normal_zero, support_zero, zero_add, sub_self, AxisEquivalent] using AxisFunctional.zero

end VolumePolynomials.PlanarInteraction
