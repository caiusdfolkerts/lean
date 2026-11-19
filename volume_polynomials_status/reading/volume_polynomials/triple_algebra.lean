module

public import VolumePolynomials.CoordinateMixedProjection

@[expose] public section

set_option autoImplicit false

/-! # Exact trilinearity and coordinate-supported remainders -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators Pointwise

namespace VolumePolynomials.PlanarInteraction

open PlanarExtrusion PlanarMixedForm PlanarCorner PlanarEdges OAI.Paper092

theorem triple_add_middle (A B D C : ConvexBody Plane) :
    triple A (B + D) C = triple A B C + triple A D C := by
  first
  | simp only [triple, mapBody_add, mixed3_add_middle]

theorem triple_add_last (A B C D : ConvexBody Plane) :
    triple A B (C + D) = triple A B C + triple A B D := by
  first
  | simp only [triple, mapBody_add, mixed3_add_last]

theorem triple_smul_middle (A B C : ConvexBody Plane) {r : ℝ} (hr : 0 ≤ r) :
    triple A (r • B) C = r * triple A B C := by
  first
  | simp only [triple, mapBody_smul, mixed3_smul_middle _ _ _ hr]

theorem triple_smul_last (A B C : ConvexBody Plane) {r : ℝ} (hr : 0 ≤ r) :
    triple A B (r • C) = r * triple A B C := by
  first
  | simp only [triple, mapBody_smul, mixed3_smul_last _ _ _ hr]

theorem triple_translate_middle (A B C : ConvexBody Plane) (v : Plane) :
    triple A (translateBody v B) C = triple A B C := by
  first
  | have h := mixed3_translate (mapBody embedXY A) (mapBody embedYZ B) (mapBody embedXZ C)
      0 (embedYZ v) 0
    simpa only [triple, mapBody_translate, translateBody_zero] using h

theorem triple_translate_last (A B C : ConvexBody Plane) (v : Plane) :
    triple A B (translateBody v C) = triple A B C := by
  first
  | have h := mixed3_translate (mapBody embedXY A) (mapBody embedYZ B) (mapBody embedXZ C)
      0 0 (embedXZ v)
    simpa only [triple, mapBody_translate, translateBody_zero] using h

theorem triple_point (v : Plane) (B C : ConvexBody Plane) : triple (pointBody v) B C = 0 := by
  first
  | rw [triple, mapBody_pointBody, mixed3_point_first]

theorem triple_zero_middle (A C : ConvexBody Plane) : triple A 0 C = 0 := by
  first
  | rw [triple, mapBody_zero, mixed3_swap_first, mixed3_zero_first]

theorem triple_zero_last (A B : ConvexBody Plane) : triple A B 0 = 0 := by
  first
  | rw [triple, mapBody_zero, mixed3_swap_last, mixed3_swap_first, mixed3_zero_first]

theorem triple_sum_middle {ι : Type*} [Fintype ι] (A C : ConvexBody Plane)
    (B : ι → ConvexBody Plane) : triple A (∑ i, B i) C = ∑ i, triple A (B i) C := by
  first
  | classical
    have h (s : Finset ι) : triple A (∑ i ∈ s, B i) C = ∑ i ∈ s, triple A (B i) C := by
      first
      | induction s using Finset.induction_on with
        | empty => simp only [Finset.sum_empty, triple_zero_middle]
        | @insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, triple_add_middle, ih]
    exact h Finset.univ

theorem triple_sum_last {ι : Type*} [Fintype ι] (A B : ConvexBody Plane)
    (C : ι → ConvexBody Plane) : triple A B (∑ i, C i) = ∑ i, triple A B (C i) := by
  first
  | classical
    have h (s : Finset ι) : triple A B (∑ i ∈ s, C i) = ∑ i ∈ s, triple A B (C i) := by
      first
      | induction s using Finset.induction_on with
        | empty => simp only [Finset.sum_empty, triple_zero_last]
        | @insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, triple_add_last, ih]
    exact h Finset.univ

def AxisEquivalent (F G : ConvexBody Plane → ℝ) : Prop := AxisFunctional (fun A => F A - G A)

theorem AxisEquivalent.refl (F : ConvexBody Plane → ℝ) : AxisEquivalent F F := by
  first
  | simpa only [AxisEquivalent, sub_self] using AxisFunctional.zero

theorem AxisEquivalent.symm {F G : ConvexBody Plane → ℝ} (h : AxisEquivalent F G) :
    AxisEquivalent G F := by
  first
  | exact h.neg.congr (fun A => by ring)

theorem AxisEquivalent.trans {F G H : ConvexBody Plane → ℝ}
    (hFG : AxisEquivalent F G) (hGH : AxisEquivalent G H) : AxisEquivalent F H := by
  first
  | exact (hFG.add hGH).congr (fun A => by ring)

theorem AxisEquivalent.add {F F' G G' : ConvexBody Plane → ℝ}
    (hF : AxisEquivalent F F') (hG : AxisEquivalent G G') :
    AxisEquivalent (fun A => F A + G A) (fun A => F' A + G' A) := by
  first
  | exact (AxisFunctional.add hF hG).congr (fun A => by ring)

theorem AxisEquivalent.sum {ι : Type*} [Fintype ι]
    {F G : ι → ConvexBody Plane → ℝ} (h : ∀ i, AxisEquivalent (F i) (G i)) :
    AxisEquivalent (fun A => ∑ i, F i A) (fun A => ∑ i, G i A) := by
  first
  | change AxisFunctional (fun A => (∑ i, F i A) - ∑ i, G i A)
    apply (AxisFunctional.sum (F := fun i A => F i A - G i A) h).congr
    intro A
    exact Finset.sum_sub_distrib (s := Finset.univ) (fun i : ι => F i A) (fun i : ι => G i A)

theorem axisEquivalent_of_axisFunctional {F G : ConvexBody Plane → ℝ}
    (hF : AxisFunctional F) (hG : AxisFunctional G) : AxisEquivalent F G := hF.sub hG

theorem support_scaled_axis_pair (A : ConvexBody Plane) (v : Plane) (r : ℝ) :
    SupportGeometry.support (A : Set Plane) (normal (r • v)) +
      SupportGeometry.support (A : Set Plane) (normal (-(r • v))) =
        |r| * (SupportGeometry.support (A : Set Plane) (normal v) +
          SupportGeometry.support (A : Set Plane) (normal (-v))) := by
  first
  | have hn : -(r • v) = (-r) • v := by module
    rw [hn, support_normal_signed_smul, support_normal_signed_smul, neg_neg]
    have hsum : max r 0 + max (-r) 0 = |r| := by
      first
      | have hp := twice_positive_part r
        have hm := twice_positive_part (-r)
        rw [abs_neg] at hm
        linarith
    calc
      _ = (max r 0 + max (-r) 0) *
          (SupportGeometry.support (A : Set Plane) (normal v) +
            SupportGeometry.support (A : Set Plane) (normal (-v))) := by ring
      _ = _ := by rw [hsum]

theorem rightTriangle_axisX_eq_translate (r : ℝ) :
    ∃ v : Plane, rightTriangle r 0 = translateBody v (|r| • unitX) := by
  first
  | apply eq_translate_of_mixedArea_eq
    intro A
    have h : 2 * mixedArea volume A (rightTriangle r 0) = |r| * height A := by
      first
      | rw [rightTriangle_zero_right, mixedArea_translate_right, twice_mixedArea_segment_support]
        have he : ((r, 0) : Plane) = r • ((1, 0) : Plane) := by ext <;> simp
        rw [he, support_scaled_axis_pair]
        simpa using congrArg (|r| * ·) (support_axisY_sum A)
    rw [mixedArea_smul_right volume A unitX (abs_nonneg r)]
    rw [← twice_mixedArea_unitX A] at h
    nlinarith [h]

theorem rightTriangle_axisY_eq_translate (r : ℝ) :
    ∃ v : Plane, rightTriangle 0 r = translateBody v (|r| • unitY) := by
  first
  | apply eq_translate_of_mixedArea_eq
    intro A
    have h : 2 * mixedArea volume A (rightTriangle 0 r) = |r| * width A := by
      first
      | rw [rightTriangle_zero_left, mixedArea_translate_right, twice_mixedArea_segment_support]
        have he : ((0, r) : Plane) = r • ((0, 1) : Plane) := by ext <;> simp
        rw [he, support_scaled_axis_pair]
        simpa using congrArg (|r| * ·) (support_axisX_sum A)
    rw [mixedArea_smul_right volume A unitY (abs_nonneg r)]
    rw [← twice_mixedArea_unitY A] at h
    nlinarith [h]

theorem axisFunctional_triple_middle_triangle {b : Plane} (hb : b.1 = 0 ∨ b.2 = 0)
    (C : ConvexBody Plane) : AxisFunctional (fun A => 6 * triple A (triangleFromEdge b) C) := by
  first
  | rcases hb with hb | hb
    · have he : triangleFromEdge b = rightTriangle 0 (-b.2) := by simp [triangleFromEdge, orientation, hb]
      obtain ⟨v, hv⟩ := rightTriangle_axisY_eq_translate (-b.2)
      apply (axisFunctional_height.smul (|b.2| * width C)).congr
      intro A
      rw [he, hv, triple_translate_middle, triple_smul_middle _ _ _ (abs_nonneg _), abs_neg]
      nlinarith [congrArg (fun x : ℝ => |b.2| * x) (triple_middle_unitY A C)]
    · have he : triangleFromEdge b = rightTriangle b.1 0 := by simp [triangleFromEdge, orientation, hb]
      obtain ⟨v, hv⟩ := rightTriangle_axisX_eq_translate b.1
      apply (axisFunctional_width.smul (|b.1| * height C)).congr
      intro A
      rw [he, hv, triple_translate_middle, triple_smul_middle _ _ _ (abs_nonneg _)]
      nlinarith [congrArg (fun x : ℝ => |b.1| * x) (triple_middle_unitX A C)]

theorem axisFunctional_triple_last_triangle {c : Plane} (hc : c.1 = 0 ∨ c.2 = 0)
    (B : ConvexBody Plane) : AxisFunctional (fun A => 6 * triple A B (triangleFromEdge c)) := by
  first
  | rcases hc with hc | hc
    · have he : triangleFromEdge c = rightTriangle 0 (-c.2) := by simp [triangleFromEdge, orientation, hc]
      obtain ⟨v, hv⟩ := rightTriangle_axisY_eq_translate (-c.2)
      apply (axisFunctional_width.smul (|c.2| * width B)).congr
      intro A
      rw [he, hv, triple_translate_last, triple_smul_last _ _ _ (abs_nonneg _), abs_neg]
      nlinarith [congrArg (fun x : ℝ => |c.2| * x) (triple_last_unitY A B)]
    · have he : triangleFromEdge c = rightTriangle c.1 0 := by simp [triangleFromEdge, orientation, hc]
      obtain ⟨v, hv⟩ := rightTriangle_axisX_eq_translate c.1
      apply (axisFunctional_height.smul (|c.1| * height B)).congr
      intro A
      rw [he, hv, triple_translate_last, triple_smul_last _ _ _ (abs_nonneg _)]
      nlinarith [congrArg (fun x : ℝ => |c.1| * x) (triple_last_unitX A B)]

end VolumePolynomials.PlanarInteraction
