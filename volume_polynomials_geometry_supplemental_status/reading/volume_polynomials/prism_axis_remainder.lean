module

public import VolumePolynomials.RoofInteractionAlgebra

@[expose] public section
set_option autoImplicit false

/-! # Identification of the non-axis part of the actual triple mixed volume -/

noncomputable section
open Set MeasureTheory Matrix
open scoped BigOperators Pointwise

namespace VolumePolynomials.PlanarInteraction

open PlanarExtrusion PlanarMixedForm PlanarCorner PlanarEdges OAI.Paper092

theorem support_embedXY (A : ConvexBody Plane) (l : Space →L[ℝ] ℝ) :
    SupportGeometry.support (mapBody embedXY A : Set Space) l =
      SupportGeometry.support (A : Set Plane) (l.comp embedXY) := by
  first
  | unfold SupportGeometry.support
    rw [coe_mapBody, Set.image_image]
    rfl

theorem normal_upperRoofEdge (a b c d : ℝ) :
    normal (upperRoofEdge a b c d) =
      (|a| * |c|) • ((upperPrismNormal a b c d).comp embedXY) := by
  first
  | apply ContinuousLinearMap.ext
    intro p
    change (|a| * |c| * max d 0 / c) * p.1 - (-|a| * |c| * max b 0 / a) * p.2 =
      (|a| * |c|) * (0 + (max d 0 / c) * p.1 + (max b 0 / a) * p.2)
    ring

theorem normal_lowerRoofEdge (a b c d : ℝ) :
    normal (lowerRoofEdge a b c d) =
      (|a| * |c|) • ((lowerPrismNormal a b c d).comp embedXY) := by
  first
  | apply ContinuousLinearMap.ext
    intro p
    change (-|a| * |c| * min d 0 / c) * p.1 - (|a| * |c| * min b 0 / a) * p.2 =
      (|a| * |c|) * (-(0 : ℝ) - (min d 0 / c) * p.1 - (min b 0 / a) * p.2)
    ring

theorem prism_roof_support {a b c d : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (A : ConvexBody Plane) :
    prismWeight a b c d ha hb hc 4 *
        SupportGeometry.support (A : Set Plane) ((prismNormals a b c d 4).comp embedXY) =
      SupportGeometry.support (A : Set Plane) (normal (upperRoofEdge a b c d)) ∧
    prismWeight a b c d ha hb hc 5 *
        SupportGeometry.support (A : Set Plane) ((prismNormals a b c d 5).comp embedXY) =
      SupportGeometry.support (A : Set Plane) (normal (lowerRoofEdge a b c d)) := by
  first
  | have hH := prismHalfHeight_positive (d := d) hb
    have hw := prism_roof_weights ha hb hc hd
    have hsmul (r : ℝ) (l : Space →L[ℝ] ℝ) : (r • l).comp embedXY = r • (l.comp embedXY) := by
      first
      | apply ContinuousLinearMap.ext
        intro p
        rfl
    constructor
    · change prismWeight a b c d ha hb hc 4 *
        SupportGeometry.support (A : Set Plane)
          (((prismHalfHeight b d)⁻¹ • upperPrismNormal a b c d).comp embedXY) = _
      rw [hsmul, support_smul_functional _ _ (inv_nonneg.mpr hH.le), normal_upperRoofEdge,
        support_smul_functional _ _ (mul_nonneg (abs_nonneg _) (abs_nonneg _))]
      calc
        _ = (prismWeight a b c d ha hb hc 4 / prismHalfHeight b d) *
          SupportGeometry.support (A : Set Plane) ((upperPrismNormal a b c d).comp embedXY) := by ring
        _ = _ := by rw [hw.1]
    · change prismWeight a b c d ha hb hc 5 *
        SupportGeometry.support (A : Set Plane)
          (((prismHalfHeight b d)⁻¹ • lowerPrismNormal a b c d).comp embedXY) = _
      rw [hsmul, support_smul_functional _ _ (inv_nonneg.mpr hH.le), normal_lowerRoofEdge,
        support_smul_functional _ _ (mul_nonneg (abs_nonneg _) (abs_nonneg _))]
      calc
        _ = (prismWeight a b c d ha hb hc 5 / prismHalfHeight b d) *
          SupportGeometry.support (A : Set Plane) ((lowerPrismNormal a b c d).comp embedXY) := by ring
        _ = _ := by rw [hw.2]

theorem prism_axis_remainder {a b c d : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    AxisEquivalent (fun A => 3 * mixed3 (mapBody embedXY A)
      (trianglePlaneSum a b c d) (trianglePlaneSum a b c d))
      (fun A => SupportGeometry.support (A : Set Plane) (normal (upperRoofEdge a b c d)) +
        SupportGeometry.support (A : Set Plane) (normal (lowerRoofEdge a b c d))) := by
  first
  | let index (i : Fin 4) : Fin 6 := ⟨i.val, by omega⟩
    let F (i : Fin 4) (A : ConvexBody Plane) := prismWeight a b c d ha hb hc (index i) *
      SupportGeometry.support (A : Set Plane) ((prismNormals a b c d (index i)).comp embedXY)
    have hF (i : Fin 4) : AxisFunctional (F i) := by
      first
      | let l := (prismNormals a b c d (index i)).comp embedXY
        have he : (edgeOfFunctional l).1 = 0 ∨ (edgeOfFunctional l).2 = 0 := by
          first
          | fin_cases i <;> simp [l, index, prismNormals, edgeOfFunctional, embedXY,
              zCoord, xCoord, yCoord]
        have hs := axisFunctional_support_normal he
        simp only [normal_edgeOfFunctional] at hs
        exact hs.smul (prismWeight a b c d ha hb hc (index i))
    apply (AxisFunctional.sum hF).congr
    intro A
    have h := prism_first_variation ha hb hc hd (mapBody embedXY A)
    simp only [support_embedXY] at h
    let G (i : Fin 6) : ℝ := prismWeight a b c d ha hb hc i *
      SupportGeometry.support (A : Set Plane) ((prismNormals a b c d i).comp embedXY)
    change 3 * mixed3 (mapBody embedXY A) (trianglePlaneSum a b c d)
      (trianglePlaneSum a b c d) = ∑ i, G i at h
    have hroof := prism_roof_support ha hb hc hd A
    change G 4 = SupportGeometry.support (A : Set Plane) (normal (upperRoofEdge a b c d)) ∧
      G 5 = SupportGeometry.support (A : Set Plane) (normal (lowerRoofEdge a b c d)) at hroof
    have hsum6 : (∑ i, G i) = G 0 + (G 1 + (G 2 + (G 3 + (G 4 + G 5)))) := by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] <;> rfl
    have hsum4 : (∑ i, F i A) = G 0 + (G 1 + (G 2 + G 3)) := by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] <;> rfl
    rw [hsum6, hroof.1, hroof.2] at h
    change (∑ i, F i A) = _
    rw [hsum4]
    linarith

theorem triple_sum_axis_difference (B C : ConvexBody Plane) :
    AxisEquivalent (fun A => 6 * triple A B C)
      (fun A => 3 * mixed3 (mapBody embedXY A)
        (mapBody embedYZ B + mapBody embedXZ C) (mapBody embedYZ B + mapBody embedXZ C)) := by
  first
  | have h := ((axisFunctional_width.smul (-volume.real (B : Set Plane))).add
      (axisFunctional_height.smul (-volume.real (C : Set Plane))))
    apply h.congr
    intro A
    dsimp only
    rw [mixed3_add_middle, mixed3_add_last, mixed3_add_last,
      mixed3_swap_last (mapBody embedXY A) (mapBody embedXZ C) (mapBody embedYZ B)]
    have hB := repeated_XY_YZ A B
    have hC := repeated_XY_XZ A C
    dsimp only [triple]
    linarith

/-- For a pair of actual right triangles, the sole non-axis contribution is
exactly the product vector in (4.11). The remaining terms are proved to lie
in the four-dimensional coordinate support space. -/
theorem triangle_pair_axis_equivalent (b c : Plane) :
    AxisEquivalent (fun A => 6 * triple A (triangleFromEdge b) (triangleFromEdge c))
      (fun A => SupportGeometry.support (A : Set Plane) (normal (interactionEdge b c))) := by
  first
  | by_cases hb : b.1 = 0 ∨ b.2 = 0
    · exact axisEquivalent_of_axisFunctional
        (axisFunctional_triple_middle_triangle hb (triangleFromEdge c))
        (axisFunctional_support_normal (interactionEdge_axis_left hb))
    by_cases hc : c.1 = 0 ∨ c.2 = 0
    · exact axisEquivalent_of_axisFunctional
        (axisFunctional_triple_last_triangle hc (triangleFromEdge b))
        (axisFunctional_support_normal (interactionEdge_axis_right hc))
    have hb1 : b.1 ≠ 0 := fun h => hb (Or.inl h)
    have hb2 : b.2 ≠ 0 := fun h => hb (Or.inr h)
    have hc1 : c.1 ≠ 0 := fun h => hc (Or.inl h)
    have hc2 : c.2 ≠ 0 := fun h => hc (Or.inr h)
    have hab : orientation b * b.1 ≠ 0 := mul_ne_zero (orientation_ne_zero b) hb1
    have hbb : -orientation b * b.2 ≠ 0 := mul_ne_zero (neg_ne_zero.mpr (orientation_ne_zero b)) hb2
    have hac : orientation c * c.1 ≠ 0 := mul_ne_zero (orientation_ne_zero c) hc1
    have hbc : -orientation c * c.2 ≠ 0 := mul_ne_zero (neg_ne_zero.mpr (orientation_ne_zero c)) hc2
    have hp := prism_axis_remainder hab hbb hac hbc
    rw [upperRoofEdge_oriented hb1 hb2 hc1 hc2,
      lowerRoofEdge_oriented hb1 hb2 hc1 hc2] at hp
    exact ((triple_sum_axis_difference (triangleFromEdge b) (triangleFromEdge c)).trans hp).trans
      (roof_product_axis_equivalent hb1 hc1)

end VolumePolynomials.PlanarInteraction
