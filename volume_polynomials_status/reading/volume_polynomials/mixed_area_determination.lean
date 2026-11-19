module

public import VolumePolynomials.CornerAreaIdentity

@[expose] public section
set_option autoImplicit false

/-! # Mixed area determines an actual planar body up to translation

The proof uses the already computed right triangles as test bodies. It recovers
each support value from the mixed area and four coordinate support values.
Thus the triangle decomposition is an actual Minkowski identity, available
inside higher-dimensional mixed-volume expressions.
-/

noncomputable section
open Set MeasureTheory
open scoped Pointwise BigOperators

namespace VolumePolynomials.PlanarEdges

open PlanarExtrusion PlanarMixedForm PlanarCorner OAI.Paper092

theorem support_translateBody (P : ConvexBody Plane) (v : Plane) (l : Plane →L[ℝ] ℝ) :
    SupportGeometry.support (translateBody v P : Set Plane) l =
      l v + SupportGeometry.support (P : Set Plane) l := by
  first
  | change SupportGeometry.support ((pointBody v : Set Plane) + (P : Set Plane)) l = _
    rw [SupportGeometry.support_add (pointBody v).isCompact (pointBody v).nonempty
      P.isCompact P.nonempty, support_pointBody]

theorem positive_part_sub_negative_part (x : ℝ) : max x 0 - max (-x) 0 = x := by
  first
  | rcases le_total 0 x with hx | hx
    · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
      ring
    · rw [max_eq_right hx, max_eq_left (neg_nonneg.mpr hx)]
      ring

theorem support_axis_difference (P Q : ConvexBody Plane) (v : Plane) (r d : ℝ)
    (hp : SupportGeometry.support (P : Set Plane) (normal v) -
      SupportGeometry.support (Q : Set Plane) (normal v) = d)
    (hn : SupportGeometry.support (P : Set Plane) (normal (-v)) -
      SupportGeometry.support (Q : Set Plane) (normal (-v)) = -d) :
    SupportGeometry.support (P : Set Plane) (normal (r • v)) -
      SupportGeometry.support (Q : Set Plane) (normal (r • v)) = r * d := by
  first
  | rw [support_normal_signed_smul, support_normal_signed_smul]
    calc
      _ = max r 0 *
          (SupportGeometry.support (P : Set Plane) (normal v) -
            SupportGeometry.support (Q : Set Plane) (normal v)) +
          max (-r) 0 *
          (SupportGeometry.support (P : Set Plane) (normal (-v)) -
            SupportGeometry.support (Q : Set Plane) (normal (-v))) := by ring
      _ = (max r 0 - max (-r) 0) * d := by rw [hp, hn]; ring
      _ = r * d := by rw [positive_part_sub_negative_part]

/-- Equality of all literal mixed areas gives equality up to an actual
translation; no uniqueness theorem for surface-area measures is assumed. -/
theorem eq_translate_of_mixedArea_eq (P Q : ConvexBody Plane)
    (h : ∀ A : ConvexBody Plane, mixedArea volume A P = mixedArea volume A Q) :
    ∃ v : Plane, P = translateBody v Q := by
  first
  | let dx : ℝ := SupportGeometry.support (P : Set Plane) (normal (0, 1)) -
      SupportGeometry.support (Q : Set Plane) (normal (0, 1))
    let dy : ℝ := SupportGeometry.support (P : Set Plane) (normal (1, 0)) -
      SupportGeometry.support (Q : Set Plane) (normal (1, 0))
    have hw : width P = width Q := by
      have hs := h unitY
      rw [mixedArea_symm volume unitY P, mixedArea_symm volume unitY Q] at hs
      linarith [twice_mixedArea_unitY P, twice_mixedArea_unitY Q]
    have hh : height P = height Q := by
      have hs := h unitX
      rw [mixedArea_symm volume unitX P, mixedArea_symm volume unitX Q] at hs
      linarith [twice_mixedArea_unitX P, twice_mixedArea_unitX Q]
    have hnx : SupportGeometry.support (P : Set Plane) (normal (0, -1)) -
        SupportGeometry.support (Q : Set Plane) (normal (0, -1)) = -dx := by
      dsimp only [dx]
      linarith [support_axisX_sum P, support_axisX_sum Q]
    have hny : SupportGeometry.support (P : Set Plane) (normal (-1, 0)) -
        SupportGeometry.support (Q : Set Plane) (normal (-1, 0)) = -dy := by
      dsimp only [dy]
      linarith [support_axisY_sum P, support_axisY_sum Q]
    have hx (r : ℝ) : SupportGeometry.support (P : Set Plane) (normal (0, r)) -
        SupportGeometry.support (Q : Set Plane) (normal (0, r)) = r * dx := by
      have hn : -((0, 1) : Plane) = (0, -1) := by ext <;> simp
      have he : r • ((0, 1) : Plane) = (0, r) := by ext <;> simp
      simpa only [hn, he] using support_axis_difference P Q (0, 1) r dx rfl (by rwa [hn])
    have hy (r : ℝ) : SupportGeometry.support (P : Set Plane) (normal (r, 0)) -
        SupportGeometry.support (Q : Set Plane) (normal (r, 0)) = r * dy := by
      have hn : -((1, 0) : Plane) = (-1, 0) := by ext <;> simp
      have he : r • ((1, 0) : Plane) = (r, 0) := by ext <;> simp
      simpa only [hn, he] using support_axis_difference P Q (1, 0) r dy rfl (by rwa [hn])
    have hall (e : Plane) : SupportGeometry.support (P : Set Plane) (normal e) -
        SupportGeometry.support (Q : Set Plane) (normal e) = e.2 * dx + e.1 * dy := by
      have ht := h (triangleFromEdge e)
      rw [mixedArea_symm volume (triangleFromEdge e) P,
        mixedArea_symm volume (triangleFromEdge e) Q] at ht
      have hp := triangleFromEdge_mixedArea e P
      have hq := triangleFromEdge_mixedArea e Q
      linarith [hx (-e.2), hy (-e.1)]
    refine ⟨(dx, -dy), ConvexBody.ext ?_⟩
    apply SupportGeometry.eq_of_support_eq P.isCompact P.nonempty P.convex
      (translateBody (dx, -dy) Q).isCompact (translateBody (dx, -dy) Q).nonempty
      (translateBody (dx, -dy) Q).convex
    intro l
    have he := hall (edgeOfFunctional l)
    rw [normal_edgeOfFunctional] at he
    rw [support_translateBody, ← normal_edgeOfFunctional l, normal_apply]
    rw [normal_edgeOfFunctional l]
    linarith

def boundingRectangle (P : ConvexBody Plane) : ConvexBody Plane :=
  width P • unitX + height P • unitY

theorem boundingRectangle_mixedArea (P A : ConvexBody Plane) :
    2 * mixedArea volume A (boundingRectangle P) =
      width P * height A + height P * width A := by
  first
  | rw [boundingRectangle, mixedArea_add_right,
      mixedArea_smul_right volume A unitX (show 0 ≤ width P from measureReal_nonneg),
      mixedArea_smul_right volume A unitY (show 0 ≤ height P from measureReal_nonneg)]
    rw [← twice_mixedArea_unitX A, ← twice_mixedArea_unitY A]
    ring

/-- Every finite facet representation yields an actual Minkowski decomposition
into the explicit right triangles, with only a harmless translation. -/
theorem Represents.triangleSum_eq_translate {ι : Type*} [Fintype ι]
    {P : ConvexBody Plane} {e : ι → Plane} (h : Represents P e) :
    ∃ v : Plane, triangleSum e = translateBody v (P + boundingRectangle P) := by
  first
  | apply eq_translate_of_mixedArea_eq
    intro A
    have ht := h.triangleSum_functional A
    have hr := boundingRectangle_mixedArea P A
    rw [mixedArea_add_right]
    linarith

end VolumePolynomials.PlanarEdges
