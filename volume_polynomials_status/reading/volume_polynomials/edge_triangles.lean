module

public import VolumePolynomials.PlanarSupportWidth

@[expose] public section
set_option autoImplicit false

/-! # A literal right triangle for each oriented edge

Axis vectors give degenerate triangles, namely actual segments. Every vector
has the same three-term support formula. Consequently no sorting of edge
directions is needed in the finite corner calculus.
-/

noncomputable section
open Set MeasureTheory
open scoped Pointwise BigOperators

namespace VolumePolynomials.PlanarEdges

open PlanarExtrusion PlanarMixedForm PlanarCorner OAI.Paper092

def orientation (e : Plane) : ℝ := if 0 ≤ e.1 * e.2 then 1 else -1

theorem abs_orientation (e : Plane) : |orientation e| = 1 := by
  first
  | unfold orientation
    split_ifs <;> norm_num

theorem orientation_ne_zero (e : Plane) : orientation e ≠ 0 := by
  first
  | intro h
    have h' := abs_orientation e
    rw [h, abs_zero] at h'
    norm_num at h'

theorem orientation_mul_product (e : Plane) :
    orientation e * (e.1 * e.2) = |e.1 * e.2| := by
  first
  | unfold orientation
    split_ifs with h
    · rw [one_mul, abs_of_nonneg h]
    · rw [neg_one_mul, abs_of_neg (lt_of_not_ge h)]

def triangleFromEdge (e : Plane) : ConvexBody Plane :=
  rightTriangle (orientation e * e.1) (-orientation e * e.2)

@[simp] theorem triangleFromEdge_width (e : Plane) : width (triangleFromEdge e) = |e.1| := by
  first
  | rw [triangleFromEdge, rightTriangle_width, abs_mul, abs_orientation, one_mul]

@[simp] theorem triangleFromEdge_height (e : Plane) : height (triangleFromEdge e) = |e.2| := by
  first
  | rw [triangleFromEdge, rightTriangle_height, abs_mul, abs_neg, abs_orientation, one_mul]

theorem triangleFromEdge_finiteHull (e : Plane) :
    PolytopeGeometry.IsFiniteHull (triangleFromEdge e : Set Plane) :=
  rightTriangle_finiteHull _ _

theorem triangleFromEdge_mixedArea (e : Plane) (A : ConvexBody Plane) :
    2 * mixedArea volume A (triangleFromEdge e) =
      SupportGeometry.support (A : Set Plane) (normal e) +
      SupportGeometry.support (A : Set Plane) (normal (0, -e.2)) +
      SupportGeometry.support (A : Set Plane) (normal (-e.1, 0)) := by
  first
  | rcases e with ⟨x, y⟩
    by_cases hx : x = 0
    · subst x
      have h := twice_mixedArea_segment_support A (0, -y)
      simp only [triangleFromEdge, orientation, zero_mul, le_refl, if_pos, one_mul,
        neg_one_mul, rightTriangle_zero_left, mixedArea_translate_right,
        neg_zero, normal_zero, normal_pair_zero, support_zero, add_zero]
      simpa only [Prod.neg_mk, neg_zero, neg_neg, add_comm] using h
    by_cases hy : y = 0
    · subst y
      have h := twice_mixedArea_segment_support A (x, 0)
      simp only [triangleFromEdge, orientation, mul_zero, le_refl, if_pos, one_mul,
        rightTriangle_zero_right, mixedArea_translate_right,
        neg_zero, normal_zero, normal_pair_zero, support_zero, add_zero]
      simpa only [Prod.neg_mk, neg_zero] using h
    let k := orientation (x, y)
    have hk : k ≠ 0 := orientation_ne_zero _
    have ha : k * x ≠ 0 := mul_ne_zero hk hx
    have hb : -k * y ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hk) hy
    have hab : |(k * x) * (-k * y)| = |x * y| := by
      first
      | simp only [abs_mul, abs_neg, show |k| = 1 from abs_orientation _, one_mul]
    have hdiva : |(k * x) * (-k * y)| / (k * x) = y := by
      first
      | apply (div_eq_iff ha).mpr
        rw [hab]
        calc
          |x * y| = k * (x * y) := (orientation_mul_product (x, y)).symm
          _ = y * (k * x) := by ring
    have hdivb : |(k * x) * (-k * y)| / (-k * y) = -x := by
      first
      | apply (div_eq_iff hb).mpr
        rw [hab]
        calc
          |x * y| = k * (x * y) := (orientation_mul_product (x, y)).symm
          _ = -x * (-k * y) := by ring
    have h := rightTriangle_mixedArea (k * x) (-k * y) ha hb A
    rw [hdiva, hdivb, neg_neg] at h
    change 2 * mixedArea volume A (triangleFromEdge (x, y)) = _ at h
    linarith

def edgeTriple (e : Plane) : Fin 3 → Plane := ![e, (0, -e.2), (-e.1, 0)]

theorem triangleFromEdge_represents (e : Plane) : Represents (triangleFromEdge e) (edgeTriple e) := by
  first
  | intro A
    simpa only [edgeTriple, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
      Matrix.cons_val_succ, add_zero, add_assoc] using triangleFromEdge_mixedArea e A

theorem positive_negative_parts (x : ℝ) : max x 0 + max (-x) 0 = |x| := by
  first
  | rcases le_total 0 x with h | h
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), abs_of_nonneg h, add_zero]
    · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h), abs_of_nonpos h, zero_add]

theorem hinge_kernel_identity (u v : ℝ) :
    max 0 (max u v) + max 0 (-u) + max 0 (-v) =
      |u| + |v| - min (max u 0) (max v 0) := by
  first
  | have hm : max 0 (max u v) = max (max u 0) (max v 0) := by
      first
      | simp only [max_assoc, max_left_comm, max_comm, max_self]
    rw [hm, max_comm 0 (-u), max_comm 0 (-v)]
    linarith [max_add_min (max u 0) (max v 0), positive_negative_parts u,
      positive_negative_parts v]

def pairKernel (e f : Plane) : ℝ :=
  min (max (orientation e * e.1 * f.2) 0) (max (orientation e * e.2 * f.1) 0)

theorem pairKernel_nonnegative (e f : Plane) : 0 ≤ pairKernel e f :=
  le_min (le_max_right _ _) (le_max_right _ _)

theorem triangleFromEdge_support (e f : Plane) :
    SupportGeometry.support (triangleFromEdge e : Set Plane) (normal f) =
      max 0 (max (orientation e * e.1 * f.2) (orientation e * e.2 * f.1)) := by
  first
  | rw [triangleFromEdge, rightTriangle_support]
    simp only [normal_apply, mul_one, mul_zero, zero_sub, sub_zero]
    congr 2 <;> ring

theorem triangle_pair_mixedArea (e f : Plane) :
    2 * mixedArea volume (triangleFromEdge e) (triangleFromEdge f) =
      |e.1| * |f.2| + |e.2| * |f.1| - pairKernel e f := by
  first
  | let u := orientation e * e.1 * f.2
    let v := orientation e * e.2 * f.1
    have h0 : SupportGeometry.support (triangleFromEdge e : Set Plane) (normal f) =
        max 0 (max u v) := triangleFromEdge_support e f
    have h1 : SupportGeometry.support (triangleFromEdge e : Set Plane) (normal (0, -f.2)) =
        max 0 (-u) := by
      first
      | rw [triangleFromEdge_support]
        simp only [u, mul_zero, mul_neg, max_assoc, max_comm, max_left_comm, max_self]
        exact max_eq_right (le_max_left _ _)
    have h2 : SupportGeometry.support (triangleFromEdge e : Set Plane) (normal (-f.1, 0)) =
        max 0 (-v) := by
      first
      | rw [triangleFromEdge_support]
        simp only [v, mul_zero, mul_neg, max_assoc, max_comm, max_left_comm, max_self]
        exact max_eq_right (le_max_left _ _)
    have hu : |u| = |e.1| * |f.2| := by simp only [u, abs_mul, abs_orientation, one_mul]
    have hv : |v| = |e.2| * |f.1| := by simp only [v, abs_mul, abs_orientation, one_mul]
    rw [triangleFromEdge_mixedArea, h0, h1, h2, hinge_kernel_identity, hu, hv]
    rfl

theorem positive_parts_min (u v : ℝ) :
    min (max u 0) (max v 0) =
      if 0 < u ∧ 0 < v then min |u| |v| else 0 := by
  first
  | by_cases h : 0 < u ∧ 0 < v
    · rw [if_pos h, max_eq_left h.1.le, max_eq_left h.2.le,
        abs_of_pos h.1, abs_of_pos h.2]
    · rw [if_neg h]
      rcases not_and_or.mp h with hu | hv
      · rw [max_eq_right (le_of_not_gt hu), min_eq_left (le_max_right _ _)]
      · rw [max_eq_right (le_of_not_gt hv), min_eq_right (le_max_right _ _)]

theorem positive_cross_iff (e f : Plane) :
    (0 < orientation e * e.1 * f.2 ∧ 0 < orientation e * e.2 * f.1) ↔
      (0 < e.1 * f.1 ∧ 0 < e.2 * f.2) := by
  first
  | by_cases hx : e.1 = 0
    · simp [hx]
    by_cases hy : e.2 = 0
    · simp [hy]
    have hprod : 0 < |e.1 * e.2| := abs_pos.mpr (mul_ne_zero hx hy)
    have hfirst : (orientation e * e.1 * f.2) * e.2 ^ 2 =
        |e.1 * e.2| * (e.2 * f.2) := by
      first
      | calc
          _ = (orientation e * (e.1 * e.2)) * (e.2 * f.2) := by ring
          _ = _ := by rw [orientation_mul_product]
    have hsecond : (orientation e * e.2 * f.1) * e.1 ^ 2 =
        |e.1 * e.2| * (e.1 * f.1) := by
      first
      | calc
          _ = (orientation e * (e.1 * e.2)) * (e.1 * f.1) := by ring
          _ = _ := by rw [orientation_mul_product]
    have h₁ : (0 < orientation e * e.1 * f.2) ↔ 0 < e.2 * f.2 := by
      first
      | rw [← mul_pos_iff_of_pos_right (sq_pos_of_ne_zero hy), hfirst,
          mul_pos_iff_of_pos_left hprod]
    have h₂ : (0 < orientation e * e.2 * f.1) ↔ 0 < e.1 * f.1 := by
      first
      | rw [← mul_pos_iff_of_pos_right (sq_pos_of_ne_zero hx), hsecond,
          mul_pos_iff_of_pos_left hprod]
    rw [h₁, h₂, and_comm]

/-- Exactly the same-corner minimum appearing in the paper. Axis vectors
contribute zero automatically. -/
theorem pairKernel_eq_min (e f : Plane) :
    pairKernel e f = if 0 < e.1 * f.1 ∧ 0 < e.2 * f.2 then
      min (|e.1| * |f.2|) (|e.2| * |f.1|) else 0 := by
  first
  | rw [pairKernel, positive_parts_min]
    simp only [positive_cross_iff, abs_mul, abs_orientation, one_mul]

theorem pairKernel_symmetric (e f : Plane) : pairKernel e f = pairKernel f e := by
  first
  | rw [pairKernel_eq_min, pairKernel_eq_min]
    simp only [mul_comm, min_comm]

end VolumePolynomials.PlanarEdges
