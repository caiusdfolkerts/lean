module

public import VolumePolynomials.CoordinateErosionBody
public import VolumePolynomials.PlanarCornerOptimizer

@[expose] public section
set_option autoImplicit false

/-! # Construction of an actual body from balanced finite edge vectors

Summing literal right triangles and removing an actual rectangle replaces
angular sorting. The resulting body has the prescribed mixed-area functional
and coordinate widths, with no nondegeneracy assumption on individual vectors.
-/

noncomputable section
open Set MeasureTheory
open scoped Pointwise BigOperators

namespace VolumePolynomials.PlanarEdges

open PlanarExtrusion PlanarMixedForm PlanarCorner OAI.Paper092

theorem rightTriangle_horizontal {r : ℝ} (hr : 0 ≤ r) :
    (rightTriangle r 0 : Set Plane) = horizontal r := by
  first
  | ext p
    constructor
    · intro hp
      have h := rightTriangle_bounds r 0 hp
      have hy' : 0 ≤ p.2 ∧ p.2 ≤ 0 := by simpa using h.2
      have hy : p.2 = 0 := le_antisymm hy'.2 hy'.1
      exact ⟨by simpa [min_eq_left hr, max_eq_right hr] using h.1, hy⟩
    · intro hp
      have hy : p.2 = 0 := hp.2
      have he : p = (p.1, 0) := by ext <;> simp [hy]
      rw [he]
      apply rightTriangle_axisX
      simpa [min_eq_left hr, max_eq_right hr] using hp.1

theorem rightTriangle_vertical {r : ℝ} (hr : 0 ≤ r) :
    (rightTriangle 0 r : Set Plane) = vertical r := by
  first
  | ext p
    constructor
    · intro hp
      have h := rightTriangle_bounds 0 r hp
      have hx' : 0 ≤ p.1 ∧ p.1 ≤ 0 := by simpa using h.1
      have hx : p.1 = 0 := le_antisymm hx'.2 hx'.1
      exact ⟨hx, by simpa [min_eq_left hr, max_eq_right hr] using h.2⟩
    · intro hp
      have hx : p.1 = 0 := hp.1
      have he : p = (0, p.2) := by ext <;> simp [hx]
      rw [he]
      apply rightTriangle_axisY
      simpa [min_eq_left hr, max_eq_right hr] using hp.2

theorem rightTriangle_axisX_mixedArea (A : ConvexBody Plane) {r : ℝ} (hr : 0 ≤ r) :
    2 * mixedArea volume A (rightTriangle r 0) = r * height A := by
  first
  | rw [rightTriangle_zero_right, mixedArea_translate_right, twice_mixedArea_segment_support]
    have h1 : ((r, 0) : Plane) = r • ((1, 0) : Plane) := by ext <;> simp
    have h2 : -((r, 0) : Plane) = r • ((-1, 0) : Plane) := by ext <;> simp
    rw [h2, h1, normal_smul, normal_smul,
      support_smul_functional _ _ hr, support_smul_functional _ _ hr, ← mul_add,
      support_axisY_sum]

theorem rightTriangle_axisY_mixedArea (A : ConvexBody Plane) {r : ℝ} (hr : 0 ≤ r) :
    2 * mixedArea volume A (rightTriangle 0 r) = r * width A := by
  first
  | rw [rightTriangle_zero_left, mixedArea_translate_right, twice_mixedArea_segment_support]
    have h1 : ((0, r) : Plane) = r • ((0, 1) : Plane) := by ext <;> simp
    have h2 : -((0, r) : Plane) = r • ((0, -1) : Plane) := by ext <;> simp
    rw [h2, h1, normal_smul, normal_smul,
      support_smul_functional _ _ hr, support_smul_functional _ _ hr, ← mul_add,
      support_axisX_sum]

theorem sum_horizontal_segments {ι : Type*} [Fintype ι]
    (K : ι → ConvexBody Plane) (y r : ι → ℝ)
    (h : ∀ i, ∃ x : ℝ, (x, y i) ∈ K i ∧ (x + r i, y i) ∈ K i) :
    ∃ x : ℝ, (x, ∑ i, y i) ∈ ∑ i, K i ∧
      (x + ∑ i, r i, ∑ i, y i) ∈ ∑ i, K i := by
  first
  | choose x hx hxr using h
    refine ⟨∑ i, x i, ?_, ?_⟩
    · apply (mem_sum_body K _).mpr
      refine ⟨fun i => (x i, y i), hx, ?_⟩
      ext <;> simp only [Prod.fst_sum, Prod.snd_sum]
    · apply (mem_sum_body K _).mpr
      refine ⟨fun i => (x i + r i, y i), hxr, ?_⟩
      ext <;> simp only [Prod.fst_sum, Prod.snd_sum, Finset.sum_add_distrib]

theorem sum_vertical_segments {ι : Type*} [Fintype ι]
    (K : ι → ConvexBody Plane) (x r : ι → ℝ)
    (h : ∀ i, ∃ y : ℝ, (x i, y) ∈ K i ∧ (x i, y + r i) ∈ K i) :
    ∃ y : ℝ, (∑ i, x i, y) ∈ ∑ i, K i ∧
      (∑ i, x i, y + ∑ i, r i) ∈ ∑ i, K i := by
  first
  | choose y hy hyr using h
    refine ⟨∑ i, y i, ?_, ?_⟩
    · apply (mem_sum_body K _).mpr
      refine ⟨fun i => (x i, y i), hy, ?_⟩
      ext <;> simp only [Prod.fst_sum, Prod.snd_sum]
    · apply (mem_sum_body K _).mpr
      refine ⟨fun i => (x i, y i + r i), hyr, ?_⟩
      ext <;> simp only [Prod.fst_sum, Prod.snd_sum, Finset.sum_add_distrib]

/-- The hypotheses are the four signed coordinate totals, not an assumed
existence theorem for polygons. The conclusion constructs an actual convex body. -/
theorem exists_body_of_balanced_edges {ι : Type*} [Fintype ι] (e : ι → Plane)
    {w h : ℝ}
    (hxp : (∑ i, max (e i).1 0) = w) (hxn : (∑ i, max (-(e i).1) 0) = w)
    (hyp : (∑ i, max (e i).2 0) = h) (hyn : (∑ i, max (-(e i).2) 0) = h) :
    ∃ Q : ConvexBody Plane, Represents Q e ∧ width Q = w ∧ height Q = h := by
  first
  | have hw : 0 ≤ w := by rw [← hxp]; positivity
    have hh : 0 ≤ h := by rw [← hyp]; positivity
    let a (i : ι) := orientation (e i) * (e i).1
    let b (i : ι) := -orientation (e i) * (e i).2
    let lx := ∑ i, min 0 (a i)
    let ux := ∑ i, max 0 (a i)
    let ly := ∑ i, min 0 (b i)
    let uy := ∑ i, max 0 (b i)
    have hbound : ∀ p ∈ triangleSum e,
        (lx ≤ p.1 ∧ p.1 ≤ ux) ∧ (ly ≤ p.2 ∧ p.2 ≤ uy) := by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := (mem_sum_body (fun i => triangleFromEdge (e i)) p).mp hp
      simp only [Prod.fst_sum, Prod.snd_sum]
      exact ⟨⟨Finset.sum_le_sum (fun i _ => (rightTriangle_bounds (a i) (b i) (hq i)).1.1),
        Finset.sum_le_sum (fun i _ => (rightTriangle_bounds (a i) (b i) (hq i)).1.2)⟩,
        ⟨Finset.sum_le_sum (fun i _ => (rightTriangle_bounds (a i) (b i) (hq i)).2.1),
        Finset.sum_le_sum (fun i _ => (rightTriangle_bounds (a i) (b i) (hq i)).2.2)⟩⟩
    have hbottom : ∃ x, (x, ly) ∈ triangleSum e ∧ (x + w, ly) ∈ triangleSum e := by
      simpa only [hxn, ly, triangleSum] using sum_horizontal_segments (fun i => triangleFromEdge (e i))
        (fun i => min 0 (b i)) (fun i => max (-(e i).1) 0)
        (fun i => (triangleFromEdge_extreme_segments (e i)).1)
    have htop : ∃ x, (x, uy) ∈ triangleSum e ∧ (x + w, uy) ∈ triangleSum e := by
      simpa only [hxp, uy, triangleSum] using sum_horizontal_segments (fun i => triangleFromEdge (e i))
        (fun i => max 0 (b i)) (fun i => max (e i).1 0)
        (fun i => (triangleFromEdge_extreme_segments (e i)).2.1)
    have hleft : ∃ y, (lx, y) ∈ triangleSum e ∧ (lx, y + h) ∈ triangleSum e := by
      simpa only [hyp, lx, triangleSum] using sum_vertical_segments (fun i => triangleFromEdge (e i))
        (fun i => min 0 (a i)) (fun i => max (e i).2 0)
        (fun i => (triangleFromEdge_extreme_segments (e i)).2.2.1)
    have hright : ∃ y, (ux, y) ∈ triangleSum e ∧ (ux, y + h) ∈ triangleSum e := by
      simpa only [hyn, ux, triangleSum] using sum_vertical_segments (fun i => triangleFromEdge (e i))
        (fun i => max 0 (a i)) (fun i => max (-(e i).2) 0)
        (fun i => (triangleFromEdge_extreme_segments (e i)).2.2.2)
    obtain ⟨Q, hQ⟩ := exists_rectangle_remainder (triangleSum e) hw hh hbound
      hbottom htop hleft hright
    have hbody : triangleSum e = (Q + rightTriangle 0 h) + rightTriangle w 0 := by
      apply ConvexBody.ext
      change (triangleSum e : Set Plane) = ((Q : Set Plane) + (rightTriangle 0 h : Set Plane)) + _
      rwa [rightTriangle_horizontal hw, rightTriangle_vertical hh]
    have hvarx : (∑ i, |(e i).1|) = 2 * w := by
      have hi (x : ℝ) : |x| = max x 0 + max (-x) 0 := by
        rcases le_total 0 x with hx | hx <;> simp [abs_of_nonneg, abs_of_nonpos, hx,
          max_eq_left, max_eq_right, neg_nonpos, neg_nonneg]
      simp_rw [hi]
      rw [Finset.sum_add_distrib, hxp, hxn]
      ring
    have hvary : (∑ i, |(e i).2|) = 2 * h := by
      have hi (x : ℝ) : |x| = max x 0 + max (-x) 0 := by
        rcases le_total 0 x with hx | hx <;> simp [abs_of_nonneg, abs_of_nonpos, hx,
          max_eq_left, max_eq_right, neg_nonpos, neg_nonneg]
      simp_rw [hi]
      rw [Finset.sum_add_distrib, hyp, hyn]
      ring
    refine ⟨Q, ?_, ?_, ?_⟩
    · intro A
      have ht : 2 * mixedArea volume A (triangleSum e) =
          (∑ i, SupportGeometry.support (A : Set Plane) (normal (e i))) +
            h * width A + w * height A := by
        rw [triangleSum, mixedArea_sum_right, Finset.mul_sum]
        simp_rw [triangleFromEdge_mixedArea]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        have hx := support_sum_balanced A (fun i => -(e i).2) (0, 1) h hyn
          (by simpa using hyp)
        have hy := support_sum_balanced A (fun i => -(e i).1) (1, 0) w hxn
          (by simpa using hxp)
        have heX (i : ι) : (-(e i).2) • ((0, 1) : Plane) = (0, -(e i).2) := by ext <;> simp
        have heY (i : ι) : (-(e i).1) • ((1, 0) : Plane) = (-(e i).1, 0) := by ext <;> simp
        simp only [heX, Prod.neg_mk, neg_zero, support_axisX_sum] at hx
        simp only [heY, Prod.neg_mk, neg_zero, support_axisY_sum] at hy
        rw [hx, hy]
      rw [hbody, mixedArea_add_right, mixedArea_add_right] at ht
      nlinarith [rightTriangle_axisX_mixedArea A hw, rightTriangle_axisY_mixedArea A hh]
    · have ht := triangleSum_width e
      rw [hbody, width_add, width_add, rightTriangle_width, rightTriangle_width,
        abs_zero, abs_of_nonneg hw, hvarx] at ht
      linarith
    · have ht := triangleSum_height e
      rw [hbody, height_add, height_add, rightTriangle_height, rightTriangle_height,
        abs_zero, abs_of_nonneg hh, hvary] at ht
      linarith

end VolumePolynomials.PlanarEdges
