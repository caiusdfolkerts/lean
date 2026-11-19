module

public import VolumePolynomials.EdgeTriangles

@[expose] public section
set_option autoImplicit false

/-! # Exact corner area identities from actual right triangles

Each vector is replaced by a literal right triangle. Summing their three-term
mixed-area formulas and using the proved balance and width identities supplies
the exact area and mixed-area corner formulas. No shoelace formula, angular
sorting, or polygon reconstruction is assumed.
-/

noncomputable section
open Set MeasureTheory
open scoped Pointwise BigOperators

namespace VolumePolynomials.PlanarEdges

open PlanarExtrusion PlanarMixedForm PlanarCorner OAI.Paper092

@[simp] theorem normal_smul (r : ℝ) (e : Plane) : normal (r • e) = r • normal e := by
  first
  | apply ContinuousLinearMap.ext
    intro x
    simp only [normal_apply, Prod.smul_fst, Prod.smul_snd,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring

theorem support_normal_signed_smul (P : ConvexBody Plane) (r : ℝ) (e : Plane) :
    SupportGeometry.support (P : Set Plane) (normal (r • e)) =
      max r 0 * SupportGeometry.support (P : Set Plane) (normal e) +
        max (-r) 0 * SupportGeometry.support (P : Set Plane) (normal (-e)) := by
  first
  | rcases le_total 0 r with hr | hr
    · rw [normal_smul, support_smul_functional _ _ hr, max_eq_left hr,
        max_eq_right (neg_nonpos.mpr hr), zero_mul, add_zero]
    · have he : r • e = (-r) • (-e) := by module
      rw [he, normal_smul, support_smul_functional _ _ (neg_nonneg.mpr hr),
        max_eq_right hr, max_eq_left (neg_nonneg.mpr hr), zero_mul, zero_add]

theorem support_sum_balanced {ι : Type*} [Fintype ι]
    (A : ConvexBody Plane) (r : ι → ℝ) (v : Plane) (c : ℝ)
    (hp : (∑ i, max (r i) 0) = c) (hn : (∑ i, max (-r i) 0) = c) :
    (∑ i, SupportGeometry.support (A : Set Plane) (normal (r i • v))) =
      c * (SupportGeometry.support (A : Set Plane) (normal v) +
        SupportGeometry.support (A : Set Plane) (normal (-v))) := by
  first
  | simp_rw [support_normal_signed_smul]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, hp, hn]
    ring

theorem width_sum {ι : Type*} [Fintype ι] (K : ι → ConvexBody Plane) :
    width (∑ i, K i) = ∑ i, width (K i) := by
  first
  | calc
      width (∑ i, K i) = 2 * mixedArea volume (∑ i, K i) unitY :=
        (twice_mixedArea_unitY _).symm
      _ = 2 * ∑ i, mixedArea volume (K i) unitY := by rw [mixedArea_sum_left]
      _ = ∑ i, width (K i) := by
        first
        | rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun i _ => twice_mixedArea_unitY (K i))

theorem height_sum {ι : Type*} [Fintype ι] (K : ι → ConvexBody Plane) :
    height (∑ i, K i) = ∑ i, height (K i) := by
  first
  | calc
      height (∑ i, K i) = 2 * mixedArea volume (∑ i, K i) unitX :=
        (twice_mixedArea_unitX _).symm
      _ = 2 * ∑ i, mixedArea volume (K i) unitX := by rw [mixedArea_sum_left]
      _ = ∑ i, height (K i) := by
        first
        | rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun i _ => twice_mixedArea_unitX (K i))

def triangleSum {ι : Type*} [Fintype ι] (e : ι → Plane) : ConvexBody Plane :=
  ∑ i, triangleFromEdge (e i)

theorem triangleSum_width {ι : Type*} [Fintype ι] (e : ι → Plane) :
    width (triangleSum e) = ∑ i, |(e i).1| := by
  first
  | simp only [triangleSum, width_sum, triangleFromEdge_width]

theorem triangleSum_height {ι : Type*} [Fintype ι] (e : ι → Plane) :
    height (triangleSum e) = ∑ i, |(e i).2| := by
  first
  | simp only [triangleSum, height_sum, triangleFromEdge_height]

theorem Represents.axis_correction_x {ι : Type*} [Fintype ι]
    {P : ConvexBody Plane} {e : ι → Plane} (h : Represents P e) (A : ConvexBody Plane) :
    (∑ i, SupportGeometry.support (A : Set Plane) (normal (0, -(e i).2))) =
      height P * width A := by
  first
  | have hp := h.signed_variation
    have hsum := support_sum_balanced A (fun i => -(e i).2) (0, 1) (height P)
      hp.2.2.2 (by simpa only [neg_neg] using hp.2.1)
    have he (i : ι) : (-(e i).2) • ((0, 1) : Plane) = (0, -(e i).2) := by
      first
      | ext <;> simp
    simp only [he, Prod.neg_mk, neg_zero, support_axisX_sum] at hsum
    exact hsum

theorem Represents.axis_correction_y {ι : Type*} [Fintype ι]
    {P : ConvexBody Plane} {e : ι → Plane} (h : Represents P e) (A : ConvexBody Plane) :
    (∑ i, SupportGeometry.support (A : Set Plane) (normal (-(e i).1, 0))) =
      width P * height A := by
  first
  | have hp := h.signed_variation
    have hsum := support_sum_balanced A (fun i => -(e i).1) (1, 0) (width P)
      hp.2.2.1 (by simpa only [neg_neg] using hp.1)
    have he (i : ι) : (-(e i).1) • ((1, 0) : Plane) = (-(e i).1, 0) := by
      first
      | ext <;> simp
    simp only [he, Prod.neg_mk, neg_zero, support_axisY_sum] at hsum
    exact hsum

theorem Represents.triangleSum_functional {ι : Type*} [Fintype ι]
    {P : ConvexBody Plane} {e : ι → Plane} (h : Represents P e) (A : ConvexBody Plane) :
    2 * mixedArea volume A (triangleSum e) = 2 * mixedArea volume A P +
      height P * width A + width P * height A := by
  first
  | rw [triangleSum, mixedArea_sum_right, Finset.mul_sum]
    simp_rw [triangleFromEdge_mixedArea]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← h A,
      h.axis_correction_x A, h.axis_correction_y A]

def cornerPairing {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι → Plane) (f : κ → Plane) : ℝ := ∑ i, ∑ j, pairKernel (e i) (f j)

theorem cornerPairing_nonnegative {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι → Plane) (f : κ → Plane) : 0 ≤ cornerPairing e f :=
  Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => pairKernel_nonnegative _ _))

theorem cornerPairing_symmetric {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι → Plane) (f : κ → Plane) : cornerPairing e f = cornerPairing f e := by
  first
  | rw [cornerPairing, cornerPairing, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    exact Finset.sum_congr rfl (fun i _ => pairKernel_symmetric _ _)

theorem triangleSum_pairing {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι → Plane) (f : κ → Plane) :
    2 * mixedArea volume (triangleSum e) (triangleSum f) =
      (∑ i, |(e i).1|) * (∑ j, |(f j).2|) +
      (∑ i, |(e i).2|) * (∑ j, |(f j).1|) - cornerPairing e f := by
  first
  | rw [triangleSum, triangleSum, mixedArea_sum_left, Finset.mul_sum]
    simp_rw [mixedArea_sum_right, Finset.mul_sum, triangle_pair_mixedArea]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul, cornerPairing]

/-- Exact mixed-area formula (4.5) for the actual finite edge representations. -/
theorem Represents.mixedArea_identity {ι κ : Type*} [Fintype ι] [Fintype κ]
    {P Q : ConvexBody Plane} {e : ι → Plane} {f : κ → Plane}
    (hP : Represents P e) (hQ : Represents Q f) :
    2 * mixedArea volume P Q =
      width P * height Q + height P * width Q - cornerPairing e f := by
  first
  | have hQP := hQ.triangleSum_functional P
    have hPT := hP.triangleSum_functional (triangleSum f)
    have hpair := triangleSum_pairing e f
    rw [mixedArea_symm volume (triangleSum f) (triangleSum e),
      mixedArea_symm volume (triangleSum f) P,
      triangleSum_width, triangleSum_height, hQ.total_variation.1, hQ.total_variation.2] at hPT
    rw [hP.total_variation.1, hP.total_variation.2,
      hQ.total_variation.1, hQ.total_variation.2] at hpair
    nlinarith

/-- Exact ordinary-area identity (4.3), not an abstract edge-area definition. -/
theorem Represents.area_identity {ι : Type*} [Fintype ι]
    {P : ConvexBody Plane} {e : ι → Plane} (h : Represents P e) :
    volume.real (P : Set Plane) = width P * height P - cornerPairing e e / 2 := by
  first
  | have harea := h.mixedArea_identity h
    rw [mixedArea_diagonal volume plane_finrank] at harea
    nlinarith

end VolumePolynomials.PlanarEdges
