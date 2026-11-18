module

public import VolumePolynomials.BalancedEdgeBody
public import VolumePolynomials.PolygonCornerMeasures

@[expose] public section
set_option autoImplicit false

/-! # The actual product-edge construction

The four signed totals are bounded using the proved input widths. Four explicit
axis vectors complete those totals to one, and the erosion construction supplies
an actual compact convex body with this finite edge representation.
-/

noncomputable section
open Set MeasureTheory Matrix
open scoped BigOperators Pointwise

namespace VolumePolynomials.PlanarEdges

open PlanarExtrusion PlanarMixedForm PlanarCorner OAI.Paper092

def interactionEdge (b c : Plane) : Plane :=
  if 0 < b.1 * c.1 then (-|c.1| * b.2, |b.1| * c.2) else 0

def positiveX {ι : Type*} [Fintype ι] (e : ι → Plane) : ℝ := ∑ i, max (e i).1 0
def negativeX {ι : Type*} [Fintype ι] (e : ι → Plane) : ℝ := ∑ i, max (-(e i).1) 0
def positiveY {ι : Type*} [Fintype ι] (e : ι → Plane) : ℝ := ∑ i, max (e i).2 0
def negativeY {ι : Type*} [Fintype ι] (e : ι → Plane) : ℝ := ∑ i, max (-(e i).2) 0

theorem positiveX_nonnegative {ι : Type*} [Fintype ι] (e : ι → Plane) : 0 ≤ positiveX e :=
  Finset.sum_nonneg (fun _ _ => le_max_right _ _)
theorem negativeX_nonnegative {ι : Type*} [Fintype ι] (e : ι → Plane) : 0 ≤ negativeX e :=
  Finset.sum_nonneg (fun _ _ => le_max_right _ _)
theorem positiveY_nonnegative {ι : Type*} [Fintype ι] (e : ι → Plane) : 0 ≤ positiveY e :=
  Finset.sum_nonneg (fun _ _ => le_max_right _ _)
theorem negativeY_nonnegative {ι : Type*} [Fintype ι] (e : ι → Plane) : 0 ≤ negativeY e :=
  Finset.sum_nonneg (fun _ _ => le_max_right _ _)

theorem max_mul_nonnegative (a x : ℝ) (ha : 0 ≤ a) :
    max (a * x) 0 = a * max x 0 := by
  first
  | rcases le_total 0 x with hx | hx
    · rw [max_eq_left (mul_nonneg ha hx), max_eq_left hx]
    · rw [max_eq_right (mul_nonpos_of_nonneg_of_nonpos ha hx), max_eq_right hx, mul_zero]

theorem matching_abs_sum_le {ι : Type*} [Fintype ι] (f : ι → Plane)
    {w : ℝ} (hp : positiveX f = w) (hn : negativeX f = w) (hw : 0 ≤ w) (x : ℝ) :
    (∑ i, if 0 < x * (f i).1 then |(f i).1| else 0) ≤ w := by
  first
  | rcases lt_trichotomy x 0 with hx | hx | hx
    · have he (i : ι) : (if 0 < x * (f i).1 then |(f i).1| else 0) = max (-(f i).1) 0 := by
        first
        | by_cases hy : (f i).1 < 0
          · rw [if_pos (mul_pos_of_neg_of_neg hx hy), abs_of_neg hy, max_eq_left (neg_pos.mpr hy).le]
          · have hy0 := le_of_not_gt hy
            rw [if_neg (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg hx.le hy0)),
              max_eq_right (neg_nonpos.mpr hy0)]
      simp_rw [he]
      exact hn.le
    · subst x
      simpa using hw
    · have he (i : ι) : (if 0 < x * (f i).1 then |(f i).1| else 0) = max (f i).1 0 := by
        first
        | by_cases hy : 0 < (f i).1
          · rw [if_pos (mul_pos hx hy), abs_of_pos hy, max_eq_left hy.le]
          · have hy0 := le_of_not_gt hy
            rw [if_neg (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hx.le hy0)), max_eq_right hy0]
      simp_rw [he]
      exact hp.le

theorem interactionEdge_positiveX (b c : Plane) :
    max (interactionEdge b c).1 0 =
      max (-b.2) 0 * (if 0 < b.1 * c.1 then |c.1| else 0) := by
  first
  | unfold interactionEdge
    split_ifs
    · change max (-|c.1| * b.2) 0 = _
      rw [show -|c.1| * b.2 = |c.1| * (-b.2) by ring,
        max_mul_nonnegative _ _ (abs_nonneg _)]
      ring
    · simp

theorem interactionEdge_negativeX (b c : Plane) :
    max (-(interactionEdge b c).1) 0 =
      max b.2 0 * (if 0 < b.1 * c.1 then |c.1| else 0) := by
  first
  | unfold interactionEdge
    split_ifs
    · change max (-(-|c.1| * b.2)) 0 = _
      rw [show -(-|c.1| * b.2) = |c.1| * b.2 by ring,
        max_mul_nonnegative _ _ (abs_nonneg _)]
      ring
    · simp

theorem interactionEdge_positiveY (b c : Plane) :
    max (interactionEdge b c).2 0 =
      max c.2 0 * (if 0 < c.1 * b.1 then |b.1| else 0) := by
  first
  | unfold interactionEdge
    rw [mul_comm c.1 b.1]
    split_ifs
    · rw [max_mul_nonnegative _ _ (abs_nonneg _)]
      ring
    · simp

theorem interactionEdge_negativeY (b c : Plane) :
    max (-(interactionEdge b c).2) 0 =
      max (-c.2) 0 * (if 0 < c.1 * b.1 then |b.1| else 0) := by
  first
  | unfold interactionEdge
    rw [mul_comm c.1 b.1]
    split_ifs
    · change max (-(|b.1| * c.2)) 0 = _
      rw [show -(|b.1| * c.2) = |b.1| * (-c.2) by ring,
        max_mul_nonnegative _ _ (abs_nonneg _)]
      ring
    · simp

def productEdges {ι κ : Type*} (b : ι → Plane) (c : κ → Plane) : ι × κ → Plane :=
  fun i => interactionEdge (b i.1) (c i.2)

theorem productEdges_signed_totals_le_one {ι κ : Type*} [Fintype ι] [Fintype κ]
    {B C : ConvexBody Plane} {b : ι → Plane} {c : κ → Plane}
    (hB : Represents B b) (hC : Represents C c)
    (hBw : width B = 1) (hBh : height B = 1)
    (hCw : width C = 1) (hCh : height C = 1) :
    positiveX (productEdges b c) ≤ 1 ∧ negativeX (productEdges b c) ≤ 1 ∧
      positiveY (productEdges b c) ≤ 1 ∧ negativeY (productEdges b c) ≤ 1 := by
  first
  | have hb := hB.signed_variation
    have hc := hC.signed_variation
    rw [hBw, hBh] at hb
    rw [hCw, hCh] at hc
    have hmatchB := matching_abs_sum_le b hb.1 hb.2.2.1 (by norm_num : (0 : ℝ) ≤ 1)
    have hmatchC := matching_abs_sum_le c hc.1 hc.2.2.1 (by norm_num : (0 : ℝ) ≤ 1)
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [positiveX, productEdges, Fintype.sum_prod_type, interactionEdge_positiveX,
        ← Finset.mul_sum]
      calc
        _ ≤ ∑ i, max (-(b i).2) 0 * 1 := Finset.sum_le_sum (fun i _ =>
          mul_le_mul_of_nonneg_left (hmatchC (b i).1) (le_max_right _ _))
        _ = 1 := by simpa only [mul_one] using hb.2.2.2
    · simp only [negativeX, productEdges, Fintype.sum_prod_type, interactionEdge_negativeX,
        ← Finset.mul_sum]
      calc
        _ ≤ ∑ i, max (b i).2 0 * 1 := Finset.sum_le_sum (fun i _ =>
          mul_le_mul_of_nonneg_left (hmatchC (b i).1) (le_max_right _ _))
        _ = 1 := by simpa only [mul_one] using hb.2.1
    · simp only [positiveY, productEdges, Fintype.sum_prod_type, interactionEdge_positiveY]
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum]
      calc
        _ ≤ ∑ j, max (c j).2 0 * 1 := Finset.sum_le_sum (fun j _ =>
          mul_le_mul_of_nonneg_left (hmatchB (c j).1) (le_max_right _ _))
        _ = 1 := by simpa only [mul_one] using hc.2.1
    · simp only [negativeY, productEdges, Fintype.sum_prod_type, interactionEdge_negativeY]
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum]
      calc
        _ ≤ ∑ j, max (-(c j).2) 0 * 1 := Finset.sum_le_sum (fun j _ =>
          mul_le_mul_of_nonneg_left (hmatchB (c j).1) (le_max_right _ _))
        _ = 1 := by simpa only [mul_one] using hc.2.2.2

def axisCompletion {ι : Type*} [Fintype ι] (e : ι → Plane) : Fin 4 → Plane :=
  ![(1 - positiveX e, 0), (negativeX e - 1, 0),
    (0, 1 - positiveY e), (0, negativeY e - 1)]

def completedEdges {ι : Type*} [Fintype ι] (e : ι → Plane) : ι ⊕ Fin 4 → Plane :=
  Sum.elim e (axisCompletion e)

theorem completedEdges_signed_totals {ι : Type*} [Fintype ι] (e : ι → Plane)
    (hpX : positiveX e ≤ 1) (hnX : negativeX e ≤ 1)
    (hpY : positiveY e ≤ 1) (hnY : negativeY e ≤ 1) :
    positiveX (completedEdges e) = 1 ∧ negativeX (completedEdges e) = 1 ∧
      positiveY (completedEdges e) = 1 ∧ negativeY (completedEdges e) = 1 := by
  first
  | have hpx : 0 ≤ 1 - positiveX e := sub_nonneg.mpr hpX
    have hnx : negativeX e - 1 ≤ 0 := sub_nonpos.mpr hnX
    have hpy : 0 ≤ 1 - positiveY e := sub_nonneg.mpr hpY
    have hny : negativeY e - 1 ≤ 0 := sub_nonpos.mpr hnY
    dsimp only [positiveX, negativeX, positiveY, negativeY] at *
    simp only [positiveX, negativeX, positiveY, negativeY, completedEdges,
      Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, axisCompletion, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero,
      max_eq_left hpx, max_eq_right hnx, max_eq_left hpy, max_eq_right hny,
      max_eq_right (neg_nonpos.mpr hpx), max_eq_left (neg_nonneg.mpr hnx),
      max_eq_right (neg_nonpos.mpr hpy), max_eq_left (neg_nonneg.mpr hny), neg_zero,
      max_self, zero_add]
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals linarith

theorem exists_productEdge_body {ι κ : Type*} [Fintype ι] [Fintype κ]
    {B C : ConvexBody Plane} {b : ι → Plane} {c : κ → Plane}
    (hB : Represents B b) (hC : Represents C c)
    (hBw : width B = 1) (hBh : height B = 1)
    (hCw : width C = 1) (hCh : height C = 1) :
    ∃ Q : ConvexBody Plane, Represents Q (completedEdges (productEdges b c)) ∧
      width Q = 1 ∧ height Q = 1 := by
  first
  | obtain ⟨hpx, hnx, hpy, hny⟩ := productEdges_signed_totals_le_one hB hC hBw hBh hCw hCh
    obtain ⟨hpx', hnx', hpy', hny'⟩ := completedEdges_signed_totals (productEdges b c) hpx hnx hpy hny
    exact exists_body_of_balanced_edges (completedEdges (productEdges b c)) hpx' hnx' hpy' hny'

end VolumePolynomials.PlanarEdges
