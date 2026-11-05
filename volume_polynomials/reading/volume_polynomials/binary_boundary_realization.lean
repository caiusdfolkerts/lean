module

public import VolumePolynomials.BinaryBoundarySequences
public import Mathlib.Order.Interval.Finset.Fin

@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# Degenerate simplex realizations

The two approximating simplices have axis lengths affine in the small
parameter. Their limits are exactly the two possibly degenerate simplices
in (A.3), with coordinate order reversed. Their volume identity passes to
the limit for every pair of nonnegative Minkowski weights.
-/

open Set MeasureTheory Filter
open scoped Pointwise BigOperators Topology

namespace VolumePolynomials.BinarySimplex

open AxisSimplex BinarySequences

def leftAxes (d l : ℕ) (C eps : ℝ) (j : Fin d) : ℝ :=
  C * if d - j.val ≤ l then eps else 1

def rightAxes (d l r : ℕ) (C : ℝ) (a : ℕ → ℝ) (eps : ℝ) (j : Fin d) : ℝ :=
  if d - j.val ≤ l then C
  else if d - j.val ≤ r then C * (a (d - j.val) / a (d - j.val - 1))
  else C * eps

theorem card_last_axes {d l : ℕ} (hl : l ≤ d) :
    (Finset.univ.filter (fun j : Fin d => d - j.val ≤ l)).card = l := by
  first
  | by_cases hl0 : l = 0
    · subst l
      have he : Finset.univ.filter (fun j : Fin d => d - j.val ≤ 0) = ∅ := by
        first
        | apply Finset.eq_empty_iff_forall_notMem.mpr
          intro j hj
          have h := (Finset.mem_filter.mp hj).2
          have hjlt := j.isLt
          omega
      simp only [he, Finset.card_empty]
    · have hlt : d - l < d := by omega
      let b : Fin d := ⟨d - l, hlt⟩
      have he : Finset.univ.filter (fun j : Fin d => d - j.val ≤ l) = Finset.Ici b := by
        first
        | ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ici]
          change d - j.val ≤ l ↔ d - l ≤ j.val
          have hjlt := j.isLt
          omega
      rw [he, Fin.card_Ici]
      change d - (d - l) = l
      omega

theorem prod_leftAxes {d l : ℕ} (hl : l ≤ d) (C eps : ℝ) :
    ∏ j, leftAxes d l C eps j = C ^ d * eps ^ l := by
  first
  | simp only [leftAxes, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    congr 1
    rw [← Finset.prod_filter, Finset.prod_const, card_last_axes hl]

theorem leftAxes_pos {d l : ℕ} {C eps : ℝ} (hC : 0 < C) (heps : 0 < eps) :
    ∀ j : Fin d, 0 < leftAxes d l C eps j := by
  first
  | intro j
    unfold leftAxes
    split_ifs <;> positivity

theorem rightAxes_eq_ratio {d : ℕ} {a : ℕ → ℝ} (h : IntervalSupport d a)
    {eps : ℝ} (heps : 0 < eps) (C : ℝ) (j : Fin d) :
    rightAxes d h.left h.right C a eps j =
      leftAxes d h.left C eps j * ratioAxes d (padded a h.left h.right eps) j := by
  first
  | have hjlt := j.isLt
    have hindex : d - j.val - 1 + 1 = d - j.val := by omega
    by_cases hjl : d - j.val ≤ h.left
    · have hr := padded_ratio_left h.left_le_right
        (h.positive _ le_rfl h.left_le_right) (i := d - j.val - 1) (by omega) heps
      rw [hindex] at hr
      simp only [rightAxes, leftAxes, if_pos hjl, ratioAxes, hr]
      field_simp [heps.ne']
    · by_cases hjr : d - j.val ≤ h.right
      · have hr := padded_ratio_middle a (l := h.left) (r := h.right)
          (i := d - j.val - 1) (by omega) (by omega) eps
        rw [hindex] at hr
        simp only [rightAxes, leftAxes, if_neg hjl, if_pos hjr, ratioAxes, hr, mul_one]
      · have hr := padded_ratio_right h.left_le_right
          (h.positive _ h.left_le_right le_rfl) (i := d - j.val - 1) (by omega) heps
        rw [hindex] at hr
        simp only [rightAxes, leftAxes, if_neg hjl, if_neg hjr, ratioAxes, hr, mul_one]

theorem padded_axis_realization {d : ℕ} (hd : 0 < d) {a : ℕ → ℝ}
    (h : IntervalSupport d a) {eps : ℝ} (heps : 0 < eps)
    (hr : DecreasingRatios d (padded a h.left h.right eps)) :
    Realizes d (padded a h.left h.right eps)
      (axisBody (leftAxes d h.left (commonScale d (a h.left)) eps))
      (axisBody (rightAxes d h.left h.right (commonScale d (a h.left)) a eps)) := by
  first
  | let C := commonScale d (a h.left)
    have ha : 0 < a h.left := h.positive _ le_rfl h.left_le_right
    have hC : 0 < C := commonScale_pos ha
    have hprod : ∏ j, leftAxes d h.left C eps j =
        (d.factorial : ℝ) * padded a h.left h.right eps 0 := by
      first
      | rw [prod_leftAxes (h.left_le_right.trans h.right_le_degree), commonScale_pow hd ha.le,
          padded_eq_left a h.left_le_right (Nat.zero_le _), Nat.sub_zero]
        ring
    have hright : rightAxes d h.left h.right C a eps =
        fun j => leftAxes d h.left C eps j * ratioAxes d (padded a h.left h.right eps) j :=
      funext (rightAxes_eq_ratio h heps C)
    change Realizes d (padded a h.left h.right eps)
      (axisBody (leftAxes d h.left C eps)) (axisBody (rightAxes d h.left h.right C a eps))
    rw [hright]
    exact realizes_ratio_axes (h.padded_pos heps) hr _ (leftAxes_pos hC heps) hprod

theorem continuous_leftAxes (d l : ℕ) (C : ℝ) : Continuous (leftAxes d l C) := by
  first
  | apply continuous_pi
    intro j
    dsimp only [leftAxes]
    split_ifs <;> fun_prop

theorem continuous_rightAxes (d l r : ℕ) (C : ℝ) (a : ℕ → ℝ) :
    Continuous (rightAxes d l r C a) := by
  first
  | apply continuous_pi
    intro j
    dsimp only [rightAxes]
    split_ifs <;> fun_prop

set_option maxHeartbeats 1000000 in
/-- Formula (A.3), with no restriction on the support interval. -/
theorem boundary_axis_realization {d : ℕ} (hd : 0 < d) {a : ℕ → ℝ}
    (h : IntervalSupport d a) (hc : Criterion d a) :
    Realizes d a
      (axisBody (leftAxes d h.left (commonScale d (a h.left)) 0))
      (axisBody (rightAxes d h.left h.right (commonScale d (a h.left)) a 0)) := by
  first
  | let C := commonScale d (a h.left)
    intro t s ht hs
    have hleft : Tendsto (fun eps : ℝ => bodyVolume
        (t • axisBody (leftAxes d h.left C eps) +
          s • axisBody (rightAxes d h.left h.right C a eps)))
        (𝓝[>] (0 : ℝ)) (𝓝 (bodyVolume
        (t • axisBody (leftAxes d h.left C 0) +
          s • axisBody (rightAxes d h.left h.right C a 0)))) := by
      first
      | have hK := (continuous_axisBody d).comp' (continuous_leftAxes d h.left C)
        have hL := (continuous_axisBody d).comp' (continuous_rightAxes d h.left h.right C a)
        have hsum : Continuous (fun eps : ℝ =>
            t • axisBody (leftAxes d h.left C eps) +
              s • axisBody (rightAxes d h.left h.right C a eps)) :=
          (hK.fun_const_smul t).fun_add (hL.fun_const_smul s)
        have hc : Continuous (fun eps : ℝ => bodyVolume
            (t • axisBody (leftAxes d h.left C eps) +
              s • axisBody (rightAxes d h.left h.right C a eps))) :=
          (continuous_bodyVolume d).comp hsum
        exact (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
    have hright := value_padded_tendsto h t s
    have heq : (fun eps : ℝ => bodyVolume
        (t • axisBody (leftAxes d h.left C eps) +
          s • axisBody (rightAxes d h.left h.right C a eps)))
        =ᶠ[𝓝[>] (0 : ℝ)] fun eps => value d (padded a h.left h.right eps) t s := by
      first
      | filter_upwards [eventually_padded_decreasingRatios h hc, self_mem_nhdsWithin]
          with eps hrat heps
        exact padded_axis_realization hd h heps hrat t s ht hs
    exact tendsto_nhds_unique hleft (hright.congr' heq.symm)

theorem boundary_axes_nonnegative {d : ℕ} {a : ℕ → ℝ}
    (h : IntervalSupport d a) {C : ℝ} (hC : 0 ≤ C) :
    (∀ j : Fin d, 0 ≤ leftAxes d h.left C 0 j) ∧
      (∀ j : Fin d, 0 ≤ rightAxes d h.left h.right C a 0 j) := by
  first
  | constructor
    · intro j
      unfold leftAxes
      split_ifs <;> positivity
    · intro j
      unfold rightAxes
      split_ifs with hjl hjr
      · exact hC
      · have hjlt := j.isLt
        exact mul_nonneg hC (div_nonneg
          (h.positive _ (by omega) hjr).le (h.positive _ (by omega) (by omega)).le)
      · simp only [mul_zero, le_refl]

/-- Full sufficiency in Proposition A.1: every admissible coefficient
sequence, including all zero patterns, is realized by two explicit axis
simplices. No positivity premise on the coefficients is retained. -/
theorem appendix_A_sufficiency {d : ℕ} (hd : 0 < d) {a : ℕ → ℝ}
    (hc : Criterion d a) :
    ∃ k lam : Fin d → ℝ, (∀ i, 0 ≤ k i) ∧ (∀ i, 0 ≤ lam i) ∧
      Realizes d a (axisBody k) (axisBody lam) := by
  first
  | by_cases hz : ∀ i ≤ d, a i = 0
    · exact ⟨fun _ => 0, fun _ => 0, fun _ => le_rfl, fun _ => le_rfl,
        zero_axis_realization hd hz⟩
    · have hne : ∃ i ≤ d, a i ≠ 0 := by simpa only [not_forall, exists_prop] using hz
      obtain ⟨h⟩ := intervalSupport_of_criterion hc hne
      let C := commonScale d (a h.left)
      have hC : 0 < C := commonScale_pos (h.positive _ le_rfl h.left_le_right)
      have hn := boundary_axes_nonnegative h hC.le
      exact ⟨leftAxes d h.left C 0, rightAxes d h.left h.right C a 0,
        hn.1, hn.2, boundary_axis_realization hd h hc⟩

end VolumePolynomials.BinarySimplex
