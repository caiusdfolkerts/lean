module
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
@[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

lemma rpow_sub_le_difference {x u k : ℝ} (hu : 0 ≤ u) (hux : u ≤ x) (hk : 1 ≤ k) :
    (x - u) ^ k ≤ x ^ k - u ^ k := by
  have h := Real.add_rpow_le_rpow_add (sub_nonneg.mpr hux) hu hk
  rw [sub_add_cancel] at h
  linarith

lemma strict_rpow_superadditive {a b k : ℝ} (ha : 0 < a) (hb : 0 < b) (hk : 1 < k) :
    a ^ k + b ^ k < (a + b) ^ k := by
  have hab : 0 < a + b := add_pos ha hb
  have hpa := Real.rpow_lt_self_of_lt_one (div_pos ha hab)
    ((div_lt_one hab).mpr (lt_add_of_pos_right _ hb)) hk
  have hpb := Real.rpow_lt_self_of_lt_one (div_pos hb hab)
    ((div_lt_one hab).mpr (lt_add_of_pos_left _ ha)) hk
  rw [Real.div_rpow ha.le hab.le] at hpa
  rw [Real.div_rpow hb.le hab.le] at hpb
  have hs : a / (a + b) + b / (a + b) = 1 := by
    rw [← add_div, div_self hab.ne']
  apply (div_lt_one (Real.rpow_pos_of_pos hab k)).mp
  rw [add_div]
  linarith

lemma rpow_sub_eq_difference_iff {x u k : ℝ} (hu : 0 ≤ u) (hux : u < x)
    (hk : 1 < k) : (x - u) ^ k = x ^ k - u ^ k ↔ u = 0 := by
  constructor
  · intro heq
    by_contra hne
    have hu' : 0 < u := lt_of_le_of_ne hu (Ne.symm hne)
    have hs := strict_rpow_superadditive (sub_pos.mpr hux) hu' hk
    rw [sub_add_cancel] at hs
    linarith
  · rintro rfl
    simp [Real.zero_rpow (lt_trans zero_lt_one hk).ne']

lemma rpow_midpoint_lower {a b k : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hk : 1 ≤ k) :
    2 * ((a + b) / 2) ^ k ≤ a ^ k + b ^ k := by
  have hconv := (convexOn_rpow hk).2
  have h := hconv ha hb
    (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  simp only [smul_eq_mul] at h
  rw [show (1 / 2 : ℝ) * a + (1 / 2) * b = (a + b) / 2 by ring] at h
  linarith

lemma rpow_midpoint_strict {a b k : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≠ b)
    (hk : 1 < k) : 2 * ((a + b) / 2) ^ k < a ^ k + b ^ k := by
  have hconv := (strictConvexOn_rpow hk).2
  have h := hconv ha hb hab
    (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  simp only [smul_eq_mul] at h
  rw [show (1 / 2 : ℝ) * a + (1 / 2) * b = (a + b) / 2 by ring] at h
  linarith

/-- The power inequality used for every real dimension ratio k≥1 in Theorem 3.3. -/
theorem dimension_lift_bound {X Y U V q k : ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hXU : U ≤ X) (hYV : V ≤ Y)
    (hq : 0 ≤ q) (hk : 1 ≤ k) (hbase : 2 * q ≤ X + Y - U - V) :
    2 * q ^ k ≤ X ^ k + Y ^ k - U ^ k - V ^ k := by
  have hx := rpow_sub_le_difference hU hXU hk
  have hy := rpow_sub_le_difference hV hYV hk
  have hm := rpow_midpoint_lower (sub_nonneg.mpr hXU) (sub_nonneg.mpr hYV) hk
  have hq' : q ≤ ((X - U) + (Y - V)) / 2 := by linarith
  have hp := Real.rpow_le_rpow hq hq' (le_trans zero_le_one hk)
  linarith

/-- All equality conditions survive the passage from eight to higher dimension. -/
theorem dimension_lift_equality {X Y U V q k : ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hXU : U < X) (hYV : V < Y)
    (hq : 0 < q) (hk : 1 < k) (hbase : 2 * q ≤ X + Y - U - V) :
    X ^ k + Y ^ k - U ^ k - V ^ k = 2 * q ^ k ↔
      U = 0 ∧ V = 0 ∧ X = q ∧ Y = q := by
  have hx := rpow_sub_le_difference hU hXU.le hk.le
  have hy := rpow_sub_le_difference hV hYV.le hk.le
  have hm := rpow_midpoint_lower (sub_nonneg.mpr hXU.le) (sub_nonneg.mpr hYV.le) hk.le
  have hq' : q ≤ ((X - U) + (Y - V)) / 2 := by linarith
  have hp := Real.rpow_le_rpow hq.le hq' (le_trans zero_le_one hk.le)
  constructor
  · intro heq
    have huEq : (X - U) ^ k = X ^ k - U ^ k := by linarith
    have hvEq : (Y - V) ^ k = Y ^ k - V ^ k := by linarith
    have hU0 := (rpow_sub_eq_difference_iff hU hXU hk).mp huEq
    have hV0 := (rpow_sub_eq_difference_iff hV hYV hk).mp hvEq
    subst U
    subst V
    simp only [sub_zero, Real.zero_rpow (lt_trans zero_lt_one hk).ne'] at heq hq' hp
    have hXY : X = Y := by
      by_contra hne
      have hs := rpow_midpoint_strict hXU.le hYV.le hne hk
      linarith
    have hXq : X = q := by
      apply (Real.rpow_left_inj hXU.le hq.le (lt_trans zero_lt_one hk).ne').mp
      rw [← hXY] at heq
      linarith
    exact ⟨rfl, rfl, hXq, hXY.symm.trans hXq⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    simp [Real.zero_rpow (lt_trans zero_lt_one hk).ne', two_mul]

end PaperVerification.ColdSpots
