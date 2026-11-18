module
public import PaperVerification.HyperbolicLargeScale
public import PaperVerification.HyperbolicBoundaryActual
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
@[expose] public section
/-! # Compact scale minimization

This replaces the asymptotic boundary-compactness argument in Lemma 5.2 by
an ordinary minimum over `0 ≤ p ≤ q ≤ R ≤ B`.  The allowed derivative at
`R = B` is retained as a one-sided inequality.  All functions here are the
literal functionals of equation (14).
-/

noncomputable section

namespace PaperVerification.Hyperbolic

open Real Set Filter Topology

def scaleSimplex (B : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {x | 0 ≤ x.2.1 ∧ x.2.1 ≤ x.2.2 ∧ x.2.2 ≤ x.1 ∧ x.1 ≤ B}

theorem isCompact_scaleSimplex (B : ℝ) : IsCompact (scaleSimplex B) := by
  have hc : IsClosed (scaleSimplex B) :=
    (isClosed_le continuous_const continuous_snd.fst).inter
      ((isClosed_le continuous_snd.fst continuous_snd.snd).inter
        ((isClosed_le continuous_snd.snd continuous_fst).inter
          (isClosed_le continuous_fst continuous_const)))
  apply (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).of_isClosed_subset hc
  intro x hx
  change x ∈ (Icc (0 : ℝ) B) ×ˢ ((Icc (0 : ℝ) B) ×ˢ Icc 0 B)
  exact ⟨⟨hx.1.trans (hx.2.1.trans hx.2.2.1), hx.2.2.2⟩,
    ⟨⟨hx.1, hx.2.1.trans (hx.2.2.1.trans hx.2.2.2)⟩,
      ⟨hx.1.trans hx.2.1, hx.2.2.1.trans hx.2.2.2⟩⟩⟩

theorem derivative_nonpos_of_left_interval_minimum {f : ℝ → ℝ} {a x d : ℝ}
    (hd : HasDerivAt f d x) (ha : a < x) (hmin : ∀ y ∈ Ioo a x, f x ≤ f y) : d ≤ 0 := by
  apply le_of_tendsto (hd.tendsto_slope.mono_left (nhdsLT_le_nhdsNE x))
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds ha)] with y hyx hya
  rw [slope_def_field]
  exact div_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hmin y ⟨hya, hyx⟩))
    (sub_nonpos.mpr hyx.le)

theorem derivative_nonneg_of_right_interval_minimum {f : ℝ → ℝ} {x b d : ℝ}
    (hd : HasDerivAt f d x) (hb : x < b) (hmin : ∀ y ∈ Ioo x b, f x ≤ f y) : 0 ≤ d := by
  apply ge_of_tendsto (hd.tendsto_slope.mono_left (nhdsGT_le_nhdsNE x))
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hb)] with y hxy hyb
  rw [slope_def_field]
  exact div_nonneg (sub_nonneg.mpr (hmin y ⟨hxy, hyb⟩)) (sub_nonneg.mpr hxy.le)

theorem twoPointObjective_mono_of_ratio {R p q R' p' q' w : ℝ}
    (hp : p ∈ Icc 0 R) (hq : q ∈ Icc 0 R)
    (hp' : p' ∈ Icc 0 R') (hq' : q' ∈ Icc 0 R') (hw : w ∈ Icc 0 1)
    (h : twoPointRatio R p q w ≤ twoPointRatio R' p' q' w) :
    twoPointObjective R p q w ≤ twoPointObjective R' p' q' w := by
  rw [twoPointObjective_eq_log_ratio hp hq hw, twoPointObjective_eq_log_ratio hp' hq' hw]
  exact (Real.log_le_log_iff (twoPointRatio_pos hp hq hw) (twoPointRatio_pos hp' hq' hw)).mpr h

/-- A nondegenerate unaligned configuration cannot minimize the literal ratio
on any compact interval of scales containing it. -/
theorem not_minimum_scaleSimplex_unaligned {B R p q w : ℝ}
    (hx : (R, p, q) ∈ scaleSimplex B) (hpq : p < q) (hs : p + q < R)
    (hw : w ∈ Ioo (1 / 4) (1 / 2))
    (hmin : ∀ x ∈ scaleSimplex B, twoPointRatio R p q w ≤ twoPointRatio x.1 x.2.1 x.2.2 w) :
    False := by
  have hp0 : 0 ≤ p := hx.1
  have hq0 : 0 < q := hp0.trans_lt hpq
  have hqR : q < R := by linarith
  have hR0 := hq0.trans hqR
  have hRB : R ≤ B := hx.2.2.2
  have hw0 : 0 < w := (by norm_num : (0 : ℝ) < 1 / 4).trans hw.1
  have hw1 : w < 1 := hw.2.trans (by norm_num)
  have hpz : p = 0 := by
    by_contra hpz
    have hp : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hpz)
    let v₁ := 2 * p - R
    let v₂ := 2 * q - R
    have hv : v₁ < v₂ := by dsimp [v₁, v₂]; linarith
    have hs' : v₁ + v₂ < 0 := by dsimp [v₁, v₂]; linarith
    have hstep := centeredRatio_scale_strictMono (R := R - p) (S := R) hv hs' hw
      (by dsimp [v₁]; linarith) (by dsimp [v₂]; linarith) (by linarith)
    have hnew : (R - p, p / 2, q - p / 2) ∈ scaleSimplex B := by
      change 0 ≤ p / 2 ∧ p / 2 ≤ q - p / 2 ∧ q - p / 2 ≤ R - p ∧ R - p ≤ B
      constructor
      · positivity
      constructor
      · linarith
      constructor <;> linarith
    have hlow := hmin (R - p, p / 2, q - p / 2) hnew
    have hstep' : twoPointRatio (R - p) (p / 2) (q - p / 2) w < twoPointRatio R p q w := by
      simpa only [centeredRatio,
        show (R - p + v₁) / 2 = p / 2 by dsimp [v₁]; ring,
        show (R - p + v₂) / 2 = q - p / 2 by dsimp [v₂]; ring,
        show (R + v₁) / 2 = p by dsimp [v₁]; ring,
        show (R + v₂) / 2 = q by dsimp [v₂]; ring] using hstep
    exact (not_lt_of_ge hlow) hstep'
  subst p
  have hpR : (0 : ℝ) ∈ Icc 0 R := ⟨le_rfl, hR0.le⟩
  have hq' : q ∈ Icc 0 R := ⟨hq0.le, hqR.le⟩
  have hw' : w ∈ Icc 0 1 := ⟨hw0.le, hw1.le⟩
  obtain ⟨hdq, hdR, hdp⟩ := boundary_actual_derivatives ⟨hq0, hqR⟩ hw
  have hlocalQ : IsLocalMin (fun q => twoPointObjective R 0 q w) q := by
    filter_upwards [Ioo_mem_nhds hq0 hqR] with q' hq''
    apply twoPointObjective_mono_of_ratio hpR hq' hpR ⟨hq''.1.le, hq''.2.le⟩ hw'
    apply hmin (R, 0, q')
    exact ⟨le_rfl, hq''.1.le, hq''.2.le, hRB⟩
  have hQzero : deriv (fun q => twoPointObjective R 0 q w) q = 0 := hlocalQ.deriv_eq_zero
  have hRnonpos : deriv (fun R => twoPointObjective R 0 q w) R ≤ 0 := by
    rw [hdR.deriv]
    apply derivative_nonpos_of_left_interval_minimum hdR hqR
    intro R' hR'
    have hR'0 : 0 < R' := hq0.trans hR'.1
    apply twoPointObjective_mono_of_ratio hpR hq' ⟨le_rfl, hR'0.le⟩ ⟨hq0.le, hR'.1.le⟩ hw'
    apply hmin (R', 0, q)
    exact ⟨le_rfl, hq0.le, hR'.1.le, hR'.2.le.trans hRB⟩
  have hPnonneg : 0 ≤ deriv (fun p => twoPointObjective R p q w) 0 := by
    rw [hdp.deriv]
    apply derivative_nonneg_of_right_interval_minimum hdp hq0
    intro p' hp'
    apply twoPointObjective_mono_of_ratio hpR hq' ⟨hp'.1.le, hp'.2.le.trans hqR.le⟩ hq' hw'
    apply hmin (R, p', q)
    exact ⟨hp'.1.le, hp'.2.le, hqR.le, hRB⟩
  exact (not_lt_of_ge hPnonneg) (boundary_inward_deriv_negative ⟨hq0, hqR⟩ hw hQzero hRnonpos)

/-- The full upper-weight bound, proved by compact scale minimization. -/
theorem twoPointRatio_ge_one_large_weight {R p q w : ℝ}
    (hp : p ∈ Icc 0 R) (hq : q ∈ Icc 0 R) (hpq : p ≤ q)
    (hw : w ∈ Ioo (1 / 4) (1 / 2)) : 1 ≤ twoPointRatio R p q w := by
  by_contra hbad
  have hbad : twoPointRatio R p q w < 1 := lt_of_not_ge hbad
  have hw0 : 0 < w := (by norm_num : (0 : ℝ) < 1 / 4).trans hw.1
  have hw1 : w < 1 := hw.2.trans (by norm_num)
  have hinit : (R, p, q) ∈ scaleSimplex R := ⟨hp.1, hpq, hq.2, le_rfl⟩
  obtain ⟨x, hx, hmin⟩ := (isCompact_scaleSimplex R).exists_isMinOn ⟨(R, p, q), hinit⟩
    (continuous_twoPointRatio ⟨hw0, hw1⟩).continuousOn
  obtain ⟨S, a, b⟩ := x
  have hvalue : twoPointRatio S a b w < 1 := (hmin hinit).trans_lt hbad
  have ha : a ∈ Icc 0 S := ⟨hx.1, hx.2.1.trans hx.2.2.1⟩
  have hb : b ∈ Icc 0 S := ⟨hx.1.trans hx.2.1, hx.2.2.1⟩
  have hab : a < b := by
    rcases hx.2.1.eq_or_lt with heq | hlt
    · change a = b at heq
      subst b
      rw [twoPointRatio_same ha] at hvalue
      exact (lt_irrefl 1 hvalue).elim
    · exact hlt
  have hs : a + b < S := by
    by_contra h
    have hstrict := twoPointRatio_gt_one_aligned ha hb hab ⟨hw0, hw.2⟩ (le_of_not_gt h)
    exact (not_lt_of_ge hstrict.le) hvalue
  exact not_minimum_scaleSimplex_unaligned hx hab hs hw (fun y hy => hmin hy)

theorem twoPointRatio_gt_one_unaligned_large_weight {R p q w : ℝ}
    (hp : p ∈ Icc 0 R) (hq : q ∈ Icc 0 R) (hpq : p < q) (hs : p + q < R)
    (hw : w ∈ Ioo (1 / 4) (1 / 2)) : 1 < twoPointRatio R p q w := by
  have hge := twoPointRatio_ge_one_large_weight hp hq hpq.le hw
  by_contra hbad
  have heq : twoPointRatio R p q w = 1 := le_antisymm (le_of_not_gt hbad) hge
  apply not_minimum_scaleSimplex_unaligned
    (show (R, p, q) ∈ scaleSimplex R from ⟨hp.1, hpq.le, hq.2, le_rfl⟩) hpq hs hw
  intro x hx
  rw [heq]
  exact twoPointRatio_ge_one_large_weight ⟨hx.1, hx.2.1.trans hx.2.2.1⟩
    ⟨hx.1.trans hx.2.1, hx.2.2.1⟩ hx.2.1 hw

theorem twoPointRatio_gt_one_below_half {R p q w : ℝ}
    (hp : p ∈ Icc 0 R) (hq : q ∈ Icc 0 R) (hpq : p < q) (hw : w ∈ Ioo 0 (1 / 2)) :
    1 < twoPointRatio R p q w := by
  by_cases hs : R ≤ p + q
  · exact twoPointRatio_gt_one_aligned hp hq hpq hw hs
  have hs' : p + q < R := lt_of_not_ge hs
  by_cases hwq : w ≤ 1 / 4
  · exact twoPointRatio_gt_one_unaligned_small_weight hp hq hpq hs' ⟨hw.1, hwq⟩
  · exact twoPointRatio_gt_one_unaligned_large_weight hp hq hpq hs' ⟨lt_of_not_ge hwq, hw.2⟩

/-- Lemma 4.2, inequality, with all degenerate cases and the entire weight interval. -/
theorem twoPointRatio_ge_one {R p q w : ℝ}
    (hp : p ∈ Icc 0 R) (hq : q ∈ Icc 0 R) (hpq : p ≤ q) (hw : w ∈ Icc 0 1) :
    1 ≤ twoPointRatio R p q w := by
  rcases hw.1.eq_or_lt with hw0 | hw0
  · rw [← hw0, twoPointRatio_weight_zero]
  rcases hw.2.eq_or_lt with hw1 | hw1
  · rw [hw1, twoPointRatio_weight_one]
  rcases hpq.eq_or_lt with hpq | hpq
  · subst q
    rw [twoPointRatio_same hp]
  rcases lt_trichotomy w (1 / 2) with hwh | hwh | hwh
  · exact (twoPointRatio_gt_one_below_half hp hq hpq ⟨hw0, hwh⟩).le
  · rw [hwh]
    exact twoPointRatio_half_ge_one R p q
  · rw [← twoPointRatio_reflect R p q w]
    exact (twoPointRatio_gt_one_below_half
      ⟨sub_nonneg.mpr hq.2, by linarith [hq.1]⟩
      ⟨sub_nonneg.mpr hp.2, by linarith [hp.1]⟩ (by linarith)
      ⟨sub_pos.mpr hw1, by linarith⟩).le

/-- Lemma 4.2, the exact equality classification. -/
theorem twoPointRatio_eq_one_iff {R p q w : ℝ}
    (hp : p ∈ Icc 0 R) (hq : q ∈ Icc 0 R) (hpq : p ≤ q) (hw : w ∈ Icc 0 1) :
    twoPointRatio R p q w = 1 ↔ w = 0 ∨ w = 1 ∨ p = q ∨ (w = 1 / 2 ∧ p + q = R) := by
  constructor
  · intro heq
    by_cases hw0 : w = 0
    · exact Or.inl hw0
    by_cases hw1 : w = 1
    · exact Or.inr (Or.inl hw1)
    by_cases hpq' : p = q
    · exact Or.inr (Or.inr (Or.inl hpq'))
    have hwp : 0 < w := lt_of_le_of_ne hw.1 (Ne.symm hw0)
    have hwlt : w < 1 := lt_of_le_of_ne hw.2 hw1
    have hpqlt : p < q := lt_of_le_of_ne hpq hpq'
    rcases lt_trichotomy w (1 / 2) with h | h | h
    · have hs := twoPointRatio_gt_one_below_half hp hq hpqlt ⟨hwp, h⟩
      rw [heq] at hs
      exact (lt_irrefl 1 hs).elim
    · refine Or.inr (Or.inr (Or.inr ⟨h, ?_⟩))
      rw [h] at heq
      exact ((twoPointRatio_half_eq_one_iff R p q).mp heq).resolve_left hpq'
    · have hs := twoPointRatio_gt_one_below_half
        (R := R) (p := R - q) (q := R - p) (w := 1 - w)
        ⟨sub_nonneg.mpr hq.2, by linarith [hq.1]⟩
        ⟨sub_nonneg.mpr hp.2, by linarith [hp.1]⟩ (by linarith)
        ⟨sub_pos.mpr hwlt, by linarith⟩
      rw [twoPointRatio_reflect, heq] at hs
      exact (lt_irrefl 1 hs).elim
  · rintro (rfl | rfl | rfl | ⟨rfl, hs⟩)
    · exact twoPointRatio_weight_zero _ _ _
    · exact twoPointRatio_weight_one _ _ _
    · exact twoPointRatio_same hp _
    · exact (twoPointRatio_half_eq_one_iff R p q).mpr (Or.inr hs)

end PaperVerification.Hyperbolic

#print axioms PaperVerification.Hyperbolic.twoPointRatio_ge_one
#print axioms PaperVerification.Hyperbolic.twoPointRatio_eq_one_iff
