module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace EllipsoidVerification

/-- A positive remainder in an improper integration-by-parts formula gives
a strict lower bound. Only finite-interval integrability of the remainder is
required; its improper integrability is a consequence, not an assumption. -/
theorem integral_gt_of_positive_remainder {f G R : ℝ → ℝ} {b : ℝ}
    (hf : IntegrableOn f (Ioi 0)) (hf0 : ∀ t > 0, 0 ≤ f t)
    (hR : ContinuousOn R (Ioi 0)) (hRpos : ∀ t > 0, 0 < R t)
    (hG : ∀ t > 0, HasDerivAt G (f t - R t) t)
    (hG0 : Tendsto G (𝓝[>] 0) (𝓝 (-b)))
    (hGtop : Tendsto G atTop (𝓝 0)) : b < ∫ t in Ioi (0 : ℝ), f t := by
  let δ := ∫ t in (1 : ℝ)..2, R t
  have hδ : 0 < δ := intervalIntegral.integral_pos (by norm_num)
    (hR.mono (by intro t ht; exact lt_of_lt_of_le zero_lt_one ht.1))
    (fun t ht => (hRpos t (zero_lt_one.trans ht.1)).le)
    ⟨1, by norm_num, hRpos 1 zero_lt_one⟩
  have hbound {s t : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (ht2 : 2 ≤ t) :
      G t - G s + δ ≤ ∫ u in Ioi (0 : ℝ), f u := by
    have hst : s ≤ t := by linarith
    have hsub : Icc s t ⊆ Ioi (0 : ℝ) := fun u hu => hs.trans_le hu.1
    have hfi : IntervalIntegrable f volume s t :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hst).mpr (hf.mono_set hsub)
    have hRi : IntervalIntegrable R volume s t :=
      (show ContinuousOn R (uIcc s t) by
        simpa only [uIcc_of_le hst] using hR.mono hsub).intervalIntegrable
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u hu => hG u (hsub (by simpa only [uIcc_of_le hst] using hu))) (hfi.sub hRi)
    rw [intervalIntegral.integral_sub hfi hRi] at hFTC
    have hRle : δ ≤ ∫ u in s..t, R u :=
      intervalIntegral.integral_mono_interval hs1 (by norm_num) ht2
        ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun u hu =>
          (hRpos u (hs.trans hu.1)).le)) hRi
    have hfle : (∫ u in s..t, f u) ≤ ∫ u in Ioi (0 : ℝ), f u := by
      rw [intervalIntegral.integral_of_le hst]
      exact setIntegral_mono_set hf
        ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ hf0))
        (show Ioc s t ⊆ Ioi (0 : ℝ) from fun u hu => hs.trans hu.1).eventuallySubset
    linarith
  have ht : Tendsto (fun s : ℝ => G s⁻¹ - G s + δ) (𝓝[>] 0) (𝓝 (b + δ)) := by
    have hlimit := ((hGtop.comp tendsto_inv_nhdsGT_zero).sub hG0).add_const δ
    change Tendsto (fun s : ℝ => G s⁻¹ - G s + δ) (𝓝[>] 0)
      (𝓝 (0 - (-b) + δ)) at hlimit
    simpa only [zero_sub, neg_neg] using hlimit
  have hevent : ∀ᶠ s : ℝ in 𝓝[>] 0,
      G s⁻¹ - G s + δ ≤ ∫ u in Ioi (0 : ℝ), f u := by
    filter_upwards [(self_mem_nhdsWithin : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s),
      (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)).filter_mono
        nhdsWithin_le_nhds] with s hs hs2
    apply hbound hs (by linarith)
    simpa only [one_div] using
      (le_div_iff₀ hs).mpr (show (2 : ℝ) * s ≤ 1 by linarith)
  exact (lt_add_of_pos_right b hδ).trans_le (le_of_tendsto ht hevent)

def barrierPrimitive (h u : ℝ → ℝ) (c t : ℝ) : ℝ :=
  (c + u t) / Real.sqrt (h t + c + u t) - Real.sqrt (c + u t)

def barrierRemainder (h u up : ℝ → ℝ) (c t : ℝ) : ℝ :=
  (up t / 2) * ((Real.sqrt (c + u t))⁻¹ - (Real.sqrt (h t + c + u t))⁻¹)

theorem barrierRemainder_pos {h u up : ℝ → ℝ} {c t : ℝ}
    (hh : 0 < h t) (hb : 0 < c + u t) (hup : 0 < up t) :
    0 < barrierRemainder h u up c t := by
  apply mul_pos (half_pos hup)
  apply sub_pos.mpr
  exact (inv_lt_inv₀ (Real.sqrt_pos.mpr (by linarith)) (Real.sqrt_pos.mpr hb)).mpr
    (Real.sqrt_lt_sqrt hb.le (by linarith))

theorem hasDerivAt_barrierPrimitive {h u : ℝ → ℝ} {c t hp up : ℝ}
    (hh : HasDerivAt h hp t) (hu : HasDerivAt u up t)
    (hh0 : 0 < h t) (hb : 0 < c + u t) :
    HasDerivAt (barrierPrimitive h u c)
      ((h t * up - (c + u t) * hp) /
          (2 * (h t + c + u t) * Real.sqrt (h t + c + u t)) -
        (up / 2) * ((Real.sqrt (c + u t))⁻¹ - (Real.sqrt (h t + c + u t))⁻¹)) t := by
  have hS : 0 < h t + c + u t := by linarith
  have hsum := (hh.add_const c).add hu
  have hbase := (hu.const_add c).div (hsum.sqrt hS.ne') (Real.sqrt_pos.mpr hS).ne'
  have hder := hbase.sub ((hu.const_add c).sqrt hb.ne')
  convert hder using 1
  · rfl
  · let a := Real.sqrt (h t + c + u t)
    let b := Real.sqrt (c + u t)
    have ha : a ≠ 0 := (Real.sqrt_pos.mpr hS).ne'
    have hb' : b ≠ 0 := (Real.sqrt_pos.mpr hb).ne'
    have hs : a ^ 2 = h t + c + u t := Real.sq_sqrt hS.le
    change (h t * up - (c + u t) * hp) /
        (2 * (h t + c + u t) * a) - (up / 2) * (b⁻¹ - a⁻¹) =
      (up * a - (c + u t) * ((hp + up) / (2 * a))) / a ^ 2 - up / (2 * b)
    rw [← hs]
    have hh' : h t = a ^ 2 - (c + u t) := by linarith
    rw [hh']
    field_simp [ha, hb']
    ring

/-- This elementary estimate controls the upper boundary without subtracting
two uncontrolled divergent quantities. -/
theorem abs_barrierPrimitive_le_sqrt {h u : ℝ → ℝ} {c t : ℝ}
    (hh : 0 ≤ h t) (hb : 0 < c + u t) :
    |barrierPrimitive h u c t| ≤ Real.sqrt (h t) := by
  let a := Real.sqrt (h t + c + u t)
  let b := Real.sqrt (c + u t)
  have ha : 0 < a := Real.sqrt_pos.mpr (by linarith)
  have hb0 : 0 < b := Real.sqrt_pos.mpr hb
  have hba : b ≤ a := Real.sqrt_le_sqrt (by linarith)
  have hb2 : b ^ 2 = c + u t := Real.sq_sqrt hb.le
  have hdiff : a - b ≤ Real.sqrt (h t) := by
    have ha2 : a ^ 2 = h t + c + u t := Real.sq_sqrt (by linarith)
    have hh2 := Real.sq_sqrt hh
    have hh0 := Real.sqrt_nonneg (h t)
    nlinarith [mul_nonneg hb0.le hh0]
  have heq : barrierPrimitive h u c t = -(b / a * (a - b)) := by
    dsimp [barrierPrimitive]
    change (c + u t) / a - b = _
    rw [← hb2]
    field_simp [ha.ne']
    ring
  rw [heq, abs_neg, abs_of_nonneg (mul_nonneg (div_nonneg hb0.le ha.le) (sub_nonneg.mpr hba))]
  calc
    _ ≤ 1 * (a - b) := mul_le_mul_of_nonneg_right ((div_le_one ha).mpr hba) (sub_nonneg.mpr hba)
    _ ≤ Real.sqrt (h t) := by simpa only [one_mul] using hdiff

end EllipsoidVerification
