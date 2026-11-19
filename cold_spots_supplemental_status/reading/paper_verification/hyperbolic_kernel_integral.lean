module
public import PaperVerification.HyperbolicKernel
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
@[expose] public section
/-! # Sign of the full resolvent integral

The reciprocal pairing is carried out for the actual interval integral, including
the part below `1 / b`.  All statements retain the open parameter ranges from
Section 5.2 of the paper.
-/

noncomputable section

namespace PaperVerification.Hyperbolic

open Real Set MeasureTheory intervalIntegral

theorem resolvent_denominators_pos {a b x s : ℝ}
    (ha : 0 < a) (hx : 0 < x) (hxa : x < a ^ 2) (hxb : b ^ 2 * x < 1)
    (hs : s ∈ Icc a b) : 0 < s ^ 2 - x ∧ 0 < 1 - s ^ 2 * x := by
  have hs0 : 0 < s := ha.trans_le hs.1
  have hb0 : 0 < b := hs0.trans_le hs.2
  have has : a ^ 2 ≤ s ^ 2 := (sq_le_sq₀ ha.le hs0.le).mpr hs.1
  have hsb : s ^ 2 ≤ b ^ 2 := (sq_le_sq₀ hs0.le hb0.le).mpr hs.2
  constructor
  · linarith
  · have := mul_le_mul_of_nonneg_right hsb hx.le
    linarith

theorem continuousOn_resolventSlope {a b x : ℝ}
    (ha : 0 < a) (hx : 0 < x) (hxa : x < a ^ 2) (hxb : b ^ 2 * x < 1) :
    ContinuousOn (fun s => resolventSlope s x) (Icc a b) := by
  unfold resolventSlope
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro s hs
    obtain ⟨h₁, h₂⟩ := resolvent_denominators_pos ha hx hxa hxb hs
    exact mul_ne_zero (pow_ne_zero _ h₁.ne') (pow_ne_zero _ h₂.ne')

theorem continuousOn_density_resolventSlope {a b r x : ℝ}
    (ha : 0 < a) (hr : r ∈ Ioo 0 2) (hx : 0 < x)
    (hxa : x < a ^ 2) (hxb : b ^ 2 * x < 1) :
    ContinuousOn (fun s => branchDensity a b r s * resolventSlope s x) (Icc a b) :=
  (continuous_branchDensity a b r ⟨hr.1, by linarith [hr.2]⟩).continuousOn.mul
    (continuousOn_resolventSlope ha hx hxa hxb)

/-- The reciprocal substitution, with the Jacobian and orientation made explicit. -/
theorem integral_reciprocal_one {b : ℝ} (hb : 1 ≤ b) (f : ℝ → ℝ) :
    (∫ s in 1..b, f (1 / s) / s ^ 2) = ∫ s in (1 / b)..1, f s := by
  have hnz : ∀ s ∈ uIcc (1 : ℝ) b, s ≠ 0 := by
    rw [uIcc_of_le hb]
    intro s hs
    linarith [hs.1]
  have hc : ContinuousOn (fun s : ℝ => 1 / s) (uIcc 1 b) :=
    continuousOn_const.div continuousOn_id (fun s hs => hnz s hs)
  have hd : ∀ s ∈ Ioo (min (1 : ℝ) b) (max 1 b),
      HasDerivAt (fun s : ℝ => 1 / s) (-(1 / s ^ 2)) s := by
    intro s hs
    have hs0 : s ≠ 0 := by
      rw [min_eq_left hb, max_eq_right hb] at hs
      linarith [hs.1]
    simpa only [one_div] using hasDerivAt_inv hs0
  have hm : ∀ s ∈ Ioo (min (1 : ℝ) b) (max 1 b), -(1 / s ^ 2) ≤ 0 := by
    intro s _
    exact neg_nonpos.mpr (div_nonneg zero_le_one (sq_nonneg s))
  have h := integral_comp_mul_deriv_of_deriv_nonpos (g := f) hc hd hm
  have hfun : (fun s : ℝ => (f ∘ fun s => 1 / s) s * -(1 / s ^ 2)) =
      fun s => -(f (1 / s) / s ^ 2) := by
    funext s
    simp only [Function.comp_apply]
    ring
  rw [hfun, intervalIntegral.integral_neg, one_div_one, integral_symm (1 / b) 1] at h
  exact neg_injective h

theorem integral_resolventSlope_negative_below_one
    {a b r x : ℝ} (ha : 0 < a) (hab : a < b) (hb : b ≤ 1)
    (hr : r ∈ Ioo 0 2) (hx : 0 < x) (hxa : x < a ^ 2) (hxb : b ^ 2 * x < 1) :
    (∫ s in a..b, branchDensity a b r s * resolventSlope s x) < 0 := by
  have hax : a < 1 := hab.trans_le hb
  have hx1 : |x| < 1 := by
    rw [abs_of_pos hx]
    nlinarith only [ha, hax, hxa]
  have hcont := continuousOn_density_resolventSlope ha hr hx hxa hxb
  have hnonpos : ∀ s ∈ Icc a b, branchDensity a b r s * resolventSlope s x ≤ 0 := by
    intro s hs
    obtain ⟨h₁, h₂⟩ := resolvent_denominators_pos ha hx hxa hxb hs
    have hs1 : s ≤ 1 := hs.2.trans hb
    rcases hs1.eq_or_lt with hs1 | hs1
    · subst s
      simp [resolventSlope]
    · exact mul_nonpos_of_nonneg_of_nonpos (branchDensity_nonneg hs)
        (resolventSlope_neg (ha.le.trans hs.1) hs1 hx1 h₁.ne' h₂.ne').le
  have hpos : 0 < ∫ s in a..b, -(branchDensity a b r s * resolventSlope s x) := by
    refine integral_pos hab hcont.neg (fun s hs => neg_nonneg.mpr (hnonpos s ⟨hs.1.le, hs.2⟩)) ?_
    let m := (a + b) / 2
    have hm : m ∈ Ioo a b := by dsimp [m]; constructor <;> linarith
    obtain ⟨h₁, h₂⟩ := resolvent_denominators_pos ha hx hxa hxb ⟨hm.1.le, hm.2.le⟩
    exact ⟨m, ⟨hm.1.le, hm.2.le⟩, neg_pos.mpr
      (mul_neg_of_pos_of_neg (branchDensity_pos hm)
        (resolventSlope_neg (ha.le.trans hm.1.le) (hm.2.trans_le hb) hx1 h₁.ne' h₂.ne'))⟩
  rw [intervalIntegral.integral_neg] at hpos
  linarith

/-- Strict negativity of equation (22), for every admissible real parameter. -/
theorem integral_resolventSlope_neg
    {a b r x : ℝ} (ha : 0 < a) (hab : a < b) (hab1 : a * b < 1)
    (hr : r ∈ Ioo 0 2) (hx : 0 < x) (hxa : x < a ^ 2) (hxb : b ^ 2 * x < 1) :
    (∫ s in a..b, branchDensity a b r s * resolventSlope s x) < 0 := by
  by_cases hb : b ≤ 1
  · exact integral_resolventSlope_negative_below_one ha hab hb hr hx hxa hxb
  have hb1 : 1 < b := lt_of_not_ge hb
  have hb0 : 0 < b := zero_lt_one.trans hb1
  have hai : a < 1 / b := (lt_div_iff₀ hb0).mpr (by simpa using hab1)
  have hi0 : 0 < 1 / b := div_pos zero_lt_one hb0
  have hi1 : 1 / b < 1 := (div_lt_iff₀ hb0).mpr (by simpa using hb1)
  have ha1 : a < 1 := hai.trans hi1
  have hx1 : |x| < 1 := by
    rw [abs_of_pos hx]
    nlinarith only [ha, ha1, hxa]
  let f : ℝ → ℝ := fun s => branchDensity a b r s * resolventSlope s x
  let paired : ℝ → ℝ := fun s =>
    resolventSlope s x * (branchDensity a b r s - s ^ 4 * branchDensity a b r (1 / s))
  have hcont : ContinuousOn f (Icc a b) := continuousOn_density_resolventSlope ha hr hx hxa hxb
  have hsub₁ : Icc a (1 / b) ⊆ Icc a b := fun s hs => ⟨hs.1, hs.2.trans (hi1.le.trans hb1.le)⟩
  have hsub₂ : Icc (1 / b) 1 ⊆ Icc a b := fun s hs => ⟨hai.le.trans hs.1, hs.2.trans hb1.le⟩
  have hsub₃ : Icc 1 b ⊆ Icc a b := fun s hs => ⟨ha1.le.trans hs.1, hs.2⟩
  have hi₁ : IntervalIntegrable f volume a (1 / b) := (hcont.mono hsub₁).intervalIntegrable_of_Icc hai.le
  have hi₂ : IntervalIntegrable f volume (1 / b) 1 := (hcont.mono hsub₂).intervalIntegrable_of_Icc hi1.le
  have hi₃ : IntervalIntegrable f volume 1 b := (hcont.mono hsub₃).intervalIntegrable_of_Icc hb1.le
  have hrec : ∀ s ∈ Icc 1 b, 1 / s ∈ Icc a b := by
    intro s hs
    have hs0 : 0 < s := zero_lt_one.trans_le hs.1
    constructor
    · apply (le_div_iff₀ hs0).mpr
      have := mul_le_mul_of_nonneg_left hs.2 ha.le
      linarith
    · apply (div_le_iff₀ hs0).mpr
      have := mul_le_mul_of_nonneg_left hs.1 hb0.le
      linarith
  have hreccont : ContinuousOn (fun s : ℝ => 1 / s) (Icc 1 b) :=
    continuousOn_const.div continuousOn_id (fun s hs => by linarith [hs.1])
  have hrecf : ContinuousOn (fun s => f (1 / s) / s ^ 2) (Icc 1 b) :=
    (hcont.comp hreccont hrec).div (continuousOn_id.pow 2)
      (fun s hs => pow_ne_zero _ (by linarith [hs.1]))
  have hpair : ∀ s ∈ Icc 1 b, f s + f (1 / s) / s ^ 2 = paired s := by
    intro s hs
    obtain ⟨h₁, h₂⟩ := resolvent_denominators_pos ha hx hxa hxb (hsub₃ hs)
    have hs0 : s ≠ 0 := by linarith [hs.1]
    dsimp [f, paired]
    rw [resolventSlope_reciprocal s x hs0 h₁.ne' h₂.ne']
    field_simp [hs0]
    ring
  have hpairint : (∫ s in (1 / b)..1, f s) + (∫ s in 1..b, f s) =
      ∫ s in 1..b, paired s := by
    rw [← integral_reciprocal_one hb1.le f, add_comm,
      ← intervalIntegral.integral_add hi₃ (hrecf.intervalIntegrable_of_Icc hb1.le)]
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hb1.le]
    exact hpair
  have hpairnonpos : (∫ s in 1..b, paired s) ≤ 0 := by
    have hnonneg : 0 ≤ ∫ s in 1..b, -paired s := by
      apply integral_nonneg hb1.le
      intro s hs
      apply neg_nonneg.mpr
      obtain ⟨h₁, h₂⟩ := resolvent_denominators_pos ha hx hxa hxb (hsub₃ hs)
      rcases hs.1.eq_or_lt with hs1 | hs1
      · rw [← hs1]
        simp [paired, resolventSlope]
      · rcases hs.2.eq_or_lt with hsb | hsb
        · subst s
          have hρ : 0 ≤ branchDensity a b r (1 / b) := branchDensity_nonneg (hrec b ⟨hb1.le, le_rfl⟩)
          have hρb : branchDensity a b r b = 0 := by
            simp [branchDensity, Real.zero_rpow (by linarith [hr.2] : 4 - r ≠ 0)]
          dsimp [paired]
          rw [hρb]
          exact mul_nonpos_of_nonneg_of_nonpos
            (resolventSlope_pos hb1 hx1 h₁.ne' h₂.ne').le
            (by simpa only [zero_sub] using
              neg_nonpos.mpr (mul_nonneg (pow_nonneg hb0.le 4) hρ))
        · exact (paired_resolventSlope_neg ha hab1 hr ⟨hs1, hsb⟩ hx1 h₁.ne' h₂.ne').le
    rw [intervalIntegral.integral_neg] at hnonneg
    linarith
  have hleft : (∫ s in a..(1 / b), f s) < 0 := by
    have hnonpos : ∀ s ∈ Icc a (1 / b), f s ≤ 0 := by
      intro s hs
      obtain ⟨h₁, h₂⟩ := resolvent_denominators_pos ha hx hxa hxb (hsub₁ hs)
      exact mul_nonpos_of_nonneg_of_nonpos (branchDensity_nonneg (hsub₁ hs))
        (resolventSlope_neg (ha.le.trans hs.1) (hs.2.trans_lt hi1) hx1 h₁.ne' h₂.ne').le
    have hpos : 0 < ∫ s in a..(1 / b), -f s := by
      refine integral_pos hai (hcont.mono hsub₁).neg
        (fun s hs => neg_nonneg.mpr (hnonpos s ⟨hs.1.le, hs.2⟩)) ?_
      let m := (a + 1 / b) / 2
      have hm : m ∈ Ioo a (1 / b) := by dsimp [m]; constructor <;> linarith
      have hmb : m ∈ Ioo a b := ⟨hm.1, hm.2.trans (hi1.trans hb1)⟩
      obtain ⟨h₁, h₂⟩ := resolvent_denominators_pos ha hx hxa hxb ⟨hmb.1.le, hmb.2.le⟩
      exact ⟨m, ⟨hm.1.le, hm.2.le⟩, neg_pos.mpr
        (mul_neg_of_pos_of_neg (branchDensity_pos hmb)
          (resolventSlope_neg (ha.le.trans hm.1.le) (hm.2.trans hi1) hx1 h₁.ne' h₂.ne'))⟩
    rw [intervalIntegral.integral_neg] at hpos
    linarith
  have hsplit := integral_add_adjacent_intervals (hi₁.trans hi₂) hi₃
  rw [← integral_add_adjacent_intervals hi₁ hi₂, add_assoc, hpairint] at hsplit
  change (∫ s in a..b, f s) < 0
  linarith

end PaperVerification.Hyperbolic

#print axioms PaperVerification.Hyperbolic.integral_resolventSlope_neg
