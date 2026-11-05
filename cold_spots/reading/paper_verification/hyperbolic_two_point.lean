module
public import PaperVerification.HyperbolicLocalization
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Tactic.LinearCombination
@[expose] public section
/-! # The literal two-point functional

The definitions below are equation (14), including endpoint atoms and the
degenerate weights.  Subsequent scale and boundary arguments use this same
functional throughout.
-/

noncomputable section

namespace PaperVerification.Hyperbolic

open Real Set

def twoPointNumerator (R p q w : ℝ) : ℝ :=
  Real.cosh p ^ (4 * w) * Real.cosh q ^ (4 * (1 - w)) +
    Real.cosh (R - p) ^ (4 * w) * Real.cosh (R - q) ^ (4 * (1 - w)) -
    Real.sinh p ^ (4 * w) * Real.sinh q ^ (4 * (1 - w)) -
    Real.sinh (R - p) ^ (4 * w) * Real.sinh (R - q) ^ (4 * (1 - w))

def twoPointDenominator (R p q w : ℝ) : ℝ :=
  2 * Real.cosh R * Real.cosh (2 * p - R) ^ w * Real.cosh (2 * q - R) ^ (1 - w)

def twoPointRatio (R p q w : ℝ) : ℝ :=
  twoPointNumerator R p q w / twoPointDenominator R p q w

theorem twoPointDenominator_pos (R p q w : ℝ) : 0 < twoPointDenominator R p q w :=
  mul_pos (mul_pos (mul_pos (by norm_num) (Real.cosh_pos _))
    (Real.rpow_pos_of_pos (Real.cosh_pos _) _))
    (Real.rpow_pos_of_pos (Real.cosh_pos _) _)

theorem cosh_fourth_sub_sinh_fourth (p : ℝ) :
    Real.cosh p ^ 4 - Real.sinh p ^ 4 = Real.cosh (2 * p) := by
  rw [Real.cosh_two_mul]
  linear_combination (Real.cosh p ^ 2 + Real.sinh p ^ 2) * Real.cosh_sq_sub_sinh_sq p

theorem cosh_two_reflected_sum (R p : ℝ) :
    Real.cosh (2 * p) + Real.cosh (2 * (R - p)) =
      2 * Real.cosh R * Real.cosh (2 * p - R) := by
  have h₁ : 2 * p = R + (2 * p - R) := by ring
  have h₂ : 2 * (R - p) = R - (2 * p - R) := by ring
  calc
    Real.cosh (2*p)+Real.cosh (2*(R-p)) =
        Real.cosh (R+(2*p-R))+Real.cosh (R-(2*p-R)) :=
      congrArg₂ (· + ·) (congrArg Real.cosh h₁) (congrArg Real.cosh h₂)
    _ = 2*Real.cosh R*Real.cosh (2*p-R) := by
      rw [Real.cosh_add R (2*p-R),Real.cosh_sub R (2*p-R)]
      ring

theorem twoPointNumerator_weight_zero (R p q : ℝ) :
    twoPointNumerator R p q 0 = 2 * Real.cosh R * Real.cosh (2 * q - R) := by
  unfold twoPointNumerator
  norm_num only [mul_zero, sub_zero, mul_one, Real.rpow_zero, one_mul, Real.rpow_ofNat]
  calc
    _ = (Real.cosh q ^ 4 - Real.sinh q ^ 4) +
        (Real.cosh (R - q) ^ 4 - Real.sinh (R - q) ^ 4) := by ring
    _ = _ := by rw [cosh_fourth_sub_sinh_fourth, cosh_fourth_sub_sinh_fourth,
      cosh_two_reflected_sum]

theorem twoPointNumerator_weight_one (R p q : ℝ) :
    twoPointNumerator R p q 1 = 2 * Real.cosh R * Real.cosh (2 * p - R) := by
  unfold twoPointNumerator
  norm_num only [mul_one, sub_self, mul_zero, Real.rpow_zero, mul_one, Real.rpow_ofNat]
  calc
    _ = (Real.cosh p ^ 4 - Real.sinh p ^ 4) +
        (Real.cosh (R - p) ^ 4 - Real.sinh (R - p) ^ 4) := by ring
    _ = _ := by rw [cosh_fourth_sub_sinh_fourth, cosh_fourth_sub_sinh_fourth,
      cosh_two_reflected_sum]

@[simp] theorem twoPointRatio_weight_zero (R p q : ℝ) : twoPointRatio R p q 0 = 1 := by
  unfold twoPointRatio
  rw [twoPointNumerator_weight_zero]
  simp only [twoPointDenominator, sub_zero, Real.rpow_zero, Real.rpow_one, mul_one]
  exact div_self (mul_ne_zero (mul_ne_zero (by norm_num) (Real.cosh_pos _).ne') (Real.cosh_pos _).ne')

@[simp] theorem twoPointRatio_weight_one (R p q : ℝ) : twoPointRatio R p q 1 = 1 := by
  unfold twoPointRatio
  rw [twoPointNumerator_weight_one]
  simp only [twoPointDenominator, sub_self, Real.rpow_zero, Real.rpow_one, mul_one]
  exact div_self (mul_ne_zero (mul_ne_zero (by norm_num) (Real.cosh_pos _).ne') (Real.cosh_pos _).ne')

theorem twoPointNumerator_same {R p : ℝ} (hp : p ∈ Icc 0 R) (w : ℝ) :
    twoPointNumerator R p p w = 2 * Real.cosh R * Real.cosh (2 * p - R) := by
  have hfour (x : ℝ) (hx : 0 ≤ x) : x ^ (4 * w) * x ^ (4 * (1 - w)) = x ^ 4 := by
    rw [← Real.rpow_add' hx (by ring_nf; norm_num : 4 * w + 4 * (1 - w) ≠ 0),
      show 4 * w + 4 * (1 - w) = (4 : ℝ) by ring, Real.rpow_ofNat]
  unfold twoPointNumerator
  rw [hfour _ (Real.cosh_pos _).le, hfour _ (Real.cosh_pos _).le,
    hfour _ (Real.sinh_nonneg_iff.mpr hp.1),
    hfour _ (Real.sinh_nonneg_iff.mpr (sub_nonneg.mpr hp.2))]
  calc
    _ = (Real.cosh p ^ 4 - Real.sinh p ^ 4) +
        (Real.cosh (R - p) ^ 4 - Real.sinh (R - p) ^ 4) := by ring
    _ = _ := by rw [cosh_fourth_sub_sinh_fourth, cosh_fourth_sub_sinh_fourth,
      cosh_two_reflected_sum]

theorem twoPointRatio_same {R p : ℝ} (hp : p ∈ Icc 0 R) (w : ℝ) :
    twoPointRatio R p p w = 1 := by
  have hden : twoPointDenominator R p p w = 2 * Real.cosh R * Real.cosh (2 * p - R) := by
    unfold twoPointDenominator
    rw [mul_assoc, ← Real.rpow_add (Real.cosh_pos _) w (1 - w),
      show w + (1 - w) = (1 : ℝ) by ring, Real.rpow_one]
  unfold twoPointRatio
  rw [twoPointNumerator_same hp, hden]
  exact div_self (mul_ne_zero (mul_ne_zero (by norm_num) (Real.cosh_pos _).ne') (Real.cosh_pos _).ne')

theorem twoPointRatio_reflect (R p q w : ℝ) :
    twoPointRatio R (R - q) (R - p) (1 - w) = twoPointRatio R p q w := by
  have hsub : 1 - (1 - w) = w := by ring
  have hp : R - (R - p) = p := by ring
  have hq : R - (R - q) = q := by ring
  have hp' : 2 * (R - p) - R = -(2 * p - R) := by ring
  have hq' : 2 * (R - q) - R = -(2 * q - R) := by ring
  unfold twoPointRatio twoPointNumerator twoPointDenominator
  rw [hsub, hp, hq, hp', hq', Real.cosh_neg, Real.cosh_neg]
  congr 1 <;> ring

theorem weighted_cosh_product_gt_sinh_product {p q r s : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 < r) (hs : 0 < s) :
    Real.sinh p ^ r * Real.sinh q ^ s < Real.cosh p ^ r * Real.cosh q ^ s := by
  have hp' := Real.rpow_lt_rpow (Real.sinh_nonneg_iff.mpr hp) (Real.sinh_lt_cosh p) hr
  have hq' := Real.rpow_lt_rpow (Real.sinh_nonneg_iff.mpr hq) (Real.sinh_lt_cosh q) hs
  exact (mul_le_mul_of_nonneg_left hq'.le
    (Real.rpow_nonneg (Real.sinh_nonneg_iff.mpr hp) r)).trans_lt
      (mul_lt_mul_of_pos_right hp' (Real.rpow_pos_of_pos (Real.cosh_pos q) s))

theorem twoPointNumerator_pos {R p q w : ℝ}
    (hp : p ∈ Icc 0 R) (hq : q ∈ Icc 0 R) (hw : w ∈ Icc 0 1) :
    0 < twoPointNumerator R p q w := by
  rcases hw.1.eq_or_lt with hw0 | hw0
  · rw [← hw0, twoPointNumerator_weight_zero]
    positivity
  rcases hw.2.eq_or_lt with hw1 | hw1
  · rw [hw1, twoPointNumerator_weight_one]
    positivity
  have h4w : 0 < 4*w := mul_pos (by norm_num : (0:ℝ)<4) hw0
  have h4c : 0 < 4*(1-w) := mul_pos (by norm_num : (0:ℝ)<4) (sub_pos.mpr hw1)
  have h₁ := weighted_cosh_product_gt_sinh_product hp.1 hq.1 h4w h4c
  have h₂ := weighted_cosh_product_gt_sinh_product (sub_nonneg.mpr hp.2) (sub_nonneg.mpr hq.2)
    h4w h4c
  unfold twoPointNumerator
  linarith

theorem twoPointRatio_pos {R p q w : ℝ}
    (hp : p ∈ Icc 0 R) (hq : q ∈ Icc 0 R) (hw : w ∈ Icc 0 1) :
    0 < twoPointRatio R p q w :=
  div_pos (twoPointNumerator_pos hp hq hw) (twoPointDenominator_pos _ _ _ _)

theorem twoPointNumerator_half (R p q : ℝ) :
    twoPointNumerator R p q (1 / 2) =
      Real.cosh R * (Real.cosh (2 * p - R) + Real.cosh (2 * q - R)) := by
  have hprod (a b : ℝ) : Real.cosh a ^ 2 * Real.cosh b ^ 2 -
      Real.sinh a ^ 2 * Real.sinh b ^ 2 = (Real.cosh (2 * a) + Real.cosh (2 * b)) / 2 := by
    rw [Real.cosh_two_mul, Real.cosh_two_mul]
    linear_combination (Real.cosh b ^ 2 + Real.sinh b ^ 2) / 2 * Real.cosh_sq_sub_sinh_sq a +
      (Real.cosh a ^ 2 + Real.sinh a ^ 2) / 2 * Real.cosh_sq_sub_sinh_sq b
  unfold twoPointNumerator
  norm_num only [show (4 : ℝ) * (1 / 2) = 2 by norm_num,
    show (4 : ℝ) * (1 - 1 / 2) = 2 by norm_num, Real.rpow_ofNat]
  calc
    _ = (Real.cosh p ^ 2 * Real.cosh q ^ 2 - Real.sinh p ^ 2 * Real.sinh q ^ 2) +
        (Real.cosh (R - p) ^ 2 * Real.cosh (R - q) ^ 2 -
          Real.sinh (R - p) ^ 2 * Real.sinh (R - q) ^ 2) := by ring
    _ = _ := by
      rw [hprod, hprod]
      linear_combination (cosh_two_reflected_sum R p) / 2 + (cosh_two_reflected_sum R q) / 2

theorem twoPointRatio_half_ge_one (R p q : ℝ) : 1 ≤ twoPointRatio R p q (1 / 2) := by
  have ham := Real.geom_mean_le_arith_mean2_weighted
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (Real.cosh_pos (2 * p - R)).le (Real.cosh_pos (2 * q - R)).le (by norm_num : (1 : ℝ) / 2 + 1 / 2 = 1)
  apply (le_div_iff₀ (twoPointDenominator_pos _ _ _ _)).mpr
  rw [one_mul, twoPointNumerator_half]
  unfold twoPointDenominator
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
  have h := mul_le_mul_of_nonneg_left ham
    (mul_pos (by norm_num : (0:ℝ)<2) (Real.cosh_pos R)).le
  nlinarith only [h]

theorem twoPointRatio_half_eq_one_iff (R p q : ℝ) :
    twoPointRatio R p q (1 / 2) = 1 ↔ p = q ∨ p + q = R := by
  let A := Real.cosh (2 * p - R)
  let B := Real.cosh (2 * q - R)
  have hmean : A ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ) = A / 2 + B / 2 ↔ A = B := by
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using
      (Real.geom_mean_eq_arith_mean2_weighted_iff_of_pos (p₁:=A) (p₂:=B)
        (show (0 : ℝ) < 1 / 2 by norm_num) (show (0 : ℝ) < 1 / 2 by norm_num)
        (Real.cosh_pos (2 * p - R)).le (Real.cosh_pos (2 * q - R)).le
        (by norm_num : (1 : ℝ) / 2 + 1 / 2 = 1))
  have hratio : twoPointRatio R p q (1 / 2) = 1 ↔ A = B := by
    rw [twoPointRatio, div_eq_one_iff_eq (twoPointDenominator_pos _ _ _ _).ne',
      twoPointNumerator_half]
    unfold twoPointDenominator
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
    change Real.cosh R * (A + B) = 2 * Real.cosh R * A ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ) ↔ A = B
    rw [← hmean]
    constructor <;> intro h
    · apply (mul_left_cancel₀ (Real.cosh_pos R).ne')
      nlinarith only [h]
    · rw [show 2 * Real.cosh R * A ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ) =
        2 * Real.cosh R * (A ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ)) by ring, h]
      ring
  rw [hratio]
  constructor
  · intro h
    have he : |2 * p - R| = |2 * q - R| := le_antisymm
      (Real.cosh_le_cosh.mp h.le) (Real.cosh_le_cosh.mp h.ge)
    rcases abs_eq_abs.mp he with h | h
    · left; linarith
    · right; linarith
  · rintro (rfl | h)
    · rfl
    · change Real.cosh (2 * p - R) = Real.cosh (2 * q - R)
      have he : 2 * p - R = -(2 * q - R) := by linarith
      rw [he, Real.cosh_neg]

theorem continuous_twoPointRatio {w : ℝ} (hw : w ∈ Ioo 0 1) :
    Continuous (fun x : ℝ × ℝ × ℝ => twoPointRatio x.1 x.2.1 x.2.2 w) := by
  have he₁ : 0 ≤ 4 * w := (mul_pos (by norm_num) hw.1).le
  have he₂ : 0 ≤ 4 * (1 - w) := (mul_pos (by norm_num) (sub_pos.mpr hw.2)).le
  have hc (f : (ℝ × ℝ × ℝ) → ℝ) (hf : Continuous f) (s : ℝ) :
      Continuous (fun x => Real.cosh (f x) ^ s) :=
    (Real.continuous_cosh.comp hf).rpow_const (fun x => Or.inl (Real.cosh_pos _).ne')
  have hs (f : (ℝ × ℝ × ℝ) → ℝ) (hf : Continuous f) (s : ℝ) (h : 0 ≤ s) :
      Continuous (fun x => Real.sinh (f x) ^ s) :=
    (Real.continuous_sinh.comp hf).rpow_const (fun x => Or.inr h)
  unfold twoPointRatio
  apply Continuous.div
  · unfold twoPointNumerator
    exact (((hc _ continuous_snd.fst _).mul (hc _ continuous_snd.snd _)).add
      ((hc _ (continuous_fst.sub continuous_snd.fst) _).mul
        (hc _ (continuous_fst.sub continuous_snd.snd) _))).sub
      ((hs _ continuous_snd.fst _ he₁).mul (hs _ continuous_snd.snd _ he₂)) |>.sub
      ((hs _ (continuous_fst.sub continuous_snd.fst) _ he₁).mul
        (hs _ (continuous_fst.sub continuous_snd.snd) _ he₂))
  · unfold twoPointDenominator
    exact ((continuous_const.mul (Real.continuous_cosh.comp continuous_fst)).mul
      (hc _ ((continuous_const.mul continuous_snd.fst).sub continuous_fst) _)).mul
      (hc _ ((continuous_const.mul continuous_snd.snd).sub continuous_fst) _)
  · exact fun x => (twoPointDenominator_pos _ _ _ _).ne'

end PaperVerification.Hyperbolic

#print axioms PaperVerification.Hyperbolic.twoPointRatio_half_ge_one
#print axioms PaperVerification.Hyperbolic.continuous_twoPointRatio
