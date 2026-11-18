module
public import PaperVerification.HyperbolicExponential
public import PaperVerification.HyperbolicDeficits
public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.Analysis.Calculus.Deriv.Slope
@[expose] public section
/-! # The exact limit at large scale

The limit is proved from derivatives at zero of two real functions.  In
particular no asymptotic expansion, formal power series, or omitted remainder
estimate is used.
-/

noncomputable section

namespace PaperVerification.Hyperbolic

open Real Set Filter Topology

def reverseBranch (a b r t : ℝ) : ℝ := |1 + a * t| ^ r * |1 + b * t| ^ (4 - r)

def centeredLimit (v₁ v₂ w : ℝ) : ℝ :=
  (w * Real.cosh (v₁ - 2 * centeredMean v₁ v₂ w) +
      (1 - w) * Real.cosh (v₂ - 2 * centeredMean v₁ v₂ w)) /
    centeredCoshMean v₁ v₂ w

theorem branchPower_homogeneity {a b r z : ℝ} (hz : 0 < z) (t : ℝ) :
    z ^ 4 * branchPower a b r (t / z) = |t + a * z| ^ r * |t + b * z| ^ (4 - r) := by
  have h₁ : t / z + a = (t + a * z) / z := by field_simp [hz.ne']
  have h₂ : t / z + b = (t + b * z) / z := by field_simp [hz.ne']
  unfold branchPower
  rw [h₁, h₂, abs_div, abs_div, abs_of_pos hz,
    Real.div_rpow (abs_nonneg _) hz.le, Real.div_rpow (abs_nonneg _) hz.le,
    div_mul_div_comm, ← Real.rpow_add hz, show r + (4 - r) = (4 : ℝ) by ring,
    Real.rpow_ofNat]
  exact mul_div_cancel₀ _ (pow_ne_zero _ hz.ne')

theorem quarticTransform_eq_symmetric_difference {a b r z : ℝ} (hz : 0 < z) :
    quarticTransform z (branchPower a b r) =
      ((branchPower a b r z + reverseBranch a b r z) -
        (branchPower a b r (-z) + reverseBranch a b r (-z))) / (z * (1 + z ^ 2)) := by
  have hplus : z ^ 4 * branchPower a b r (1 / z) = reverseBranch a b r z := by
    simpa only [reverseBranch] using branchPower_homogeneity (a := a) (b := b) (r := r) hz 1
  have hminus : z ^ 4 * branchPower a b r (-1 / z) = reverseBranch a b r (-z) := by
    rw [branchPower_homogeneity hz (-1)]
    unfold reverseBranch
    rw [show -1 + a * z = -(1 + a * (-z)) by ring,
      show -1 + b * z = -(1 + b * (-z)) by ring, abs_neg, abs_neg]
  unfold quarticTransform
  rw [mul_sub, hplus, hminus]
  congr 1 <;> ring

theorem hasDerivAt_branchPower_zero {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) :
    HasDerivAt (branchPower a b r)
      (a ^ r * b ^ (4 - r) * (r / a + (4 - r) / b)) 0 := by
  have hda : HasDerivAt (fun t : ℝ => |t + a|) 1 0 := by
    simpa only [Function.comp_def, id_eq, Pi.add_apply, zero_add, one_mul] using
      (hasDerivAt_abs_pos (show 0 < (0 : ℝ) + a by simpa only [zero_add] using ha)).comp 0
        ((hasDerivAt_id 0).add_const a)
  have hdb : HasDerivAt (fun t : ℝ => |t + b|) 1 0 := by
    simpa only [Function.comp_def, id_eq, Pi.add_apply, zero_add, one_mul] using
      (hasDerivAt_abs_pos (show 0 < (0 : ℝ) + b by simpa only [zero_add] using hb)).comp 0
        ((hasDerivAt_id 0).add_const b)
  have hd := hasDerivAt_rpow_product_logarithmic (r := r) (s := 4 - r) hda hdb
    (by simpa only [zero_add, abs_of_pos ha] using ha)
    (by simpa only [zero_add, abs_of_pos hb] using hb)
  change HasDerivAt (fun t : ℝ => |t + a| ^ r * |t + b| ^ (4 - r)) _ 0
  simpa only [zero_add, abs_of_pos ha, abs_of_pos hb, mul_one] using hd

theorem hasDerivAt_reverseBranch_zero (a b r : ℝ) :
    HasDerivAt (reverseBranch a b r) (r * a + (4 - r) * b) 0 := by
  have hda : HasDerivAt (fun t : ℝ => |1 + a * t|) a 0 := by
    simpa only [Function.comp_def, id_eq, Pi.add_apply, Pi.mul_apply,
      mul_zero, add_zero, one_mul, mul_one, zero_add] using
      (hasDerivAt_abs_pos (show 0 < (1 : ℝ) + a * 0 by simp)).comp 0
        ((hasDerivAt_const 0 (1 : ℝ)).add ((hasDerivAt_id 0).const_mul a))
  have hdb : HasDerivAt (fun t : ℝ => |1 + b * t|) b 0 := by
    simpa only [Function.comp_def, id_eq, Pi.add_apply, Pi.mul_apply,
      mul_zero, add_zero, one_mul, mul_one, zero_add] using
      (hasDerivAt_abs_pos (show 0 < (1 : ℝ) + b * 0 by simp)).comp 0
        ((hasDerivAt_const 0 (1 : ℝ)).add ((hasDerivAt_id 0).const_mul b))
  have hd := hasDerivAt_rpow_product_logarithmic (r := r) (s := 4 - r) hda hdb
    (by simp) (by simp)
  change HasDerivAt (fun t : ℝ => |1 + a * t| ^ r * |1 + b * t| ^ (4 - r)) _ 0
  simpa only [mul_zero, add_zero, abs_one, Real.one_rpow, mul_one, one_mul, div_one] using hd

theorem tendsto_quarticTransform_zero {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun z => quarticTransform z (branchPower a b r)) (𝓝[>] 0)
      (𝓝 (2 * (a ^ r * b ^ (4 - r) * (r / a + (4 - r) / b) + r * a + (4 - r) * b))) := by
  let f := fun t => branchPower a b r t + reverseBranch a b r t
  let d := a ^ r * b ^ (4 - r) * (r / a + (4 - r) / b) + r * a + (4 - r) * b
  have hd : HasDerivAt f d 0 := by
    have h : HasDerivAt
        (fun t : ℝ => branchPower a b r t + reverseBranch a b r t)
        (a ^ r * b ^ (4 - r) * (r / a + (4 - r) / b) +
          (r * a + (4 - r) * b)) 0 :=
      (hasDerivAt_branchPower_zero (r := r) ha hb).fun_add
        (hasDerivAt_reverseBranch_zero a b r)
    have he : a ^ r * b ^ (4 - r) * (r / a + (4 - r) / b) +
        (r * a + (4 - r) * b) = d := by dsimp [d]; ring
    exact h.congr_deriv he
  have hsym : HasDerivAt (fun t => f t - f (-t)) (2 * d) 0 := by
    have hneg : HasDerivAt (fun t => f (-t)) (-d) 0 := by
      simpa only [Function.comp_def, mul_neg_one] using
        hd.comp_of_eq 0 (hasDerivAt_neg (0 : ℝ)) (by simp only [neg_zero])
    have he : d - -d = 2 * d := by ring
    have hh : HasDerivAt (fun t : ℝ => f t - f (-t)) (d - -d) 0 := hd.fun_sub hneg
    exact hh.congr_deriv he
  have hlim : Tendsto (fun t => (f t - f (-t)) / t) (𝓝[>] 0) (𝓝 (2 * d)) := by
    simpa only [zero_add, neg_zero, sub_self, sub_zero, smul_eq_mul, div_eq_mul_inv, mul_comm] using
      hsym.tendsto_slope_zero_right
  have hden : Tendsto (fun t : ℝ => 1 + t ^ 2) (𝓝[>] 0) (𝓝 1) := by
    have ht : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
      (continuous_id.continuousAt : ContinuousAt (fun t : ℝ => t) 0).tendsto.mono_left
        nhdsWithin_le_nhds
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] using
      (show Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) from
        tendsto_const_nhds).add (ht.pow 2)
  have hlim' := hlim.div hden (by norm_num : (1 : ℝ) ≠ 0)
  simp only [div_one] at hlim'
  apply hlim'.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [quarticTransform_eq_symmetric_difference hz]
  change ((f z - f (-z)) / z) / (1 + z ^ 2) = _
  rw [div_div]

theorem centered_limit_coefficient (v₁ v₂ w : ℝ) :
    centeredFactor v₁ v₂ w *
      (2 * (Real.exp v₁ ^ (4 * w) * Real.exp v₂ ^ (4 - 4 * w) *
          ((4 * w) / Real.exp v₁ + (4 - 4 * w) / Real.exp v₂) +
        (4 * w) * Real.exp v₁ + (4 - 4 * w) * Real.exp v₂)) = centeredLimit v₁ v₂ w := by
  let M := centeredMean v₁ v₂ w
  let H := centeredCoshMean v₁ v₂ w
  have hp : Real.exp v₁ ^ (4 * w) * Real.exp v₂ ^ (4 - 4 * w) = Real.exp (4 * M) := by
    rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
    congr 1
    dsimp [M, centeredMean]
    ring
  have hn (v : ℝ) : Real.exp (-2 * M) * (Real.exp (4 * M) / Real.exp v) =
      Real.exp (2 * M - v) := by
    rw [← mul_div_assoc, ← Real.exp_add, ← Real.exp_sub]
    congr 1
    ring
  have hp' (v : ℝ) : Real.exp (-2 * M) * Real.exp v = Real.exp (v - 2 * M) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hp]
  unfold centeredFactor centeredLimit
  change Real.exp (-2 * M) / (16 * H) * (2 * (Real.exp (4 * M) * _ + _ + _)) =
    (w * Real.cosh (v₁ - 2 * M) + (1 - w) * Real.cosh (v₂ - 2 * M)) / H
  calc
    _ = (w * (Real.exp (-2 * M) * (Real.exp (4 * M) / Real.exp v₁)) +
        (1 - w) * (Real.exp (-2 * M) * (Real.exp (4 * M) / Real.exp v₂)) +
        w * (Real.exp (-2 * M) * Real.exp v₁) +
        (1 - w) * (Real.exp (-2 * M) * Real.exp v₂)) / (2 * H) := by ring
    _ = _ := by
      rw [hn, hn, hp', hp', Real.cosh_eq, Real.cosh_eq,
        show -(v₁ - 2 * M) = 2 * M - v₁ by ring,
        show -(v₂ - 2 * M) = 2 * M - v₂ by ring]
      ring

/-- Equation (23), with the limit and the geometric normalization made exact. -/
theorem tendsto_centeredRatio_atTop (v₁ v₂ w : ℝ) :
    Tendsto (centeredRatio v₁ v₂ w) atTop (𝓝 (centeredLimit v₁ v₂ w)) := by
  have hz : Tendsto (fun R : ℝ => Real.exp (-R)) atTop (𝓝[>] 0) :=
    Real.tendsto_exp_atBot_nhdsGT.comp tendsto_neg_atTop_atBot
  have hlim := (tendsto_quarticTransform_zero (r := 4 * w) (Real.exp_pos v₁) (Real.exp_pos v₂)).comp hz
  have hlim' := hlim.const_mul (centeredFactor v₁ v₂ w)
  rw [centered_limit_coefficient] at hlim'
  apply hlim'.congr'
  filter_upwards [eventually_ge_atTop (max |v₁| |v₂|)] with R hR
  have h₁ : v₁ ∈ Icc (-R) R := by
    have h := (le_max_left |v₁| |v₂|).trans hR
    exact abs_le.mp h
  have h₂ : v₂ ∈ Icc (-R) R := by
    have h := (le_max_right |v₁| |v₂|).trans hR
    exact abs_le.mp h
  exact (centeredRatio_eq_quarticTransform h₁ h₂ w).symm

theorem centeredLimit_gt_one {v₁ v₂ w : ℝ}
    (hv : v₁ < v₂) (hs : v₁ + v₂ < 0) (hw : w ∈ Ioo 0 1) :
    1 < centeredLimit v₁ v₂ w := by
  have hmean : centeredCoshMean v₁ v₂ w =
      Real.exp (w * Real.log (Real.cosh v₁) + (1 - w) * Real.log (Real.cosh v₂)) := by
    unfold centeredCoshMean
    rw [Real.rpow_def_of_pos (Real.cosh_pos _), Real.rpow_def_of_pos (Real.cosh_pos _), ← Real.exp_add]
    congr 1
    ring
  apply (lt_div_iff₀ (centeredCoshMean_pos _ _ _)).mpr
  rw [one_mul, hmean]
  exact two_point_centered_cosh_gt_geometric hw hv hs

theorem branchPower_one_polynomial {a b t : ℝ} (hab : a < b) (ht : OutsideCut a b t) :
    branchPower a b 1 t = (t + a) * (t + b) ^ 3 := by
  unfold branchPower
  norm_num only [Real.rpow_one, show (4 : ℝ) - 1 = 3 by norm_num, Real.rpow_ofNat]
  rcases ht with ht | ht
  · rw [abs_of_pos (show 0 < t + a by linarith), abs_of_pos (show 0 < t + b by linarith)]
  · rw [abs_of_neg (show t + a < 0 by linarith), abs_of_neg (show t + b < 0 by linarith)]
    ring

theorem quarticTransform_branch_one {a b z : ℝ}
    (ha : 0 < a) (hab : a < b) (hz : ScaleDomain a b z) :
    quarticTransform z (branchPower a b 1) = 2 * (b ^ 3 + 3 * a * b ^ 2 + a + 3 * b) := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := scale_points_outside ha hab hz
  rw [quarticTransform_congr (z := z) (f := branchPower a b 1)
    (g := fun t => (t + a) * (t + b) ^ 3)
    (branchPower_one_polynomial hab h₁) (branchPower_one_polynomial hab h₂)
    (branchPower_one_polynomial hab h₃) (branchPower_one_polynomial hab h₄)]
  have hf : (fun t : ℝ => (t + a) * (t + b) ^ 3) =
      fun t => a * b ^ 3 + (b ^ 3 + 3 * a * b ^ 2) * t +
        (3 * b ^ 2 + 3 * a * b) * t ^ 2 + (a + 3 * b) * t ^ 3 + 1 * t ^ 4 := by
    funext t
    ring
  rw [hf, quarticTransform_polynomial _ _ _ _ _ _ hz.1.ne']
  ring

theorem centeredRatio_scale_antitone {v₁ v₂ w R S : ℝ}
    (hv : v₁ < v₂) (hs : v₁ + v₂ < 0) (hw : w ∈ Ioc 0 (1 / 4))
    (hR₁ : -R < v₁) (hR₂ : v₂ < R) (hRS : R < S) :
    centeredRatio v₁ v₂ w S ≤ centeredRatio v₁ v₂ w R := by
  rcases hw.2.lt_or_eq with hwq | hwq
  · exact (centeredRatio_scale_strictAnti hv hs ⟨hw.1, hwq⟩ hR₁ hR₂ hRS).le
  subst w
  have hS₁ : -S < v₁ := by linarith
  have hS₂ : v₂ < S := hR₂.trans hRS
  rw [centeredRatio_eq_quarticTransform ⟨hS₁.le, (hv.trans hS₂).le⟩
      ⟨(hS₁.trans hv).le, hS₂.le⟩,
    centeredRatio_eq_quarticTransform ⟨hR₁.le, (hv.trans hR₂).le⟩
      ⟨(hR₁.trans hv).le, hR₂.le⟩,
    show (4 : ℝ) * (1 / 4) = 1 by norm_num,
    quarticTransform_branch_one (Real.exp_pos _) (Real.exp_lt_exp.mpr hv) (centered_scale_domain hS₁ hS₂),
    quarticTransform_branch_one (Real.exp_pos _) (Real.exp_lt_exp.mpr hv) (centered_scale_domain hR₁ hR₂)]

theorem centeredLimit_le_ratio_interior {v₁ v₂ w R : ℝ}
    (hv : v₁ < v₂) (hs : v₁ + v₂ < 0) (hw : w ∈ Ioc 0 (1 / 4))
    (hR₁ : -R < v₁) (hR₂ : v₂ < R) :
    centeredLimit v₁ v₂ w ≤ centeredRatio v₁ v₂ w R := by
  apply le_of_tendsto (tendsto_centeredRatio_atTop _ _ _)
  filter_upwards [eventually_gt_atTop R] with S hS
  exact centeredRatio_scale_antitone hv hs hw hR₁ hR₂ hS

theorem continuous_centeredRatio {v₁ v₂ w : ℝ} (hw : w ∈ Ioo 0 1) :
    Continuous (centeredRatio v₁ v₂ w) := by
  have h₁ : Continuous (fun R : ℝ => (R + v₁) / 2) :=
    (continuous_id.add continuous_const).div_const 2
  have h₂ : Continuous (fun R : ℝ => (R + v₂) / 2) :=
    (continuous_id.add continuous_const).div_const 2
  have hc : Continuous (fun R : ℝ => (R, ((R + v₁) / 2, (R + v₂) / 2))) :=
    continuous_id.prodMk (h₁.prodMk h₂)
  change Continuous (fun R : ℝ => twoPointRatio R ((R + v₁) / 2) ((R + v₂) / 2) w)
  simpa only [Function.comp_def] using (continuous_twoPointRatio hw).comp hc

theorem centeredLimit_le_ratio {v₁ v₂ w R : ℝ}
    (hv : v₁ < v₂) (hs : v₁ + v₂ < 0) (hw : w ∈ Ioc 0 (1 / 4))
    (hR₁ : -R ≤ v₁) (hR₂ : v₂ ≤ R) :
    centeredLimit v₁ v₂ w ≤ centeredRatio v₁ v₂ w R := by
  have hw1 : w ∈ Ioo 0 1 := ⟨hw.1, hw.2.trans_lt (by norm_num)⟩
  have hcont : Tendsto (centeredRatio v₁ v₂ w) (𝓝[>] R) (𝓝 (centeredRatio v₁ v₂ w R)) :=
    (continuous_centeredRatio hw1).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hcont
  filter_upwards [self_mem_nhdsWithin] with S hS
  have hSR : R < S := hS
  exact centeredLimit_le_ratio_interior hv hs hw (by linarith) (hR₂.trans_lt hSR)

/-- The full lower-weight unaligned range, including atoms at either endpoint. -/
theorem twoPointRatio_gt_one_unaligned_small_weight {R p q w : ℝ}
    (hp : p ∈ Icc 0 R) (hq : q ∈ Icc 0 R)
    (hpq : p < q) (hs : p + q < R) (hw : w ∈ Ioc 0 (1 / 4)) :
    1 < twoPointRatio R p q w := by
  let v₁ := 2 * p - R
  let v₂ := 2 * q - R
  have hv : v₁ < v₂ := by dsimp [v₁, v₂]; linarith
  have hs' : v₁ + v₂ < 0 := by dsimp [v₁, v₂]; linarith
  have hle := centeredLimit_le_ratio (R := R) hv hs' hw
    (by dsimp [v₁]; linarith [hp.1]) (by dsimp [v₂]; linarith [hq.2])
  have hstrict := centeredLimit_gt_one hv hs' ⟨hw.1, hw.2.trans_lt (by norm_num)⟩
  have he : centeredRatio v₁ v₂ w R = twoPointRatio R p q w := by
    unfold centeredRatio
    rw [show (R + v₁) / 2 = p by dsimp [v₁]; ring,
      show (R + v₂) / 2 = q by dsimp [v₂]; ring]
  rw [he] at hle
  exact hstrict.trans_le hle

end PaperVerification.Hyperbolic

#print axioms PaperVerification.Hyperbolic.tendsto_centeredRatio_atTop
#print axioms PaperVerification.Hyperbolic.twoPointRatio_gt_one_unaligned_small_weight
