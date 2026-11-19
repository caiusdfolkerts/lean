module
public import PaperVerification.HyperbolicScale
public import PaperVerification.HyperbolicTwoPoint
@[expose] public section
/-! # Exact exponential coordinates for the two-point ratio

The interval midpoint is fixed by the two values `v₁ = 2p-R` and
`v₂ = 2q-R`.  The proportionality factor below is positive and independent
of the scale `R`.
-/

noncomputable section

namespace PaperVerification.Hyperbolic

open Real Set

def centeredMean (v₁ v₂ w : ℝ) : ℝ := w * v₁ + (1 - w) * v₂

def centeredCoshMean (v₁ v₂ w : ℝ) : ℝ :=
  Real.cosh v₁ ^ w * Real.cosh v₂ ^ (1 - w)

def centeredFactor (v₁ v₂ w : ℝ) : ℝ :=
  Real.exp (-2 * centeredMean v₁ v₂ w) / (16 * centeredCoshMean v₁ v₂ w)

def centeredRatio (v₁ v₂ w R : ℝ) : ℝ :=
  twoPointRatio R ((R + v₁) / 2) ((R + v₂) / 2) w

theorem centeredCoshMean_pos (v₁ v₂ w : ℝ) : 0 < centeredCoshMean v₁ v₂ w :=
  mul_pos (Real.rpow_pos_of_pos (Real.cosh_pos _) _) (Real.rpow_pos_of_pos (Real.cosh_pos _) _)

theorem centeredFactor_pos (v₁ v₂ w : ℝ) : 0 < centeredFactor v₁ v₂ w :=
  div_pos (Real.exp_pos _) (mul_pos (by norm_num) (centeredCoshMean_pos _ _ _))

theorem cosh_centered_exp (R v : ℝ) :
    Real.cosh ((R + v) / 2) = Real.exp ((R - v) / 2) / 2 * (Real.exp v + Real.exp (-R)) := by
  have h₁ : Real.exp ((R - v) / 2) * Real.exp v = Real.exp ((R + v) / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have h₂ : Real.exp ((R - v) / 2) * Real.exp (-R) = Real.exp (-((R + v) / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [Real.cosh_eq, ← h₁, ← h₂]
  ring

theorem sinh_centered_exp (R v : ℝ) :
    Real.sinh ((R + v) / 2) = Real.exp ((R - v) / 2) / 2 * (Real.exp v - Real.exp (-R)) := by
  have h₁ : Real.exp ((R - v) / 2) * Real.exp v = Real.exp ((R + v) / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have h₂ : Real.exp ((R - v) / 2) * Real.exp (-R) = Real.exp (-((R + v) / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [Real.sinh_eq, ← h₁, ← h₂]
  ring

theorem cosh_reflected_centered_exp (R v : ℝ) :
    Real.cosh ((R - v) / 2) =
      Real.exp ((-R - v) / 2) / 2 * (Real.exp v + Real.exp R) := by
  rw [show (R - v) / 2 = -((-R + v) / 2) by ring, Real.cosh_neg,
    cosh_centered_exp, neg_neg]

theorem sinh_reflected_centered_exp (R v : ℝ) :
    Real.sinh ((R - v) / 2) =
      Real.exp ((-R - v) / 2) / 2 * (Real.exp R - Real.exp v) := by
  rw [show (R - v) / 2 = -((-R + v) / 2) by ring, Real.sinh_neg,
    sinh_centered_exp, neg_neg]
  ring

theorem weighted_exp_prefactor (x y r s : ℝ) (hrs : r + s = 4) :
    (Real.exp x / 2) ^ r * (Real.exp y / 2) ^ s = Real.exp (x * r + y * s) / 16 := by
  rw [Real.div_rpow (Real.exp_pos x).le (by norm_num),
    Real.div_rpow (Real.exp_pos y).le (by norm_num), ← Real.exp_mul, ← Real.exp_mul]
  rw [div_mul_div_comm, ← Real.exp_add, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), hrs,
    Real.rpow_ofNat]
  norm_num

theorem weighted_exp_product {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (x y r s : ℝ) (hrs : r + s = 4) :
    (Real.exp x / 2 * A) ^ r * (Real.exp y / 2 * B) ^ s =
      Real.exp (x * r + y * s) / 16 * (A ^ r * B ^ s) := by
  rw [Real.mul_rpow (div_pos (Real.exp_pos x) (by norm_num)).le hA,
    Real.mul_rpow (div_pos (Real.exp_pos y) (by norm_num)).le hB]
  calc
    _ = ((Real.exp x / 2) ^ r * (Real.exp y / 2) ^ s) * (A ^ r * B ^ s) := by ring
    _ = _ := by rw [weighted_exp_prefactor x y r s hrs]

theorem centered_numerator_exp {R v₁ v₂ : ℝ}
    (hv₁ : v₁ ∈ Icc (-R) R) (hv₂ : v₂ ∈ Icc (-R) R) (w : ℝ) :
    twoPointNumerator R ((R + v₁) / 2) ((R + v₂) / 2) w =
      Real.exp (2 * R - 2 * centeredMean v₁ v₂ w) / 16 *
        (branchPower (Real.exp v₁) (Real.exp v₂) (4 * w) (Real.exp (-R)) -
          branchPower (Real.exp v₁) (Real.exp v₂) (4 * w) (-Real.exp (-R))) +
      Real.exp (-2 * R - 2 * centeredMean v₁ v₂ w) / 16 *
        (branchPower (Real.exp v₁) (Real.exp v₂) (4 * w) (Real.exp R) -
          branchPower (Real.exp v₁) (Real.exp v₂) (4 * w) (-Real.exp R)) := by
  let a := Real.exp v₁
  let b := Real.exp v₂
  let z := Real.exp (-R)
  let Z := Real.exp R
  have ha : 0 < a := Real.exp_pos _
  have hb : 0 < b := Real.exp_pos _
  have hz : 0 < z := Real.exp_pos _
  have hZ : 0 < Z := Real.exp_pos _
  have hza : z ≤ a := Real.exp_le_exp.mpr hv₁.1
  have hzb : z ≤ b := Real.exp_le_exp.mpr hv₂.1
  have haZ : a ≤ Z := Real.exp_le_exp.mpr hv₁.2
  have hbZ : b ≤ Z := Real.exp_le_exp.mpr hv₂.2
  have hrs : 4 * w + 4 * (1 - w) = (4 : ℝ) := by ring
  have he₁ : (R - v₁) / 2 * (4 * w) + (R - v₂) / 2 * (4 * (1 - w)) =
      2 * R - 2 * centeredMean v₁ v₂ w := by unfold centeredMean; ring
  have he₂ : (-R - v₁) / 2 * (4 * w) + (-R - v₂) / 2 * (4 * (1 - w)) =
      -2 * R - 2 * centeredMean v₁ v₂ w := by unfold centeredMean; ring
  unfold twoPointNumerator
  rw [show R - (R + v₁) / 2 = (R - v₁) / 2 by ring,
    show R - (R + v₂) / 2 = (R - v₂) / 2 by ring,
    cosh_centered_exp, cosh_centered_exp, sinh_centered_exp, sinh_centered_exp,
    cosh_reflected_centered_exp, cosh_reflected_centered_exp,
    sinh_reflected_centered_exp, sinh_reflected_centered_exp]
  rw [weighted_exp_product (add_pos ha hz).le (add_pos hb hz).le _ _ _ _ hrs,
    weighted_exp_product (add_pos ha hZ).le (add_pos hb hZ).le _ _ _ _ hrs,
    weighted_exp_product (sub_nonneg.mpr hza) (sub_nonneg.mpr hzb) _ _ _ _ hrs,
    weighted_exp_product (sub_nonneg.mpr haZ) (sub_nonneg.mpr hbZ) _ _ _ _ hrs,
    he₁, he₂]
  unfold branchPower
  change _ = Real.exp (2 * R - 2 * centeredMean v₁ v₂ w) / 16 *
      (|z + a| ^ (4 * w) * |z + b| ^ (4 - 4 * w) -
        |-z + a| ^ (4 * w) * |-z + b| ^ (4 - 4 * w)) +
    Real.exp (-2 * R - 2 * centeredMean v₁ v₂ w) / 16 *
      (|Z + a| ^ (4 * w) * |Z + b| ^ (4 - 4 * w) -
        |-Z + a| ^ (4 * w) * |-Z + b| ^ (4 - 4 * w))
  rw [abs_of_pos (add_pos hz ha), abs_of_pos (add_pos hz hb),
    abs_of_nonneg (show 0 ≤ -z + a by linarith only [hza]),
    abs_of_nonneg (show 0 ≤ -z + b by linarith only [hzb]),
    abs_of_pos (add_pos hZ ha), abs_of_pos (add_pos hZ hb),
    abs_of_nonpos (show -Z + a ≤ 0 by linarith only [haZ]),
    abs_of_nonpos (show -Z + b ≤ 0 by linarith only [hbZ])]
  simp only [show 4 - 4 * w = 4 * (1 - w) by ring,
    show -z + a = a - z by ring, show -z + b = b - z by ring,
    show -(-Z + a) = Z - a by ring, show -(-Z + b) = Z - b by ring,
    show z + a = a + z by ring, show z + b = b + z by ring,
    show Z + a = a + Z by ring, show Z + b = b + Z by ring]
  ring

/-- Equation (20), with its complete positive proportionality factor. -/
theorem centeredRatio_eq_quarticTransform {R v₁ v₂ : ℝ}
    (hv₁ : v₁ ∈ Icc (-R) R) (hv₂ : v₂ ∈ Icc (-R) R) (w : ℝ) :
    centeredRatio v₁ v₂ w R = centeredFactor v₁ v₂ w *
      quarticTransform (Real.exp (-R)) (branchPower (Real.exp v₁) (Real.exp v₂) (4 * w)) := by
  let z := Real.exp (-R)
  let M := centeredMean v₁ v₂ w
  let H := centeredCoshMean v₁ v₂ w
  have hz : 0 < z := Real.exp_pos _
  have hH : 0 < H := centeredCoshMean_pos _ _ _
  have hz2 : z ^ 2 = Real.exp (-2 * R) := by
    dsimp [z]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hZ : Real.exp R = 1 / z := by dsimp [z]; rw [Real.exp_neg, one_div, inv_inv]
  have hplus : Real.exp (2 * R - 2 * M) = Real.exp (-2 * M) / z ^ 2 := by
    rw [hz2, ← Real.exp_sub]
    congr 1
    ring
  have hminus : Real.exp (-2 * R - 2 * M) = Real.exp (-2 * M) * z ^ 2 := by
    rw [hz2, ← Real.exp_add]
    congr 1
    ring
  have hden : twoPointDenominator R ((R + v₁) / 2) ((R + v₂) / 2) w = (z + 1 / z) * H := by
    unfold twoPointDenominator
    rw [show 2 * ((R + v₁) / 2) - R = v₁ by ring,
      show 2 * ((R + v₂) / 2) - R = v₂ by ring, Real.cosh_eq, hZ]
    dsimp [z, H, centeredCoshMean]
    ring
  have hq : z + z ^ 3 ≠ 0 := by
    rw [show z + z ^ 3 = z * (1 + z ^ 2) by ring]
    exact mul_ne_zero hz.ne' (by positivity)
  have hden' : z + 1 / z ≠ 0 := (add_pos hz (div_pos zero_lt_one hz)).ne'
  unfold centeredRatio twoPointRatio
  rw [centered_numerator_exp hv₁ hv₂, hden]
  change (Real.exp (2 * R - 2 * M) / 16 * _ + Real.exp (-2 * R - 2 * M) / 16 * _) /
    ((z + 1 / z) * H) = _
  rw [hplus, hminus, hZ]
  unfold centeredFactor quarticTransform
  change _ = Real.exp (-2 * M) / (16 * H) *
    ((_ - _ + z ^ 4 * (_ - _)) / (z + z ^ 3))
  simp only [neg_div]
  field_simp [hz.ne', hH.ne', hq, hden'] <;> ring

theorem centered_scale_domain {R v₁ v₂ : ℝ}
    (hv₁ : -R < v₁) (hv₂ : v₂ < R) :
    ScaleDomain (Real.exp v₁) (Real.exp v₂) (Real.exp (-R)) := by
  refine ⟨Real.exp_pos _, Real.exp_lt_exp.mpr hv₁, ?_⟩
  rw [← Real.exp_add, ← Real.exp_zero]
  apply Real.exp_lt_exp.mpr
  linarith

theorem centered_scale_parameters {v₁ v₂ : ℝ} (hv : v₁ < v₂) (hs : v₁ + v₂ < 0) :
    0 < Real.exp v₁ ∧ Real.exp v₁ < Real.exp v₂ ∧ Real.exp v₁ * Real.exp v₂ < 1 := by
  refine ⟨Real.exp_pos _, Real.exp_lt_exp.mpr hv, ?_⟩
  rw [← Real.exp_add, ← Real.exp_zero]
  exact Real.exp_lt_exp.mpr hs

theorem centeredRatio_scale_strictAnti {v₁ v₂ w R S : ℝ}
    (hv : v₁ < v₂) (hs : v₁ + v₂ < 0) (hw : w ∈ Ioo 0 (1 / 4))
    (hR₁ : -R < v₁) (hR₂ : v₂ < R) (hRS : R < S) :
    centeredRatio v₁ v₂ w S < centeredRatio v₁ v₂ w R := by
  obtain ⟨ha, hab, hab1⟩ := centered_scale_parameters hv hs
  have hS₁ : -S < v₁ := by linarith
  have hS₂ : v₂ < S := hR₂.trans hRS
  rw [centeredRatio_eq_quarticTransform ⟨hS₁.le, (hv.trans hS₂).le⟩
      ⟨(hS₁.trans hv).le, hS₂.le⟩,
    centeredRatio_eq_quarticTransform ⟨hR₁.le, (hv.trans hR₂).le⟩
      ⟨(hR₁.trans hv).le, hR₂.le⟩]
  apply mul_lt_mul_of_pos_left _ (centeredFactor_pos _ _ _)
  exact quarticTransform_lt_of_r_lt_one ha hab hab1
    (by constructor <;> linarith [hw.1, hw.2])
    (centered_scale_domain hS₁ hS₂) (centered_scale_domain hR₁ hR₂)
    (Real.exp_lt_exp.mpr (neg_lt_neg hRS))

theorem centeredRatio_scale_strictMono {v₁ v₂ w R S : ℝ}
    (hv : v₁ < v₂) (hs : v₁ + v₂ < 0) (hw : w ∈ Ioo (1 / 4) (1 / 2))
    (hR₁ : -R < v₁) (hR₂ : v₂ < R) (hRS : R < S) :
    centeredRatio v₁ v₂ w R < centeredRatio v₁ v₂ w S := by
  obtain ⟨ha, hab, hab1⟩ := centered_scale_parameters hv hs
  have hS₁ : -S < v₁ := by linarith
  have hS₂ : v₂ < S := hR₂.trans hRS
  rw [centeredRatio_eq_quarticTransform ⟨hR₁.le, (hv.trans hR₂).le⟩
      ⟨(hR₁.trans hv).le, hR₂.le⟩,
    centeredRatio_eq_quarticTransform ⟨hS₁.le, (hv.trans hS₂).le⟩
      ⟨(hS₁.trans hv).le, hS₂.le⟩]
  apply mul_lt_mul_of_pos_left _ (centeredFactor_pos _ _ _)
  exact quarticTransform_lt_of_one_lt_r ha hab hab1
    (by constructor <;> linarith [hw.1, hw.2])
    (centered_scale_domain hS₁ hS₂) (centered_scale_domain hR₁ hR₂)
    (Real.exp_lt_exp.mpr (neg_lt_neg hRS))

end PaperVerification.Hyperbolic

#print axioms PaperVerification.Hyperbolic.centeredRatio_eq_quarticTransform
#print axioms PaperVerification.Hyperbolic.centeredRatio_scale_strictMono
