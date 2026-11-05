module
public import PaperVerification.HyperbolicKernelIntegral
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation
public import Mathlib.MeasureTheory.Function.JacobianOneDim
@[expose] public section
/-! # A real Stieltjes representation for the quartic transform

The proof uses the kernel-checked integral representation of real fractional
powers.  It therefore supplies the required scale comparison without assuming
the complex Cauchy representation in equation (19).
-/

noncomputable section

namespace PaperVerification.Hyperbolic

open Real Set MeasureTheory intervalIntegral

def branchPower (a b r t : ℝ) : ℝ := |t + a| ^ r * |t + b| ^ (4 - r)

def OutsideCut (a b t : ℝ) : Prop := -a < t ∨ t < -b

def ScaleDomain (a b z : ℝ) : Prop := 0 < z ∧ z < a ∧ b * z < 1

def stieltjesNormalizer (r : ℝ) : ℝ := ∫ s in Ioi 0, Real.rpowIntegrand₀₁ r s 1

def stieltjesRaw01 (a b r s t : ℝ) : ℝ :=
  (t + b) ^ 4 * Real.rpowIntegrand₀₁ r s ((t + a) / (t + b))

def stieltjesRaw12 (a b r s t : ℝ) : ℝ :=
  (t + b) ^ 4 * Real.rpowIntegrand₁₂ r s ((t + a) / (t + b))

def stieltjesMap (a b s : ℝ) : ℝ := (a + b * s) / (1 + s)

def stieltjesWeight (a b r s : ℝ) : ℝ := (b - a) ^ 5 * s ^ r / (1 + s) ^ 6

theorem outsideCut_ratio_pos {a b t : ℝ} (hab : a < b) (ht : OutsideCut a b t) :
    0 < (t + a) / (t + b) := by
  rcases ht with ht | ht
  · exact div_pos (by linarith) (by linarith)
  · exact div_pos_of_neg_of_neg (by linarith) (by linarith)

theorem outsideCut_add_ne_zero {a b t u : ℝ} (ht : OutsideCut a b t) (hu : u ∈ Icc a b) :
    t + u ≠ 0 := by
  rcases ht with ht | ht <;> linarith [hu.1, hu.2]

theorem scale_points_outside {a b z : ℝ} (ha : 0 < a) (hab : a < b) (hz : ScaleDomain a b z) :
    OutsideCut a b z ∧ OutsideCut a b (-z) ∧
      OutsideCut a b (1 / z) ∧ OutsideCut a b (-1 / z) := by
  have hb : 0 < b := ha.trans hab
  have hzi : 0 < 1 / z := div_pos zero_lt_one hz.1
  refine ⟨Or.inl (by linarith [hz.1]), Or.inl (by linarith [hz.2.1]),
    Or.inl (by linarith), Or.inr ?_⟩
  have hzb : b < 1 / z := (lt_div_iff₀ hz.1).mpr (by simpa [mul_comm] using hz.2.2)
  simpa only [neg_div] using neg_lt_neg hzb

theorem branchPower_eq_ratio {a b r t : ℝ} (hab : a < b) (ht : OutsideCut a b t) :
    branchPower a b r t = (t + b) ^ 4 * ((t + a) / (t + b)) ^ r := by
  have htb : t + b ≠ 0 := outsideCut_add_ne_zero ht ⟨hab.le, le_rfl⟩
  have hq := outsideCut_ratio_pos hab ht
  have habs : |t + a| = ((t + a) / (t + b)) * |t + b| := by
    calc
      |t + a| = |((t + a) / (t + b)) * (t + b)| := by rw [div_mul_cancel₀ _ htb]
      _ = ((t + a) / (t + b)) * |t + b| := by rw [abs_mul, abs_of_pos hq]
  unfold branchPower
  rw [habs, Real.mul_rpow hq.le (abs_nonneg _), mul_assoc,
    ← Real.rpow_add (abs_pos.mpr htb), show r + (4 - r) = (4 : ℝ) by ring,
    Real.rpow_ofNat, (show Even (4 : ℕ) from ⟨2, rfl⟩).pow_abs]
  ring

theorem integrable_stieltjesRaw01 {a b r t : ℝ} (hab : a < b) (hr : r ∈ Ioo 0 1)
    (ht : OutsideCut a b t) : IntegrableOn (fun s => stieltjesRaw01 a b r s t) (Ioi 0) :=
  (Real.integrableOn_rpowIntegrand₀₁_Ioi hr (outsideCut_ratio_pos hab ht).le).const_mul _

theorem integrable_stieltjesRaw12 {a b r t : ℝ} (hab : a < b) (hr : r ∈ Ioo 1 2)
    (ht : OutsideCut a b t) : IntegrableOn (fun s => stieltjesRaw12 a b r s t) (Ioi 0) :=
  (Real.integrableOn_rpowIntegrand₁₂ hr (outsideCut_ratio_pos hab ht).le).const_mul _

theorem branchPower_stieltjes01 {a b r t : ℝ} (hab : a < b) (hr : r ∈ Ioo 0 1)
    (ht : OutsideCut a b t) :
    branchPower a b r t = (stieltjesNormalizer r)⁻¹ *
      ∫ s in Ioi 0, stieltjesRaw01 a b r s t := by
  rw [branchPower_eq_ratio hab ht,
    Real.rpow_eq_const_mul_integral hr (outsideCut_ratio_pos hab ht).le]
  unfold stieltjesRaw01 stieltjesNormalizer
  rw [MeasureTheory.integral_const_mul]
  ring

theorem branchPower_stieltjes12 {a b r t : ℝ} (hab : a < b) (hr : r ∈ Ioo 1 2)
    (ht : OutsideCut a b t) :
    branchPower a b r t = (stieltjesNormalizer (r - 1))⁻¹ *
      ∫ s in Ioi 0, stieltjesRaw12 a b r s t := by
  rw [branchPower_eq_ratio hab ht,
    Real.rpow_eq_const_mul_integral_rpowIntegrand₁₂ hr (outsideCut_ratio_pos hab ht).le]
  unfold stieltjesRaw12 stieltjesNormalizer
  rw [MeasureTheory.integral_const_mul]
  ring

theorem stieltjesNormalizer_pos {r : ℝ} (hr : r ∈ Ioo 0 1) :
    0 < stieltjesNormalizer r := Real.integral_rpowIntegrand₀₁_one_pos hr

theorem stieltjesMap_sub_left (a b s : ℝ) (hs : 1 + s ≠ 0) :
    stieltjesMap a b s - a = (b - a) * s / (1 + s) := by
  unfold stieltjesMap
  field_simp [hs] <;> ring

theorem right_sub_stieltjesMap (a b s : ℝ) (hs : 1 + s ≠ 0) :
    b - stieltjesMap a b s = (b - a) / (1 + s) := by
  unfold stieltjesMap
  field_simp [hs] <;> ring

theorem stieltjesMap_mem {a b s : ℝ} (hab : a < b) (hs : 0 < s) :
    stieltjesMap a b s ∈ Ioo a b := by
  have he : 0 < 1 + s := by linarith
  constructor
  · apply sub_pos.mp
    rw [stieltjesMap_sub_left a b s he.ne']
    exact div_pos (mul_pos (sub_pos.mpr hab) hs) he
  · apply sub_pos.mp
    rw [right_sub_stieltjesMap a b s he.ne']
    exact div_pos (sub_pos.mpr hab) he

theorem hasDerivAt_stieltjesMap (a b s : ℝ) (hs : 1 + s ≠ 0) :
    HasDerivAt (stieltjesMap a b) ((b - a) / (1 + s) ^ 2) s := by
  convert ((hasDerivAt_id s).const_mul b |>.const_add a).div
    ((hasDerivAt_id s).const_add 1) hs using 1 <;>
    (try funext t) <;> (try simp only [stieltjesMap, Pi.mul_apply, Pi.add_apply,
      Pi.div_apply, id_eq]) <;> ring

theorem stieltjesMap_injOn {a b : ℝ} (hab : a < b) :
    InjOn (stieltjesMap a b) (Ioi 0) := by
  intro s hs t ht h
  change 0 < s at hs
  change 0 < t at ht
  have hs1 : 1 + s ≠ 0 := by linarith
  have ht1 : 1 + t ≠ 0 := by linarith
  dsimp [stieltjesMap] at h
  have hcross := (div_eq_div_iff hs1 ht1).mp h
  apply (mul_left_cancel₀ (sub_ne_zero.mpr hab.ne'))
  nlinarith only [hcross]

theorem stieltjesMap_image {a b : ℝ} (hab : a < b) :
    stieltjesMap a b '' Ioi 0 = Ioo a b := by
  ext u
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact stieltjesMap_mem hab hs
  · intro hu
    have hδ : b - u ≠ 0 := (sub_pos.mpr hu.2).ne'
    refine ⟨(u - a) / (b - u), div_pos (sub_pos.mpr hu.1) (sub_pos.mpr hu.2), ?_⟩
    have he : 1 + (u - a) / (b - u) ≠ 0 := by
      have : 0 < (u - a) / (b - u) := div_pos (sub_pos.mpr hu.1) (sub_pos.mpr hu.2)
      linarith
    unfold stieltjesMap
    apply (div_eq_iff he).mpr
    field_simp [hδ] <;> ring

theorem stieltjesWeight_eq_density_jacobian {a b r s : ℝ} (hab : a < b) (hs : 0 < s) :
    stieltjesWeight a b r s =
      (b - a) / (1 + s) ^ 2 * branchDensity a b r (stieltjesMap a b s) := by
  have hδ : 0 < b - a := sub_pos.mpr hab
  have he : 0 < 1 + s := by linarith
  have hpδ : (b - a) ^ r * (b - a) ^ (4 - r) = (b - a) ^ (4 : ℕ) := by
    rw [← Real.rpow_add hδ, show r + (4 - r) = (4 : ℝ) by ring, Real.rpow_ofNat]
  have hpe : (1 + s) ^ r * (1 + s) ^ (4 - r) = (1 + s) ^ (4 : ℕ) := by
    rw [← Real.rpow_add he, show r + (4 - r) = (4 : ℝ) by ring, Real.rpow_ofNat]
  have hρ : branchDensity a b r (stieltjesMap a b s) =
      (b - a) ^ (4 : ℕ) / (1 + s) ^ (4 : ℕ) * s ^ r := by
    unfold branchDensity
    rw [stieltjesMap_sub_left a b s he.ne', right_sub_stieltjesMap a b s he.ne',
      Real.div_rpow (mul_nonneg hδ.le hs.le) he.le, Real.mul_rpow hδ.le hs.le,
      Real.div_rpow hδ.le he.le]
    calc
      _ = ((b - a) ^ r * (b - a) ^ (4 - r)) /
          ((1 + s) ^ r * (1 + s) ^ (4 - r)) * s ^ r := by ring
      _ = _ := by rw [hpδ, hpe]
  rw [hρ]
  unfold stieltjesWeight
  field_simp [he.ne'] <;> ring

/-- Compact-interval change of variables for the exact Stieltjes density. -/
theorem integral_stieltjesWeight {a b r : ℝ} (hab : a < b) (f : ℝ → ℝ) :
    (∫ s in Ioi 0, stieltjesWeight a b r s * f (stieltjesMap a b s)) =
      ∫ u in a..b, branchDensity a b r u * f u := by
  have hchange := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun s (hs : s ∈ Ioi (0 : ℝ)) =>
      (hasDerivAt_stieltjesMap a b s (by linarith only [show 0 < s from hs])).hasDerivWithinAt)
    (stieltjesMap_injOn hab) (fun u => branchDensity a b r u * f u)
  rw [stieltjesMap_image hab] at hchange
  rw [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo, hchange]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have he : 0 < 1 + s := by linarith only [show 0 < s from hs]
  rw [smul_eq_mul, abs_of_pos (div_pos (sub_pos.mpr hab) (sq_pos_of_ne_zero he.ne')),
    stieltjesWeight_eq_density_jacobian hab hs]
  ring

theorem quarticTransform_add (z : ℝ) (f g : ℝ → ℝ) :
    quarticTransform z (fun t => f t + g t) = quarticTransform z f + quarticTransform z g := by
  unfold quarticTransform
  ring

theorem quarticTransform_const_mul (z c : ℝ) (f : ℝ → ℝ) :
    quarticTransform z (fun t => c * f t) = c * quarticTransform z f := by
  unfold quarticTransform
  ring

theorem quarticTransform_congr {z : ℝ} {f g : ℝ → ℝ}
    (h₁ : f z = g z) (h₂ : f (-z) = g (-z))
    (h₃ : f (1 / z) = g (1 / z)) (h₄ : f (-1 / z) = g (-1 / z)) :
    quarticTransform z f = quarticTransform z g := by
  simp only [quarticTransform, h₁, h₂, h₃, h₄]

theorem integrable_quarticTransform {μ : Measure ℝ} {z : ℝ} {f : ℝ → ℝ → ℝ}
    (h₁ : Integrable (fun s => f s z) μ) (h₂ : Integrable (fun s => f s (-z)) μ)
    (h₃ : Integrable (fun s => f s (1 / z)) μ) (h₄ : Integrable (fun s => f s (-1 / z)) μ) :
    Integrable (fun s => quarticTransform z (f s)) μ :=
  ((h₁.sub h₂).add ((h₃.sub h₄).const_mul (z ^ 4))).div_const _

theorem quarticTransform_integral {μ : Measure ℝ} {z : ℝ} {f : ℝ → ℝ → ℝ}
    (h₁ : Integrable (fun s => f s z) μ) (h₂ : Integrable (fun s => f s (-z)) μ)
    (h₃ : Integrable (fun s => f s (1 / z)) μ) (h₄ : Integrable (fun s => f s (-1 / z)) μ) :
    quarticTransform z (fun t => ∫ s, f s t ∂μ) = ∫ s, quarticTransform z (f s) ∂μ := by
  have hleft : Integrable (fun s => f s z - f s (-z)) μ := h₁.sub h₂
  have hright : Integrable (fun s => f s (1 / z) - f s (-1 / z)) μ := h₃.sub h₄
  unfold quarticTransform
  rw [MeasureTheory.integral_div, MeasureTheory.integral_add hleft
    (hright.const_mul (z ^ 4)), MeasureTheory.integral_const_mul,
    MeasureTheory.integral_sub h₁ h₂, MeasureTheory.integral_sub h₃ h₄]

/-- The quartic-polynomial cancellation remains valid after translation. -/
theorem quarticTransform_shift_polynomial (z u p₀ p₁ p₂ p₃ p₄ : ℝ) (hz : z ≠ 0) :
    quarticTransform z (fun t => p₀ + p₁ * (t + u) + p₂ * (t + u) ^ 2 +
      p₃ * (t + u) ^ 3 + p₄ * (t + u) ^ 4) =
      2 * (p₁ + 2 * p₂ * u + 3 * p₃ * u ^ 2 + 4 * p₄ * u ^ 3 + p₃ + 4 * p₄ * u) := by
  have hp : (fun t : ℝ => p₀ + p₁ * (t + u) + p₂ * (t + u) ^ 2 +
      p₃ * (t + u) ^ 3 + p₄ * (t + u) ^ 4) =
      fun t => (p₀ + p₁ * u + p₂ * u ^ 2 + p₃ * u ^ 3 + p₄ * u ^ 4) +
        (p₁ + 2 * p₂ * u + 3 * p₃ * u ^ 2 + 4 * p₄ * u ^ 3) * t +
        (p₂ + 3 * p₃ * u + 6 * p₄ * u ^ 2) * t ^ 2 +
        (p₃ + 4 * p₄ * u) * t ^ 3 + p₄ * t ^ 4 := by
    funext t
    ring
  rw [hp, quarticTransform_polynomial _ _ _ _ _ _ hz]
  ring

def divisionPolynomial01 (a b u t : ℝ) : ℝ :=
  ((b - u) ^ 4 + 4 * (b - u) ^ 3 * (a - u)) +
  (4 * (b - u) ^ 3 + 6 * (b - u) ^ 2 * (a - u)) * (t + u) +
  (6 * (b - u) ^ 2 + 4 * (b - u) * (a - u)) * (t + u) ^ 2 +
  (4 * (b - u) + (a - u)) * (t + u) ^ 3 + (t + u) ^ 4

def divisionPolynomial12 (a b u t : ℝ) : ℝ :=
  (2 * (b - u) ^ 3 * (a - u) + 3 * (b - u) ^ 2 * (a - u) ^ 2) +
  ((b - u) ^ 3 + 6 * (b - u) ^ 2 * (a - u) + 3 * (b - u) * (a - u) ^ 2) * (t + u) +
  (3 * (b - u) ^ 2 + 6 * (b - u) * (a - u) + (a - u) ^ 2) * (t + u) ^ 2 +
  (3 * (b - u) + 2 * (a - u)) * (t + u) ^ 3 + (t + u) ^ 4

theorem division01 (a b u t : ℝ) (ht : t + u ≠ 0) :
    (t + b) ^ 4 * (t + a) / (t + u) =
      divisionPolynomial01 a b u t + (b - u) ^ 4 * (a - u) * (1 / (t + u)) := by
  unfold divisionPolynomial01
  field_simp [ht] <;> ring

theorem division12 (a b u t : ℝ) (ht : t + u ≠ 0) :
    (t + b) ^ 3 * (t + a) ^ 2 / (t + u) =
      divisionPolynomial12 a b u t + (b - u) ^ 3 * (a - u) ^ 2 * (1 / (t + u)) := by
  unfold divisionPolynomial12
  field_simp [ht] <;> ring

theorem divisionPolynomial01_transform_eq (a b u z y : ℝ) (hz : z ≠ 0) (hy : y ≠ 0) :
    quarticTransform z (divisionPolynomial01 a b u) =
      quarticTransform y (divisionPolynomial01 a b u) := by
  let p₀ := (b - u) ^ 4 + 4 * (b - u) ^ 3 * (a - u)
  let p₁ := 4 * (b - u) ^ 3 + 6 * (b - u) ^ 2 * (a - u)
  let p₂ := 6 * (b - u) ^ 2 + 4 * (b - u) * (a - u)
  let p₃ := 4 * (b - u) + (a - u)
  have hz' := quarticTransform_shift_polynomial z u p₀ p₁ p₂ p₃ 1 hz
  have hy' := quarticTransform_shift_polynomial y u p₀ p₁ p₂ p₃ 1 hy
  have hp : divisionPolynomial01 a b u =
      (fun t : ℝ => p₀ + p₁ * (t + u) + p₂ * (t + u) ^ 2 +
        p₃ * (t + u) ^ 3 + 1 * (t + u) ^ 4) := by
    funext t
    dsimp [divisionPolynomial01, p₀, p₁, p₂, p₃]
    ring
  rw [hp]
  exact hz'.trans hy'.symm

theorem divisionPolynomial12_transform_eq (a b u z y : ℝ) (hz : z ≠ 0) (hy : y ≠ 0) :
    quarticTransform z (divisionPolynomial12 a b u) =
      quarticTransform y (divisionPolynomial12 a b u) := by
  let p₀ := 2 * (b - u) ^ 3 * (a - u) + 3 * (b - u) ^ 2 * (a - u) ^ 2
  let p₁ := (b - u) ^ 3 + 6 * (b - u) ^ 2 * (a - u) + 3 * (b - u) * (a - u) ^ 2
  let p₂ := 3 * (b - u) ^ 2 + 6 * (b - u) * (a - u) + (a - u) ^ 2
  let p₃ := 3 * (b - u) + 2 * (a - u)
  have hz' := quarticTransform_shift_polynomial z u p₀ p₁ p₂ p₃ 1 hz
  have hy' := quarticTransform_shift_polynomial y u p₀ p₁ p₂ p₃ 1 hy
  have hp : divisionPolynomial12 a b u =
      (fun t : ℝ => p₀ + p₁ * (t + u) + p₂ * (t + u) ^ 2 +
        p₃ * (t + u) ^ 3 + 1 * (t + u) ^ 4) := by
    funext t
    dsimp [divisionPolynomial12, p₀, p₁, p₂, p₃]
    ring
  rw [hp]
  exact hz'.trans hy'.symm

theorem scale_resolvent_denominators {a b z u : ℝ} (ha : 0 < a) (hz : ScaleDomain a b z)
    (hu : u ∈ Icc a b) : u ≠ 0 ∧ u ^ 2 - z ^ 2 ≠ 0 ∧ 1 - u ^ 2 * z ^ 2 ≠ 0 := by
  have hu0 : 0 < u := ha.trans_le hu.1
  have hzu : z < u := hz.2.1.trans_le hu.1
  have huz : u * z < 1 := (mul_le_mul_of_nonneg_right hu.2 hz.1.le).trans_lt hz.2.2
  have hmul : 0 < u * z := mul_pos hu0 hz.1
  refine ⟨hu0.ne', ?_, ?_⟩
  · apply ne_of_gt
    nlinarith only [hu0, hz.1, hzu]
  · apply ne_of_gt
    nlinarith only [hmul, huz, sq_nonneg (u * z - 1)]

theorem transform_division01 {a b u z : ℝ} (ha : 0 < a) (hab : a < b)
    (hu : u ∈ Icc a b) (hz : ScaleDomain a b z) :
    quarticTransform z (fun t => (t + b) ^ 4 * (t + a) / (t + u)) =
      quarticTransform z (divisionPolynomial01 a b u) +
        (b - u) ^ 4 * (a - u) * resolventKernel u (z ^ 2) := by
  obtain ⟨hz₁, hz₂, hz₃, hz₄⟩ := scale_points_outside ha hab hz
  obtain ⟨hu₀, hu₁, hu₂⟩ := scale_resolvent_denominators ha hz hu
  rw [quarticTransform_congr (z := z)
    (f := fun t => (t + b) ^ 4 * (t + a) / (t + u))
    (g := fun t => divisionPolynomial01 a b u t + (b - u) ^ 4 * (a - u) * (1 / (t + u)))
    (division01 a b u z (outsideCut_add_ne_zero hz₁ hu))
    (division01 a b u (-z) (outsideCut_add_ne_zero hz₂ hu))
    (division01 a b u (1 / z) (outsideCut_add_ne_zero hz₃ hu))
    (division01 a b u (-1 / z) (outsideCut_add_ne_zero hz₄ hu)),
    quarticTransform_add, quarticTransform_const_mul,
    quarticTransform_resolvent u z hu₀ hz.1.ne' hu₁ hu₂]

theorem transform_division12 {a b u z : ℝ} (ha : 0 < a) (hab : a < b)
    (hu : u ∈ Icc a b) (hz : ScaleDomain a b z) :
    quarticTransform z (fun t => (t + b) ^ 3 * (t + a) ^ 2 / (t + u)) =
      quarticTransform z (divisionPolynomial12 a b u) +
        (b - u) ^ 3 * (a - u) ^ 2 * resolventKernel u (z ^ 2) := by
  obtain ⟨hz₁, hz₂, hz₃, hz₄⟩ := scale_points_outside ha hab hz
  obtain ⟨hu₀, hu₁, hu₂⟩ := scale_resolvent_denominators ha hz hu
  rw [quarticTransform_congr (z := z)
    (f := fun t => (t + b) ^ 3 * (t + a) ^ 2 / (t + u))
    (g := fun t => divisionPolynomial12 a b u t + (b - u) ^ 3 * (a - u) ^ 2 * (1 / (t + u)))
    (division12 a b u z (outsideCut_add_ne_zero hz₁ hu))
    (division12 a b u (-z) (outsideCut_add_ne_zero hz₂ hu))
    (division12 a b u (1 / z) (outsideCut_add_ne_zero hz₃ hu))
    (division12 a b u (-1 / z) (outsideCut_add_ne_zero hz₄ hu)),
    quarticTransform_add, quarticTransform_const_mul,
    quarticTransform_resolvent u z hu₀ hz.1.ne' hu₁ hu₂]

theorem stieltjesRaw01_rational {a b r s t : ℝ} (hab : a < b)
    (hr : r ∈ Ioo 0 1) (hs : 0 < s) (ht : OutsideCut a b t) :
    stieltjesRaw01 a b r s t = s ^ (r - 1) / (1 + s) *
      ((t + b) ^ 4 * (t + a) / (t + stieltjesMap a b s)) := by
  have hq := outsideCut_ratio_pos hab ht
  have htb := outsideCut_add_ne_zero ht (show b ∈ Icc a b from ⟨hab.le, le_rfl⟩)
  have he : 1 + s ≠ 0 := by linarith
  have hsq : s + (t + a) / (t + b) ≠ 0 := (add_pos hs hq).ne'
  have hden := outsideCut_add_ne_zero ht
    (show stieltjesMap a b s ∈ Icc a b from ⟨(stieltjesMap_mem hab hs).1.le,
      (stieltjesMap_mem hab hs).2.le⟩)
  unfold stieltjesRaw01
  rw [Real.rpowIntegrand₀₁_eq_pow_div hr hs.le hq.le]
  unfold stieltjesMap at hden ⊢
  field_simp [htb, he, hsq, hden] <;> ring

theorem stieltjesRaw12_rational {a b r s t : ℝ} (hab : a < b)
    (hr : r ∈ Ioo 1 2) (hs : 0 < s) (ht : OutsideCut a b t) :
    stieltjesRaw12 a b r s t = s ^ (r - 2) / (1 + s) *
      ((t + b) ^ 3 * (t + a) ^ 2 / (t + stieltjesMap a b s)) := by
  have hq := outsideCut_ratio_pos hab ht
  have htb := outsideCut_add_ne_zero ht (show b ∈ Icc a b from ⟨hab.le, le_rfl⟩)
  have he : 1 + s ≠ 0 := by linarith
  have hsq : s + (t + a) / (t + b) ≠ 0 := (add_pos hs hq).ne'
  have hden := outsideCut_add_ne_zero ht
    (show stieltjesMap a b s ∈ Icc a b from ⟨(stieltjesMap_mem hab hs).1.le,
      (stieltjesMap_mem hab hs).2.le⟩)
  unfold stieltjesRaw12
  rw [Real.rpowIntegrand₁₂_eq_mul_rpowIntegrand₀₁ hq.le hs,
    Real.rpowIntegrand₀₁_eq_pow_div (by constructor <;> linarith [hr.1, hr.2]) hs.le hq.le,
    show r - 1 - 1 = r - 2 by ring]
  unfold stieltjesMap at hden ⊢
  field_simp [htb, he, hsq, hden] <;> ring

theorem stieltjesRemainder01 {a b r s : ℝ} (hs : 0 < s) :
    s ^ (r - 1) / (1 + s) * (b - stieltjesMap a b s) ^ 4 *
      (a - stieltjesMap a b s) = -stieltjesWeight a b r s := by
  have he : 1 + s ≠ 0 := by linarith
  rw [show a - stieltjesMap a b s = -(stieltjesMap a b s - a) by ring,
    stieltjesMap_sub_left a b s he, right_sub_stieltjesMap a b s he,
    Real.rpow_sub_one hs.ne' r]
  unfold stieltjesWeight
  field_simp [hs.ne', he] <;> ring

theorem stieltjesRemainder12 {a b r s : ℝ} (hs : 0 < s) :
    s ^ (r - 2) / (1 + s) * (b - stieltjesMap a b s) ^ 3 *
      (a - stieltjesMap a b s) ^ 2 = stieltjesWeight a b r s := by
  have he : 1 + s ≠ 0 := by linarith
  rw [show a - stieltjesMap a b s = -(stieltjesMap a b s - a) by ring,
    stieltjesMap_sub_left a b s he, right_sub_stieltjesMap a b s he,
    show r - 2 = r - 1 - 1 by ring,
    Real.rpow_sub_one hs.ne' (r - 1), Real.rpow_sub_one hs.ne' r]
  unfold stieltjesWeight
  field_simp [hs.ne', he] <;> ring

theorem transform_stieltjesRaw01 {a b r s z : ℝ} (ha : 0 < a) (hab : a < b)
    (hr : r ∈ Ioo 0 1) (hs : 0 < s) (hz : ScaleDomain a b z) :
    quarticTransform z (stieltjesRaw01 a b r s) = s ^ (r - 1) / (1 + s) *
      (quarticTransform z (divisionPolynomial01 a b (stieltjesMap a b s)) +
        (b - stieltjesMap a b s) ^ 4 * (a - stieltjesMap a b s) *
          resolventKernel (stieltjesMap a b s) (z ^ 2)) := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := scale_points_outside ha hab hz
  have hu := stieltjesMap_mem hab hs
  rw [quarticTransform_congr (z := z) (f := stieltjesRaw01 a b r s)
    (g := fun t => s ^ (r - 1) / (1 + s) *
      ((t + b) ^ 4 * (t + a) / (t + stieltjesMap a b s)))
    (stieltjesRaw01_rational hab hr hs h₁)
    (stieltjesRaw01_rational hab hr hs h₂)
    (stieltjesRaw01_rational hab hr hs h₃)
    (stieltjesRaw01_rational hab hr hs h₄), quarticTransform_const_mul,
    transform_division01 ha hab ⟨hu.1.le, hu.2.le⟩ hz]

theorem transform_stieltjesRaw12 {a b r s z : ℝ} (ha : 0 < a) (hab : a < b)
    (hr : r ∈ Ioo 1 2) (hs : 0 < s) (hz : ScaleDomain a b z) :
    quarticTransform z (stieltjesRaw12 a b r s) = s ^ (r - 2) / (1 + s) *
      (quarticTransform z (divisionPolynomial12 a b (stieltjesMap a b s)) +
        (b - stieltjesMap a b s) ^ 3 * (a - stieltjesMap a b s) ^ 2 *
          resolventKernel (stieltjesMap a b s) (z ^ 2)) := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := scale_points_outside ha hab hz
  have hu := stieltjesMap_mem hab hs
  rw [quarticTransform_congr (z := z) (f := stieltjesRaw12 a b r s)
    (g := fun t => s ^ (r - 2) / (1 + s) *
      ((t + b) ^ 3 * (t + a) ^ 2 / (t + stieltjesMap a b s)))
    (stieltjesRaw12_rational hab hr hs h₁)
    (stieltjesRaw12_rational hab hr hs h₂)
    (stieltjesRaw12_rational hab hr hs h₃)
    (stieltjesRaw12_rational hab hr hs h₄), quarticTransform_const_mul,
    transform_division12 ha hab ⟨hu.1.le, hu.2.le⟩ hz]

theorem transform_stieltjesRaw01_difference {a b r s z y : ℝ} (ha : 0 < a) (hab : a < b)
    (hr : r ∈ Ioo 0 1) (hs : 0 < s) (hz : ScaleDomain a b z) (hy : ScaleDomain a b y) :
    quarticTransform z (stieltjesRaw01 a b r s) - quarticTransform y (stieltjesRaw01 a b r s) =
      -stieltjesWeight a b r s *
        (resolventKernel (stieltjesMap a b s) (z ^ 2) -
          resolventKernel (stieltjesMap a b s) (y ^ 2)) := by
  rw [transform_stieltjesRaw01 ha hab hr hs hz, transform_stieltjesRaw01 ha hab hr hs hy,
    divisionPolynomial01_transform_eq a b (stieltjesMap a b s) z y hz.1.ne' hy.1.ne']
  calc
    _ = (s ^ (r - 1) / (1 + s) * (b - stieltjesMap a b s) ^ 4 *
      (a - stieltjesMap a b s)) *
      (resolventKernel (stieltjesMap a b s) (z ^ 2) -
        resolventKernel (stieltjesMap a b s) (y ^ 2)) := by ring
    _ = _ := by rw [stieltjesRemainder01 hs]

theorem transform_stieltjesRaw12_difference {a b r s z y : ℝ} (ha : 0 < a) (hab : a < b)
    (hr : r ∈ Ioo 1 2) (hs : 0 < s) (hz : ScaleDomain a b z) (hy : ScaleDomain a b y) :
    quarticTransform z (stieltjesRaw12 a b r s) - quarticTransform y (stieltjesRaw12 a b r s) =
      stieltjesWeight a b r s *
        (resolventKernel (stieltjesMap a b s) (z ^ 2) -
          resolventKernel (stieltjesMap a b s) (y ^ 2)) := by
  rw [transform_stieltjesRaw12 ha hab hr hs hz, transform_stieltjesRaw12 ha hab hr hs hy,
    divisionPolynomial12_transform_eq a b (stieltjesMap a b s) z y hz.1.ne' hy.1.ne']
  calc
    _ = (s ^ (r - 2) / (1 + s) * (b - stieltjesMap a b s) ^ 3 *
      (a - stieltjesMap a b s) ^ 2) *
      (resolventKernel (stieltjesMap a b s) (z ^ 2) -
        resolventKernel (stieltjesMap a b s) (y ^ 2)) := by ring
    _ = _ := by rw [stieltjesRemainder12 hs]

theorem integrable_transform_stieltjes01 {a b r z : ℝ} (ha : 0 < a) (hab : a < b)
    (hr : r ∈ Ioo 0 1) (hz : ScaleDomain a b z) :
    IntegrableOn (fun s => quarticTransform z (stieltjesRaw01 a b r s)) (Ioi 0) := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := scale_points_outside ha hab hz
  exact integrable_quarticTransform (integrable_stieltjesRaw01 hab hr h₁)
    (integrable_stieltjesRaw01 hab hr h₂) (integrable_stieltjesRaw01 hab hr h₃)
    (integrable_stieltjesRaw01 hab hr h₄)

theorem integrable_transform_stieltjes12 {a b r z : ℝ} (ha : 0 < a) (hab : a < b)
    (hr : r ∈ Ioo 1 2) (hz : ScaleDomain a b z) :
    IntegrableOn (fun s => quarticTransform z (stieltjesRaw12 a b r s)) (Ioi 0) := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := scale_points_outside ha hab hz
  exact integrable_quarticTransform (integrable_stieltjesRaw12 hab hr h₁)
    (integrable_stieltjesRaw12 hab hr h₂) (integrable_stieltjesRaw12 hab hr h₃)
    (integrable_stieltjesRaw12 hab hr h₄)

theorem quarticTransform_stieltjes01 {a b r z : ℝ} (ha : 0 < a) (hab : a < b)
    (hr : r ∈ Ioo 0 1) (hz : ScaleDomain a b z) :
    quarticTransform z (branchPower a b r) = (stieltjesNormalizer r)⁻¹ *
      ∫ s in Ioi 0, quarticTransform z (stieltjesRaw01 a b r s) := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := scale_points_outside ha hab hz
  rw [quarticTransform_congr (z := z) (f := branchPower a b r)
    (g := fun t => (stieltjesNormalizer r)⁻¹ * ∫ s in Ioi 0, stieltjesRaw01 a b r s t)
    (branchPower_stieltjes01 hab hr h₁)
    (branchPower_stieltjes01 hab hr h₂) (branchPower_stieltjes01 hab hr h₃)
    (branchPower_stieltjes01 hab hr h₄), quarticTransform_const_mul,
    quarticTransform_integral (integrable_stieltjesRaw01 hab hr h₁)
      (integrable_stieltjesRaw01 hab hr h₂) (integrable_stieltjesRaw01 hab hr h₃)
      (integrable_stieltjesRaw01 hab hr h₄)]

theorem quarticTransform_stieltjes12 {a b r z : ℝ} (ha : 0 < a) (hab : a < b)
    (hr : r ∈ Ioo 1 2) (hz : ScaleDomain a b z) :
    quarticTransform z (branchPower a b r) = (stieltjesNormalizer (r - 1))⁻¹ *
      ∫ s in Ioi 0, quarticTransform z (stieltjesRaw12 a b r s) := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := scale_points_outside ha hab hz
  rw [quarticTransform_congr (z := z) (f := branchPower a b r)
    (g := fun t => (stieltjesNormalizer (r - 1))⁻¹ * ∫ s in Ioi 0, stieltjesRaw12 a b r s t)
    (branchPower_stieltjes12 hab hr h₁)
    (branchPower_stieltjes12 hab hr h₂) (branchPower_stieltjes12 hab hr h₃)
    (branchPower_stieltjes12 hab hr h₄), quarticTransform_const_mul,
    quarticTransform_integral (integrable_stieltjesRaw12 hab hr h₁)
      (integrable_stieltjesRaw12 hab hr h₂) (integrable_stieltjesRaw12 hab hr h₃)
      (integrable_stieltjesRaw12 hab hr h₄)]

/-- Real-integral form of equations (19)--(20) for `0<r<1`.
The entire quartic part has cancelled before the integral is taken. -/
theorem quarticTransform_difference_stieltjes01 {a b r z y : ℝ}
    (ha : 0 < a) (hab : a < b) (hr : r ∈ Ioo 0 1)
    (hz : ScaleDomain a b z) (hy : ScaleDomain a b y) :
    quarticTransform z (branchPower a b r) - quarticTransform y (branchPower a b r) =
      -(stieltjesNormalizer r)⁻¹ *
        ∫ u in a..b, branchDensity a b r u * (resolventKernel u (z ^ 2) - resolventKernel u (y ^ 2)) := by
  rw [quarticTransform_stieltjes01 ha hab hr hz, quarticTransform_stieltjes01 ha hab hr hy,
    ← mul_sub, ← MeasureTheory.integral_sub (integrable_transform_stieltjes01 ha hab hr hz)
      (integrable_transform_stieltjes01 ha hab hr hy)]
  have heq : (∫ s in Ioi 0, quarticTransform z (stieltjesRaw01 a b r s) -
      quarticTransform y (stieltjesRaw01 a b r s)) =
      -(∫ s in Ioi 0, stieltjesWeight a b r s *
        (resolventKernel (stieltjesMap a b s) (z ^ 2) -
          resolventKernel (stieltjesMap a b s) (y ^ 2))) := by
    rw [← MeasureTheory.integral_neg]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [transform_stieltjesRaw01_difference ha hab hr hs hz hy]
    ring
  rw [heq, integral_stieltjesWeight (r := r) hab
    (fun u => resolventKernel u (z ^ 2) - resolventKernel u (y ^ 2))]
  ring

/-- Real-integral form of equations (19)--(20) for `1<r<2`. -/
theorem quarticTransform_difference_stieltjes12 {a b r z y : ℝ}
    (ha : 0 < a) (hab : a < b) (hr : r ∈ Ioo 1 2)
    (hz : ScaleDomain a b z) (hy : ScaleDomain a b y) :
    quarticTransform z (branchPower a b r) - quarticTransform y (branchPower a b r) =
      (stieltjesNormalizer (r - 1))⁻¹ *
        ∫ u in a..b, branchDensity a b r u * (resolventKernel u (z ^ 2) - resolventKernel u (y ^ 2)) := by
  rw [quarticTransform_stieltjes12 ha hab hr hz, quarticTransform_stieltjes12 ha hab hr hy,
    ← mul_sub, ← MeasureTheory.integral_sub (integrable_transform_stieltjes12 ha hab hr hz)
      (integrable_transform_stieltjes12 ha hab hr hy)]
  have heq : (∫ s in Ioi 0, quarticTransform z (stieltjesRaw12 a b r s) -
      quarticTransform y (stieltjesRaw12 a b r s)) =
      ∫ s in Ioi 0, stieltjesWeight a b r s *
        (resolventKernel (stieltjesMap a b s) (z ^ 2) -
          resolventKernel (stieltjesMap a b s) (y ^ 2)) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact transform_stieltjesRaw12_difference ha hab hr hs hz hy
  rw [heq, integral_stieltjesWeight (r := r) hab
    (fun u => resolventKernel u (z ^ 2) - resolventKernel u (y ^ 2))]

end PaperVerification.Hyperbolic

#print axioms PaperVerification.Hyperbolic.integral_stieltjesWeight
#print axioms PaperVerification.Hyperbolic.transform_division01
#print axioms PaperVerification.Hyperbolic.quarticTransform_difference_stieltjes01
#print axioms PaperVerification.Hyperbolic.quarticTransform_difference_stieltjes12
