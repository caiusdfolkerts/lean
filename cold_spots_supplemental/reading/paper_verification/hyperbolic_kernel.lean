module
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
@[expose] public section
/-! # Exact resolvent algebra and reciprocal comparison

These are equations (20)--(22) and the pointwise sign comparison in Section 5.2.
The formulas are proved for arbitrary real parameters in their stated domains.
-/

noncomputable section

namespace PaperVerification.Hyperbolic

open Real Set MeasureTheory intervalIntegral

/-- The quartic transform appearing after the exponential coordinate change. -/
def quarticTransform (z : ℝ) (f : ℝ → ℝ) : ℝ :=
  (f z - f (-z) + z ^ 4 * (f (1 / z) - f (-1 / z))) / (z + z ^ 3)

/-- All quartic polynomials have transform independent of z. -/
theorem quarticTransform_polynomial (z p₀ p₁ p₂ p₃ p₄ : ℝ) (hz : z ≠ 0) :
    quarticTransform z (fun t => p₀ + p₁ * t + p₂ * t ^ 2 + p₃ * t ^ 3 + p₄ * t ^ 4) =
      2 * (p₁ + p₃) := by
  have hd : z + z ^ 3 ≠ 0 := by
    have hf : z + z ^ 3 = z * (1 + z ^ 2) := by ring
    rw [hf]
    exact mul_ne_zero hz (ne_of_gt (by nlinarith only [sq_nonneg z]))
  unfold quarticTransform
  field_simp [hz, hd]
  ring

/-- Resolvent transform as a rational function of x=z². -/
def resolventKernel (s x : ℝ) : ℝ :=
  -2 / s ^ 2 + (2 * (s ^ 2 - 1) / s ^ 2) * (x / ((s ^ 2 - x) * (1 - s ^ 2 * x)))

def resolventSlope (s x : ℝ) : ℝ :=
  2 * (s ^ 2 - 1) * (1 - x ^ 2) / ((s ^ 2 - x) ^ 2 * (1 - s ^ 2 * x) ^ 2)

theorem quarticTransform_resolvent (s z : ℝ) (hs : s ≠ 0) (hz : z ≠ 0)
    (h₁ : s ^ 2 - z ^ 2 ≠ 0) (h₂ : 1 - s ^ 2 * z ^ 2 ≠ 0) :
    quarticTransform z (fun t => 1 / (t + s)) = resolventKernel s (z ^ 2) := by
  have hsp : z + s ≠ 0 := by
    intro h
    apply h₁
    rw [show s = -z by linarith]
    ring
  have hsm : -z + s ≠ 0 := by
    intro h
    apply h₁
    rw [show s = z by linarith]
    ring
  have hsz : 1 / z + s ≠ 0 := by
    intro h
    apply h₂
    have hh := congrArg (fun t : ℝ => t * z) h
    field_simp [hz] at hh
    nlinarith [sq_nonneg (s * z + 1)]
  have hsz' : -1 / z + s ≠ 0 := by
    intro h
    apply h₂
    have hh := congrArg (fun t : ℝ => t * z) h
    field_simp [hz] at hh
    nlinarith [sq_nonneg (s * z - 1)]
  have hd : z + z ^ 3 ≠ 0 := by
    rw [show z + z ^ 3 = z * (1 + z ^ 2) by ring]
    exact mul_ne_zero hz (ne_of_gt (by nlinarith only [sq_nonneg z]))
  have hplus : 1 + s * z ≠ 0 := by
    intro h
    apply h₂
    rw [← mul_pow, show s * z = -1 by linarith]
    norm_num
  have hminus : -1 + s * z ≠ 0 := by
    intro h
    apply h₂
    rw [← mul_pow, show s * z = 1 by linarith]
    norm_num
  unfold quarticTransform resolventKernel
  field_simp [hs, hz, h₁, h₂, hsp, hsm, hsz, hsz', hd, hplus, hminus] <;>
    (try field_simp [hs, hz, h₁, h₂, hsp, hsm, hsz, hsz', hd, hplus, hminus]) <;> ring

theorem hasDerivAt_resolventKernel (s x : ℝ) (hs : s ≠ 0)
    (h₁ : s ^ 2 - x ≠ 0) (h₂ : 1 - s ^ 2 * x ≠ 0) :
    HasDerivAt (resolventKernel s) (resolventSlope s x) x := by
  have hleft := (hasDerivAt_id x).const_sub (s ^ 2)
  have hright := ((hasDerivAt_id x).const_mul (s ^ 2)).const_sub 1
  have hden := hleft.mul hright
  have hquot := (hasDerivAt_id x).div hden (mul_ne_zero h₁ h₂)
  convert (hasDerivAt_const x (-2 / s ^ 2)).add
    (hquot.const_mul (2 * (s ^ 2 - 1) / s ^ 2)) using 1 <;>
    (try funext t) <;>
    (try simp only [resolventKernel, resolventSlope, Pi.mul_apply, Pi.add_apply,
      Pi.div_apply, Pi.sub_apply, id_eq]) <;>
    field_simp [hs, h₁, h₂] <;> ring

/-- The exact reciprocity factor, including its negative sign. -/
theorem resolventSlope_reciprocal (s x : ℝ) (hs : s ≠ 0)
    (h₁ : s ^ 2 - x ≠ 0) (h₂ : 1 - s ^ 2 * x ≠ 0) :
    resolventSlope (1 / s) x = -(s ^ 6) * resolventSlope s x := by
  have hd₁ : (1 / s) ^ 2 - x = (1 - s ^ 2 * x) / s ^ 2 := by field_simp [hs] <;> ring
  have hd₂ : 1 - (1 / s) ^ 2 * x = (s ^ 2 - x) / s ^ 2 := by field_simp [hs] <;> ring
  unfold resolventSlope
  rw [hd₁, hd₂]
  field_simp [hs, h₁, h₂] <;> ring

theorem resolventSlope_pos {s x : ℝ} (hs : 1 < s) (hx : |x| < 1)
    (h₁ : s ^ 2 - x ≠ 0) (h₂ : 1 - s ^ 2 * x ≠ 0) : 0 < resolventSlope s x := by
  apply div_pos
  · have hx2 : x ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one x).mpr hx
    exact mul_pos (mul_pos (by norm_num) (by nlinarith only [hs])) (by linarith)
  · exact mul_pos (sq_pos_of_ne_zero h₁) (sq_pos_of_ne_zero h₂)

theorem resolventSlope_neg {s x : ℝ} (hs₀ : 0 ≤ s) (hs₁ : s < 1) (hx : |x| < 1)
    (h₁ : s ^ 2 - x ≠ 0) (h₂ : 1 - s ^ 2 * x ≠ 0) : resolventSlope s x < 0 := by
  apply div_neg_of_neg_of_pos
  · have hx2 : x ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one x).mpr hx
    have hs2 : s ^ 2 < 1 := by nlinarith only [hs₀, hs₁]
    exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num) (by linarith)) (by linarith)
  · exact mul_pos (sq_pos_of_ne_zero h₁) (sq_pos_of_ne_zero h₂)

/-- Density arising from the compact Stieltjes representation. -/
def branchDensity (a b r s : ℝ) : ℝ := (s - a) ^ r * (b - s) ^ (4 - r)

theorem branchDensity_pos {a b r s : ℝ} (hs : s ∈ Ioo a b) :
    0 < branchDensity a b r s :=
  mul_pos (Real.rpow_pos_of_pos (sub_pos.mpr hs.1) _)
    (Real.rpow_pos_of_pos (sub_pos.mpr hs.2) _)

theorem branchDensity_nonneg {a b r s : ℝ} (hs : s ∈ Icc a b) :
    0 ≤ branchDensity a b r s :=
  mul_nonneg (Real.rpow_nonneg (sub_nonneg.mpr hs.1) _)
    (Real.rpow_nonneg (sub_nonneg.mpr hs.2) _)

theorem continuous_branchDensity (a b r : ℝ) (hr : r ∈ Ioo 0 4) :
    Continuous (branchDensity a b r) :=
  ((continuous_id.sub continuous_const).rpow_const (fun _ => Or.inr hr.1.le)).mul
    ((continuous_const.sub continuous_id).rpow_const (fun _ => Or.inr (sub_pos.mpr hr.2).le))

/-- The strict reciprocal density comparison, for the full parameter range r<2. -/
theorem branchDensity_lt_reciprocal
    {a b r s : ℝ} (ha : 0 < a) (hab : a * b < 1)
    (hr : r ∈ Ioo 0 2) (hs : s ∈ Ioo 1 b) :
    branchDensity a b r s < s ^ 4 * branchDensity a b r (1 / s) := by
  have hs0 : 0 < s := lt_trans zero_lt_one hs.1
  have hb0 : 0 < b := hs0.trans hs.2
  have ha1 : a < 1 := by nlinarith [mul_pos ha (sub_pos.mpr (lt_trans hs.1 hs.2))]
  have has : a * s < 1 := by nlinarith [mul_pos ha (sub_pos.mpr hs.2)]
  have hC : 0 < 1 - a * s := sub_pos.mpr has
  have hB : 0 < b - s := sub_pos.mpr hs.2
  have hA : 0 < s - a := by linarith only [ha1, hs.1]
  have hD : 0 < b * s - 1 := by nlinarith [mul_pos (sub_pos.mpr hs.1) hb0]
  let U : ℝ := (s - a) / (1 - a * s)
  let V : ℝ := (b * s - 1) / (b - s)
  have hU : 1 < U := by
    apply (lt_div_iff₀ hC).mpr
    have hp := mul_pos (sub_pos.mpr hs.1) (by linarith : 0 < 1 + a)
    nlinarith
  have hVU : V - U = (1 - a * b) * (s ^ 2 - 1) / ((b - s) * (1 - a * s)) := by
    dsimp [U, V]
    rw [div_sub_div _ _ hB.ne' hC.ne']
    congr 1 <;> ring
  have hUV : U < V := by
    apply sub_pos.mp
    rw [hVU]
    exact div_pos (mul_pos (sub_pos.mpr hab) (by nlinarith only [hs.1])) (mul_pos hB hC)
  have hV : 1 < V := hU.trans hUV
  have hpowers : U ^ r < V ^ (4 - r) :=
    (Real.rpow_lt_rpow (lt_trans zero_lt_one hU).le hUV hr.1).trans
      (Real.rpow_lt_rpow_of_exponent_lt hV (by linarith [hr.2]))
  have hfactor : 0 < (1 - a * s) ^ r * (b - s) ^ (4 - r) :=
    mul_pos (Real.rpow_pos_of_pos hC _) (Real.rpow_pos_of_pos hB _)
  have hleft : branchDensity a b r s =
      ((1 - a * s) ^ r * (b - s) ^ (4 - r)) * U ^ r := by
    have hprod : (1 - a * s) * U = s - a := by dsimp [U]; field_simp [hC.ne']
    unfold branchDensity
    rw [← hprod, Real.mul_rpow hC.le (lt_trans zero_lt_one hU).le]
    ring
  have hright : s ^ 4 * branchDensity a b r (1 / s) =
      ((1 - a * s) ^ r * (b - s) ^ (4 - r)) * V ^ (4 - r) := by
    have h₁ : 1 / s - a = (1 - a * s) / s := by field_simp [hs0.ne'] <;> ring
    have h₂ : b - 1 / s = (b * s - 1) / s := by field_simp [hs0.ne'] <;> ring
    have hprod : (b - s) * V = b * s - 1 := by dsimp [V]; field_simp [hB.ne']
    have hsPow : s ^ r * s ^ (4 - r) = s ^ (4 : ℕ) := by
      rw [← Real.rpow_add hs0, show r + (4 - r) = (4 : ℝ) by ring]
      exact Real.rpow_natCast s 4
    unfold branchDensity
    rw [h₁, h₂, Real.div_rpow hC.le hs0.le, Real.div_rpow hD.le hs0.le,
      div_mul_div_comm, hsPow, ← hprod, Real.mul_rpow hB.le (lt_trans zero_lt_one hV).le]
    field_simp [hs0.ne'] <;> ring
  rw [hleft, hright]
  exact mul_lt_mul_of_pos_left hpowers hfactor

/-- In reciprocal coordinates the combined kernel contribution is strictly negative. -/
theorem paired_resolventSlope_neg
    {a b r s x : ℝ} (ha : 0 < a) (hab : a * b < 1)
    (hr : r ∈ Ioo 0 2) (hs : s ∈ Ioo 1 b) (hx : |x| < 1)
    (h₁ : s ^ 2 - x ≠ 0) (h₂ : 1 - s ^ 2 * x ≠ 0) :
    resolventSlope s x * (branchDensity a b r s - s ^ 4 * branchDensity a b r (1 / s)) < 0 :=
  mul_neg_of_pos_of_neg (resolventSlope_pos hs.1 hx h₁ h₂)
    (sub_neg.mpr (branchDensity_lt_reciprocal ha hab hr hs))

end PaperVerification.Hyperbolic

#print axioms PaperVerification.Hyperbolic.quarticTransform_polynomial
#print axioms PaperVerification.Hyperbolic.hasDerivAt_resolventKernel
#print axioms PaperVerification.Hyperbolic.branchDensity_lt_reciprocal
