module
public import PaperVerification.HyperbolicLocalization
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Tactic.LinearCombination
@[expose] public section
/-! # The large-scale Jensen bound

The two curvature facts used in Section 5.3 are proved on the full closed
half-line, including zero.  The final strict inequality covers all distinct
unaligned two-point supports and every nontrivial probability weight.
-/

noncomputable section

namespace PaperVerification.Hyperbolic

open Real Set

theorem sinh_cosh_sub_self_pos {v : ℝ} (hv : 0 < v) :
    0 < Real.sinh v * Real.cosh v - v := by
  let f : ℝ → ℝ := fun t => Real.sinh t * Real.cosh t - t
  have hd (t : ℝ) : HasDerivAt f (2 * Real.sinh t ^ 2) t := by
    convert ((Real.hasDerivAt_sinh t).mul (Real.hasDerivAt_cosh t)).sub (hasDerivAt_id t) using 1
    · rfl
    · nlinarith only [Real.cosh_sq_sub_sinh_sq t]
  have hm : StrictMonoOn f (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
      (((Real.continuous_sinh.mul Real.continuous_cosh).sub continuous_id).continuousOn)
    intro t ht
    have ht0 : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
    change 0 < deriv f t
    rw [(hd t).deriv]
    exact mul_pos (by norm_num) (sq_pos_of_ne_zero (Real.sinh_pos_iff.mpr ht0).ne')
  have h := hm (show (0 : ℝ) ∈ Ici 0 from le_rfl) hv.le hv
  simpa only [f, Real.sinh_zero, Real.cosh_zero, zero_mul, sub_zero] using h

theorem self_cosh_sub_sinh_pos {v : ℝ} (hv : 0 < v) :
    0 < v * Real.cosh v - Real.sinh v := by
  let f : ℝ → ℝ := fun t => t * Real.cosh t - Real.sinh t
  have hd (t : ℝ) : HasDerivAt f (t * Real.sinh t) t := by
    convert ((hasDerivAt_id t).mul (Real.hasDerivAt_cosh t)).sub (Real.hasDerivAt_sinh t) using 1
    · rfl
    · simp only [id_eq]
      ring
  have hm : StrictMonoOn f (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
      (((continuous_id.mul Real.continuous_cosh).sub Real.continuous_sinh).continuousOn)
    intro t ht
    have ht0 : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
    change 0 < deriv f t
    rw [(hd t).deriv]
    exact mul_pos ht0 (Real.sinh_pos_iff.mpr ht0)
  have h := hm (show (0 : ℝ) ∈ Ici 0 from le_rfl) hv.le hv
  simpa only [f, Real.sinh_zero, Real.cosh_zero, zero_mul, sub_zero] using h

theorem strictMonoOn_self_coth : StrictMonoOn (fun t : ℝ => t * coth t) (Ioi 0) := by
  have hd (t : ℝ) (ht : 0 < t) : HasDerivAt (fun t : ℝ => t * coth t)
      ((Real.sinh t * Real.cosh t - t) / Real.sinh t ^ 2) t := by
    have hs := (Real.sinh_pos_iff.mpr ht).ne'
    convert (hasDerivAt_id t).mul (hasDerivAt_coth t ht.ne') using 1 <;>
      (try funext s) <;> (try simp only [coth, id_eq, Pi.mul_apply]) <;>
      field_simp [hs] <;> linear_combination t * Real.cosh_sq_sub_sinh_sq t
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
  intro t ht
  have ht0 : 0 < t := interior_subset ht
  rw [(hd t ht0).deriv]
  exact div_pos (sinh_cosh_sub_self_pos ht0)
    (sq_pos_of_ne_zero (Real.sinh_pos_iff.mpr ht0).ne')

theorem strictAntiOn_sinh_scale_ratio {r : ℝ} (hr : r ∈ Ioo 0 1) :
    StrictAntiOn (fun t : ℝ => Real.sinh (r * t) / Real.sinh t) (Ioi 0) := by
  have hd (t : ℝ) (ht : 0 < t) :
      HasDerivAt (fun t : ℝ => Real.sinh (r * t) / Real.sinh t)
        (Real.sinh (r * t) / Real.sinh t * (r * coth (r * t) - coth t)) t := by
    have hs := (Real.sinh_pos_iff.mpr ht).ne'
    have hrs := (Real.sinh_pos_iff.mpr (mul_pos hr.1 ht)).ne'
    convert (((hasDerivAt_id t).const_mul r).sinh).div (Real.hasDerivAt_sinh t) hs using 1 <;>
      (try funext s) <;> (try simp only [coth, id_eq, Pi.div_apply, Function.comp_apply]) <;>
      field_simp [hs, hrs] <;> ring
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
  intro t ht
  have ht0 : 0 < t := interior_subset ht
  have hrt0 := mul_pos hr.1 ht0
  have hrt : r * t < t := by simpa only [one_mul] using mul_lt_mul_of_pos_right hr.2 ht0
  have hc := strictMonoOn_self_coth hrt0 ht0 hrt
  have hcot : r * coth (r * t) - coth t < 0 := by
    have hmul : t * (r * coth (r * t) - coth t) < 0 := by
      nlinarith only [hc]
    nlinarith only [hmul, ht0]
  rw [(hd t ht0).deriv]
  exact mul_neg_of_pos_of_neg
    (div_pos (Real.sinh_pos_iff.mpr hrt0) (Real.sinh_pos_iff.mpr ht0)) hcot

def coshSqrt (x : ℝ) : ℝ := Real.cosh (Real.sqrt x)

def logCoshSqrt (x : ℝ) : ℝ := Real.log (Real.cosh (Real.sqrt x))

theorem hasDerivAt_coshSqrt {x : ℝ} (hx : 0 < x) :
    HasDerivAt coshSqrt (Real.sinh (Real.sqrt x) / (2 * Real.sqrt x)) x := by
  convert (Real.hasDerivAt_sqrt hx.ne').cosh using 1 <;>
    (try funext t) <;> (try simp only [coshSqrt, Function.comp_apply]) <;> ring

theorem hasDerivAt_coshSqrt_derivative {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t => Real.sinh (Real.sqrt t) / (2 * Real.sqrt t))
      ((Real.sqrt x * Real.cosh (Real.sqrt x) - Real.sinh (Real.sqrt x)) /
        (4 * Real.sqrt x ^ 3)) x := by
  have hs := (Real.sqrt_pos.mpr hx).ne'
  convert ((Real.hasDerivAt_sqrt hx.ne').sinh).div
    ((Real.hasDerivAt_sqrt hx.ne').const_mul 2) (mul_ne_zero (by norm_num) hs) using 1 <;>
    (try funext t) <;> (try simp only [Pi.div_apply, Pi.mul_apply, Function.comp_apply]) <;>
    field_simp [hs] <;> ring

theorem deriv2_coshSqrt {x : ℝ} (hx : 0 < x) :
    deriv (deriv coshSqrt) x =
      (Real.sqrt x * Real.cosh (Real.sqrt x) - Real.sinh (Real.sqrt x)) /
        (4 * Real.sqrt x ^ 3) := by
  have hd : (Ioi 0).EqOn (deriv coshSqrt)
      (fun t => Real.sinh (Real.sqrt t) / (2 * Real.sqrt t)) :=
    fun t ht => (hasDerivAt_coshSqrt ht).deriv
  exact (hd.deriv isOpen_Ioi hx).trans (hasDerivAt_coshSqrt_derivative hx).deriv

theorem strictConvexOn_coshSqrt : StrictConvexOn ℝ (Ici 0) coshSqrt := by
  apply strictConvexOn_of_deriv2_pos (convex_Ici 0)
    (Real.continuous_cosh.comp Real.continuous_sqrt).continuousOn
  intro x hx
  have hx0 : 0 < x := by simpa only [interior_Ici, mem_Ioi] using hx
  change 0 < deriv (deriv coshSqrt) x
  rw [deriv2_coshSqrt hx0]
  exact div_pos (self_cosh_sub_sinh_pos (Real.sqrt_pos.mpr hx0))
    (mul_pos (by norm_num) (pow_pos (Real.sqrt_pos.mpr hx0) 3))

theorem hasDerivAt_logCoshSqrt {x : ℝ} (hx : 0 < x) :
    HasDerivAt logCoshSqrt (Real.tanh (Real.sqrt x) / (2 * Real.sqrt x)) x := by
  have hs := (Real.sqrt_pos.mpr hx).ne'
  have hc := (Real.cosh_pos (Real.sqrt x)).ne'
  convert (hasDerivAt_coshSqrt hx).log hc using 1 <;>
    (try funext t) <;>
    (try simp only [logCoshSqrt, coshSqrt, Real.tanh_eq_sinh_div_cosh, Function.comp_apply]) <;>
    field_simp [hs, hc] <;> ring

theorem hasDerivAt_logCoshSqrt_derivative {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t => Real.tanh (Real.sqrt t) / (2 * Real.sqrt t))
      ((Real.sqrt x - Real.sinh (Real.sqrt x) * Real.cosh (Real.sqrt x)) /
        (4 * Real.sqrt x ^ 3 * Real.cosh (Real.sqrt x) ^ 2)) x := by
  have hs := (Real.sqrt_pos.mpr hx).ne'
  have hc := (Real.cosh_pos (Real.sqrt x)).ne'
  have ht := (hasDerivAt_tanh (Real.sqrt x)).comp x (Real.hasDerivAt_sqrt hx.ne')
  simp only [one_sub_tanh_sq] at ht
  convert ht.div ((Real.hasDerivAt_sqrt hx.ne').const_mul 2)
    (mul_ne_zero (by norm_num) hs) using 1 <;>
    (try funext t) <;>
    (try simp only [Pi.div_apply, Pi.mul_apply, Function.comp_apply, Real.tanh_eq_sinh_div_cosh]) <;>
    field_simp [hs, hc] <;> ring

theorem deriv2_logCoshSqrt {x : ℝ} (hx : 0 < x) :
    deriv (deriv logCoshSqrt) x =
      (Real.sqrt x - Real.sinh (Real.sqrt x) * Real.cosh (Real.sqrt x)) /
        (4 * Real.sqrt x ^ 3 * Real.cosh (Real.sqrt x) ^ 2) := by
  have hd : (Ioi 0).EqOn (deriv logCoshSqrt)
      (fun t => Real.tanh (Real.sqrt t) / (2 * Real.sqrt t)) :=
    fun t ht => (hasDerivAt_logCoshSqrt ht).deriv
  exact (hd.deriv isOpen_Ioi hx).trans (hasDerivAt_logCoshSqrt_derivative hx).deriv

theorem strictConcaveOn_logCoshSqrt : StrictConcaveOn ℝ (Ici 0) logCoshSqrt := by
  apply strictConcaveOn_of_deriv2_neg (convex_Ici 0)
    (((Real.continuous_cosh.comp Real.continuous_sqrt).log
      (fun x => (Real.cosh_pos (Real.sqrt x)).ne')).continuousOn)
  intro x hx
  have hx0 : 0 < x := by simpa only [interior_Ici, mem_Ioi] using hx
  change deriv (deriv logCoshSqrt) x < 0
  rw [deriv2_logCoshSqrt hx0]
  exact div_neg_of_neg_of_pos (by linarith only [sinh_cosh_sub_self_pos (Real.sqrt_pos.mpr hx0)])
    (mul_pos (mul_pos (by norm_num) (pow_pos (Real.sqrt_pos.mpr hx0) 3))
      (sq_pos_of_ne_zero (Real.cosh_pos _).ne'))

theorem coshSqrt_square (v : ℝ) : coshSqrt (v ^ 2) = Real.cosh v := by
  rw [coshSqrt, Real.sqrt_sq_eq_abs, Real.cosh_abs]

theorem logCoshSqrt_square (v : ℝ) : logCoshSqrt (v ^ 2) = Real.log (Real.cosh v) := by
  rw [logCoshSqrt, Real.sqrt_sq_eq_abs, Real.cosh_abs]

/-- The strict bound in equation (23) throughout the unaligned range.
No assumption on the size of the support values is used. -/
theorem two_point_centered_cosh_gt_geometric
    {w v₁ v₂ : ℝ} (hw : w ∈ Ioo 0 1) (hv : v₁ < v₂) (hs : v₁ + v₂ < 0) :
    Real.exp (w * Real.log (Real.cosh v₁) + (1 - w) * Real.log (Real.cosh v₂)) <
      w * Real.cosh (v₁ - 2 * (w * v₁ + (1 - w) * v₂)) +
        (1 - w) * Real.cosh (v₂ - 2 * (w * v₁ + (1 - w) * v₂)) := by
  let m := w * v₁ + (1 - w) * v₂
  let Q := w * v₁ ^ 2 + (1 - w) * v₂ ^ 2
  have hm2 : w * (v₁ - 2 * m) ^ 2 + (1 - w) * (v₂ - 2 * m) ^ 2 = Q := by
    dsimp [m, Q]
    ring
  have hne : v₁ ^ 2 ≠ v₂ ^ 2 := by
    intro he
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp he with h | h
    · exact hv.ne h
    · linarith
  have hlog := strictConcaveOn_logCoshSqrt.2 (sq_nonneg v₁) (sq_nonneg v₂) hne
    hw.1 (sub_pos.mpr hw.2) (by ring : w + (1 - w) = 1)
  simp only [smul_eq_mul, logCoshSqrt_square] at hlog
  have hconv := strictConvexOn_coshSqrt.convexOn.2
    (sq_nonneg (v₁ - 2 * m)) (sq_nonneg (v₂ - 2 * m)) hw.1.le
    (sub_nonneg.mpr hw.2.le) (by ring : w + (1 - w) = 1)
  simp only [smul_eq_mul, hm2, coshSqrt_square] at hconv
  have hexp := Real.exp_lt_exp.mpr hlog
  change _ < Real.exp (Real.log (Real.cosh (Real.sqrt Q))) at hexp
  rw [Real.exp_log (Real.cosh_pos _)] at hexp
  exact hexp.trans_le hconv

end PaperVerification.Hyperbolic

#print axioms PaperVerification.Hyperbolic.strictConvexOn_coshSqrt
#print axioms PaperVerification.Hyperbolic.strictConcaveOn_logCoshSqrt
#print axioms PaperVerification.Hyperbolic.two_point_centered_cosh_gt_geometric
