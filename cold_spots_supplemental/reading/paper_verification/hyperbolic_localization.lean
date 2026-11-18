module
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
@[expose] public section
/-! # Calculus underlying the two-support localization

This file develops the exact second-derivative and strict-convexity calculations
in equation (13) of the cold-spots paper. These facts do not assume the
hyperbolic inequality, a finite-support reduction, or a Gaussian minimum.
-/

noncomputable section

namespace PaperVerification.Hyperbolic

open Real Set

/-- The hyperbolic cotangent, used only away from zero. -/
def coth (p : ℝ) : ℝ := Real.cosh p / Real.sinh p

/-- The derivative of tanh in a form convenient for exact polynomial certificates. -/
theorem hasDerivAt_tanh (p : ℝ) :
    HasDerivAt Real.tanh (1 - (Real.tanh p) ^ 2) p := by
  have hc : Real.cosh p ≠ 0 := (Real.cosh_pos p).ne'
  convert (Real.hasDerivAt_sinh p).div (Real.hasDerivAt_cosh p) hc using 1 <;>
    (try funext t) <;> (try simp only [Real.tanh_eq_sinh_div_cosh, Pi.div_apply]) <;> field_simp [hc] <;>
    nlinarith only [Real.cosh_sq_sub_sinh_sq p]

theorem hasDerivAt_coth (p : ℝ) (hp : p ≠ 0) :
    HasDerivAt coth (1 - coth p ^ 2) p := by
  have hs : Real.sinh p ≠ 0 := Real.sinh_ne_zero.mpr hp
  unfold coth
  convert (Real.hasDerivAt_cosh p).div (Real.hasDerivAt_sinh p) hs using 1 <;>
    field_simp [hs] <;> nlinarith only [Real.cosh_sq_sub_sinh_sq p]

/-- First quotient in equation (13). -/
def coshQuotient (R p : ℝ) : ℝ := (Real.cosh (2 * p - R)) ^ 2 / (Real.cosh p) ^ 2

/-- Third quotient in equation (13); its domain is p>0. -/
def sinhQuotient (R p : ℝ) : ℝ := (Real.cosh (2 * p - R)) ^ 2 / (Real.sinh p) ^ 2

private theorem hasDerivAt_centered (R p : ℝ) : HasDerivAt (fun t : ℝ => 2 * t - R) 2 p := by
  simpa using ((hasDerivAt_id p).const_mul 2).sub_const R

theorem hasDerivAt_coshQuotient (R p : ℝ) :
    HasDerivAt (coshQuotient R)
      (coshQuotient R p * (4 * Real.tanh (2 * p - R) - 2 * Real.tanh p)) p := by
  have hc : Real.cosh p ≠ 0 := (Real.cosh_pos p).ne'
  have hC : Real.cosh (2 * p - R) ≠ 0 := (Real.cosh_pos _).ne'
  convert (((hasDerivAt_centered R p).cosh).pow 2).div
    ((Real.hasDerivAt_cosh p).pow 2) (pow_ne_zero 2 hc) using 1 <;>
    (try funext t) <;>
    (try simp only [coshQuotient, Real.tanh_eq_sinh_div_cosh, Pi.pow_apply,
      Pi.mul_apply, Pi.sub_apply, Pi.div_apply, Function.comp_apply, Nat.reduceSub, Nat.cast_ofNat, pow_one]) <;>
    field_simp [hc, hC] <;> ring

theorem hasDerivAt_coshQuotient_derivative (R p : ℝ) :
    HasDerivAt
      (fun t => coshQuotient R t * (4 * Real.tanh (2 * t - R) - 2 * Real.tanh t))
      (coshQuotient R p * (6 + 8 * Real.tanh (2 * p - R) ^ 2 +
        6 * Real.tanh p ^ 2 - 16 * Real.tanh (2 * p - R) * Real.tanh p)) p := by
  have hT := (hasDerivAt_tanh (2 * p - R)).comp p (hasDerivAt_centered R p)
  have ht := hasDerivAt_tanh p
  convert (hasDerivAt_coshQuotient R p).mul
    ((hT.const_mul 4).sub (ht.const_mul 2)) using 1 <;>
    (try funext t) <;>
    (try simp only [Function.comp_apply, Pi.mul_apply, Pi.sub_apply]) <;> ring

theorem deriv2_coshQuotient (R p : ℝ) :
    deriv (deriv (coshQuotient R)) p =
      coshQuotient R p * (6 + 8 * Real.tanh (2 * p - R) ^ 2 +
        6 * Real.tanh p ^ 2 - 16 * Real.tanh (2 * p - R) * Real.tanh p) := by
  have hd : deriv (coshQuotient R) =
      fun t => coshQuotient R t * (4 * Real.tanh (2 * t - R) - 2 * Real.tanh t) :=
    funext fun t => (hasDerivAt_coshQuotient R t).deriv
  rw [hd]
  exact (hasDerivAt_coshQuotient_derivative R p).deriv

theorem coshQuotient_secondFactor_pos (R p : ℝ) :
    0 < 6 + 8 * Real.tanh (2 * p - R) ^ 2 + 6 * Real.tanh p ^ 2 -
      16 * Real.tanh (2 * p - R) * Real.tanh p := by
  nlinarith only [sq_nonneg (Real.tanh (2 * p - R) - Real.tanh p), Real.tanh_sq_lt_one p]

theorem continuous_coshQuotient (R : ℝ) : Continuous (coshQuotient R) := by
  unfold coshQuotient
  exact ((Real.continuous_cosh.comp ((continuous_const.mul continuous_id).sub continuous_const)).pow 2).div
    (Real.continuous_cosh.pow 2) (fun p => pow_ne_zero 2 (Real.cosh_pos p).ne')

/-- Strict convexity is global; no sign restriction on R is needed for this quotient. -/
theorem strictConvexOn_coshQuotient (R : ℝ) : StrictConvexOn ℝ Set.univ (coshQuotient R) := by
  apply strictConvexOn_of_deriv2_pos' convex_univ (continuous_coshQuotient R).continuousOn
  intro p hp
  change 0 < deriv (deriv (coshQuotient R)) p
  rw [deriv2_coshQuotient]
  apply mul_pos
  · exact div_pos (pow_pos (Real.cosh_pos _) 2) (pow_pos (Real.cosh_pos _) 2)
  · exact coshQuotient_secondFactor_pos R p

theorem hasDerivAt_sinhQuotient (R p : ℝ) (hp : p ≠ 0) :
    HasDerivAt (sinhQuotient R)
      (sinhQuotient R p * (4 * Real.tanh (2 * p - R) - 2 * coth p)) p := by
  have hs : Real.sinh p ≠ 0 := Real.sinh_ne_zero.mpr hp
  have hC : Real.cosh (2 * p - R) ≠ 0 := (Real.cosh_pos _).ne'
  convert (((hasDerivAt_centered R p).cosh).pow 2).div
    ((Real.hasDerivAt_sinh p).pow 2) (pow_ne_zero 2 hs) using 1 <;>
    (try funext t) <;>
    (try simp only [sinhQuotient, coth, Real.tanh_eq_sinh_div_cosh, Pi.pow_apply,
      Pi.mul_apply, Pi.sub_apply, Pi.div_apply, Function.comp_apply, Nat.reduceSub, Nat.cast_ofNat, pow_one]) <;>
    field_simp [hs, hC] <;> ring

theorem hasDerivAt_sinhQuotient_derivative (R p : ℝ) (hp : p ≠ 0) :
    HasDerivAt
      (fun t => sinhQuotient R t * (4 * Real.tanh (2 * t - R) - 2 * coth t))
      (sinhQuotient R p * (6 + 8 * Real.tanh (2 * p - R) ^ 2 +
        6 * coth p ^ 2 - 16 * Real.tanh (2 * p - R) * coth p)) p := by
  have hT := (hasDerivAt_tanh (2 * p - R)).comp p (hasDerivAt_centered R p)
  have ht := hasDerivAt_coth p hp
  convert (hasDerivAt_sinhQuotient R p hp).mul
    ((hT.const_mul 4).sub (ht.const_mul 2)) using 1 <;>
    (try funext t) <;>
    (try simp only [Function.comp_apply, Pi.mul_apply, Pi.sub_apply]) <;> ring

theorem deriv2_sinhQuotient (R p : ℝ) (hp : 0 < p) :
    deriv (deriv (sinhQuotient R)) p =
      sinhQuotient R p * (6 + 8 * Real.tanh (2 * p - R) ^ 2 +
        6 * coth p ^ 2 - 16 * Real.tanh (2 * p - R) * coth p) := by
  have hd : (Set.Ioi 0).EqOn (deriv (sinhQuotient R))
      (fun t => sinhQuotient R t * (4 * Real.tanh (2 * t - R) - 2 * coth t)) :=
    fun t ht => (hasDerivAt_sinhQuotient R t (ne_of_gt ht)).deriv
  exact (hd.deriv isOpen_Ioi hp).trans (hasDerivAt_sinhQuotient_derivative R p hp.ne').deriv

theorem one_le_coth {p : ℝ} (hp : 0 < p) : 1 ≤ coth p := by
  unfold coth
  apply (le_div_iff₀ (Real.sinh_pos_iff.mpr hp)).mpr
  simpa only [one_mul] using (Real.sinh_lt_cosh (x := p)).le

theorem sinhQuotient_secondFactor_pos (R p : ℝ) (hp : 0 < p) :
    0 < 6 + 8 * Real.tanh (2 * p - R) ^ 2 + 6 * coth p ^ 2 -
      16 * Real.tanh (2 * p - R) * coth p := by
  have hu := one_le_coth hp
  have hT := (Real.tanh_lt_one (2 * p - R)).le
  have hprod : 0 ≤ (1 - Real.tanh (2 * p - R)) *
      (2 * coth p - Real.tanh (2 * p - R) - 1) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith only [hprod, sq_nonneg (coth p - 4 / 3)]

theorem continuousOn_sinhQuotient (R : ℝ) : ContinuousOn (sinhQuotient R) (Set.Ioi 0) := by
  unfold sinhQuotient
  apply (((Real.continuous_cosh.comp ((continuous_const.mul continuous_id).sub continuous_const)).pow 2).continuousOn).div
    (Real.continuous_sinh.pow 2).continuousOn
  intro p hp
  exact pow_ne_zero 2 (Real.sinh_ne_zero.mpr (ne_of_gt hp))

/-- The second type of quotient is strictly convex on the entire positive half-line. -/
theorem strictConvexOn_sinhQuotient (R : ℝ) :
    StrictConvexOn ℝ (Set.Ioi 0) (sinhQuotient R) := by
  apply strictConvexOn_of_deriv2_pos' (convex_Ioi 0) (continuousOn_sinhQuotient R)
  intro p hp
  change 0 < deriv (deriv (sinhQuotient R)) p
  rw [deriv2_sinhQuotient R p hp]
  apply mul_pos
  · exact div_pos (pow_pos (Real.cosh_pos _) 2) (pow_pos (Real.sinh_pos_iff.mpr hp) 2)
  · exact sinhQuotient_secondFactor_pos R p hp

/-- Positive scalar multiplication preserves strict convexity. -/
theorem strictConvexOn_mul_pos {s : Set ℝ} {f : ℝ → ℝ}
    (hf : StrictConvexOn ℝ s f) {c : ℝ} (hc : 0 < c) :
    StrictConvexOn ℝ s (fun x => c * f x) := by
  refine ⟨hf.1, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  simp only [smul_eq_mul]
  calc
    c * f (a * x + b * y) < c * (a * f x + b * f y) := by
      exact mul_lt_mul_of_pos_left (by simpa only [smul_eq_mul] using hf.2 hx hy hxy ha hb hab) hc
    _ = a * (c * f x) + b * (c * f y) := by ring

/-- Nonnegative scalar multiplication preserves convexity, including a vanishing term. -/
theorem convexOn_mul_nonneg {s : Set ℝ} {f : ℝ → ℝ}
    (hf : ConvexOn ℝ s f) {c : ℝ} (hc : 0 ≤ c) :
    ConvexOn ℝ s (fun x => c * f x) := by
  refine ⟨hf.1, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  calc
    c * f (a * x + b * y) ≤ c * (a * f x + b * f y) := by
      exact mul_le_mul_of_nonneg_left (by simpa only [smul_eq_mul] using hf.2 hx hy ha hb hab) hc
    _ = a * (c * f x) + b * (c * f y) := by ring

/-- Reflection preserves strict convexity on an interval symmetric about R/2. -/
theorem strictConvexOn_reflection {R : ℝ} {f : ℝ → ℝ}
    (hf : StrictConvexOn ℝ (Ioo 0 R) f) :
    StrictConvexOn ℝ (Ioo 0 R) (fun p => f (R - p)) := by
  refine ⟨convex_Ioo 0 R, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hRx : R - x ∈ Ioo 0 R := by constructor <;> linarith [hx.1, hx.2]
  have hRy : R - y ∈ Ioo 0 R := by constructor <;> linarith [hy.1, hy.2]
  have hRxy : R - x ≠ R - y := by intro h; apply hxy; linarith
  have hs := hf.2 hRx hRy hRxy ha hb hab
  simp only [smul_eq_mul] at hs ⊢
  have harg : a * (R - x) + b * (R - y) = R - (a * x + b * y) := by
    calc
      _ = (a + b) * R - (a * x + b * y) := by ring
      _ = R - (a * x + b * y) := by rw [hab, one_mul]
  rwa [harg] at hs

/-- Right-hand side of equation (13), using reflection to keep all four quotient
functions in their already established strictly convex form. -/
def curvatureModel (R A C B D F p : ℝ) : ℝ :=
  (A * coshQuotient R p + C * coshQuotient R (R - p) +
    B * sinhQuotient R p + D * sinhQuotient R (R - p)) / F - 1

theorem strictConvexOn_curvatureModel
    (R A C B D F : ℝ) (hA : 0 < A) (hC : 0 < C)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hF : 0 < F) :
    StrictConvexOn ℝ (Ioo 0 R) (curvatureModel R A C B D F) := by
  have hc : StrictConvexOn ℝ (Ioo 0 R) (coshQuotient R) :=
    (strictConvexOn_coshQuotient R).subset (subset_univ _) (convex_Ioo 0 R)
  have hs : StrictConvexOn ℝ (Ioo 0 R) (sinhQuotient R) :=
    (strictConvexOn_sinhQuotient R).subset (fun _ hp => hp.1) (convex_Ioo 0 R)
  have hsum := ((strictConvexOn_mul_pos hc hA).add
    (strictConvexOn_mul_pos (strictConvexOn_reflection hc) hC)).add_convexOn
    ((convexOn_mul_nonneg hs.convexOn hB).add
      (convexOn_mul_nonneg (strictConvexOn_reflection hs).convexOn hD))
  have hscaled := (strictConvexOn_mul_pos hsum (one_div_pos.mpr hF)).add_const (-1)
  apply hscaled.congr
  intro p hp
  simp only [Pi.add_apply, curvatureModel]
  ring

theorem coshQuotient_reflected (R p : ℝ) :
    coshQuotient R (R - p) = Real.cosh (2 * p - R) ^ 2 / Real.cosh (R - p) ^ 2 := by
  unfold coshQuotient
  have he : 2 * (R - p) - R = -(2 * p - R) := by ring
  rw [he, Real.cosh_neg]

theorem sinhQuotient_reflected (R p : ℝ) :
    sinhQuotient R (R - p) = Real.cosh (2 * p - R) ^ 2 / Real.sinh (R - p) ^ 2 := by
  unfold sinhQuotient
  have he : 2 * (R - p) - R = -(2 * p - R) := by ring
  rw [he, Real.cosh_neg]

/-- The real first-variation potential on the open interval. At an endpoint,
a positive coefficient of minus log sinh is interpreted through its positive
infinite limit; no endpoint value is silently assigned by this definition. -/
def variationPotential (R A C B D F p : ℝ) : ℝ :=
  4 / F * (A * Real.log (Real.cosh p) + C * Real.log (Real.cosh (R - p)) -
    B * Real.log (Real.sinh p) - D * Real.log (Real.sinh (R - p))) -
    Real.log (Real.cosh (2 * p - R))

def variationDerivative (R A C B D F p : ℝ) : ℝ :=
  4 / F * (A * Real.tanh p - C * Real.tanh (R - p) -
    B * coth p + D * coth (R - p)) - 2 * Real.tanh (2 * p - R)

def variationSecondDerivative (R A C B D F p : ℝ) : ℝ :=
  4 / F * (A / Real.cosh p ^ 2 + C / Real.cosh (R - p) ^ 2 +
    B / Real.sinh p ^ 2 + D / Real.sinh (R - p) ^ 2) -
    4 / Real.cosh (2 * p - R) ^ 2

theorem hasDerivAt_log_cosh (p : ℝ) :
    HasDerivAt (fun t => Real.log (Real.cosh t)) (Real.tanh p) p := by
  simpa only [Real.tanh_eq_sinh_div_cosh] using
    (Real.hasDerivAt_cosh p).log (Real.cosh_pos p).ne'

theorem hasDerivAt_log_sinh (p : ℝ) (hp : p ≠ 0) :
    HasDerivAt (fun t => Real.log (Real.sinh t)) (coth p) p := by
  simpa only [coth] using (Real.hasDerivAt_sinh p).log (Real.sinh_ne_zero.mpr hp)

private theorem hasDerivAt_reflection (R p : ℝ) :
    HasDerivAt (fun t : ℝ => R - t) (-1) p := by
  simpa using (hasDerivAt_id p).const_sub R

theorem hasDerivAt_variationPotential (R A C B D F p : ℝ) (hp : p ∈ Ioo 0 R) :
    HasDerivAt (variationPotential R A C B D F)
      (variationDerivative R A C B D F p) p := by
  have ha := (hasDerivAt_log_cosh p).const_mul A
  have hc := ((hasDerivAt_log_cosh (R - p)).comp p (hasDerivAt_reflection R p)).const_mul C
  have hb := (hasDerivAt_log_sinh p hp.1.ne').const_mul B
  have hd := ((hasDerivAt_log_sinh (R - p) (sub_pos.mpr hp.2).ne').comp p
    (hasDerivAt_reflection R p)).const_mul D
  have hv := (hasDerivAt_log_cosh (2 * p - R)).comp p (hasDerivAt_centered R p)
  convert ((((ha.add hc).sub hb).sub hd).const_mul (4 / F)).sub hv using 1 <;>
    (try funext t) <;>
    (try simp only [variationPotential, variationDerivative, Function.comp_apply,
      Pi.add_apply, Pi.sub_apply, Pi.mul_apply]) <;> ring

theorem one_sub_tanh_sq (p : ℝ) : 1 - Real.tanh p ^ 2 = 1 / Real.cosh p ^ 2 := by
  rw [Real.tanh_eq_sinh_div_cosh]
  have hc := (Real.cosh_pos p).ne'
  field_simp [hc]
  nlinarith only [Real.cosh_sq_sub_sinh_sq p]

theorem one_sub_coth_sq (p : ℝ) (hp : p ≠ 0) :
    1 - coth p ^ 2 = -(1 / Real.sinh p ^ 2) := by
  unfold coth
  have hs := Real.sinh_ne_zero.mpr hp
  field_simp [hs]
  nlinarith only [Real.cosh_sq_sub_sinh_sq p]

theorem hasDerivAt_variationDerivative (R A C B D F p : ℝ) (hp : p ∈ Ioo 0 R) :
    HasDerivAt (variationDerivative R A C B D F)
      (variationSecondDerivative R A C B D F p) p := by
  have ha := (hasDerivAt_tanh p).const_mul A
  have hc := ((hasDerivAt_tanh (R - p)).comp p (hasDerivAt_reflection R p)).const_mul C
  have hb := (hasDerivAt_coth p hp.1.ne').const_mul B
  have hd := ((hasDerivAt_coth (R - p) (sub_pos.mpr hp.2).ne').comp p
    (hasDerivAt_reflection R p)).const_mul D
  have hv := ((hasDerivAt_tanh (2 * p - R)).comp p (hasDerivAt_centered R p)).const_mul 2
  convert ((((ha.sub hc).sub hb).add hd).const_mul (4 / F)).sub hv using 1 <;>
    (try funext t) <;>
    (try simp only [variationDerivative, variationSecondDerivative, Function.comp_apply,
      Pi.add_apply, Pi.sub_apply, Pi.mul_apply, one_sub_tanh_sq,
      one_sub_coth_sq p hp.1.ne', one_sub_coth_sq (R - p) (sub_pos.mpr hp.2).ne']) <;> ring

theorem deriv2_variationPotential (R A C B D F p : ℝ) (hp : p ∈ Ioo 0 R) :
    deriv (deriv (variationPotential R A C B D F)) p =
      variationSecondDerivative R A C B D F p := by
  have hd : (Ioo 0 R).EqOn (deriv (variationPotential R A C B D F))
      (variationDerivative R A C B D F) :=
    fun t ht => (hasDerivAt_variationPotential R A C B D F t ht).deriv
  exact (hd.deriv isOpen_Ioo hp).trans
    (hasDerivAt_variationDerivative R A C B D F p hp).deriv

/-- Equation (13), with the positive normalization made explicit. -/
theorem variationSecondDerivative_eq_curvatureModel
    (R A C B D F p : ℝ) (hF : F ≠ 0) (hp : p ∈ Ioo 0 R) :
    variationSecondDerivative R A C B D F p =
      (4 / Real.cosh (2 * p - R) ^ 2) * curvatureModel R A C B D F p := by
  have hcp := (Real.cosh_pos p).ne'
  have hcr := (Real.cosh_pos (R - p)).ne'
  have hcv := (Real.cosh_pos (2 * p - R)).ne'
  have hsp := Real.sinh_ne_zero.mpr hp.1.ne'
  have hsr := Real.sinh_ne_zero.mpr (sub_pos.mpr hp.2).ne'
  unfold curvatureModel variationSecondDerivative
  rw [coshQuotient_reflected R p, sinhQuotient_reflected R p]
  unfold coshQuotient sinhQuotient
  field_simp [hF, hcp, hcr, hcv, hsp, hsr] <;> ring

end PaperVerification.Hyperbolic

#print axioms PaperVerification.Hyperbolic.strictConvexOn_coshQuotient
#print axioms PaperVerification.Hyperbolic.strictConvexOn_sinhQuotient

#print axioms PaperVerification.Hyperbolic.strictConvexOn_curvatureModel
#print axioms PaperVerification.Hyperbolic.variationSecondDerivative_eq_curvatureModel
