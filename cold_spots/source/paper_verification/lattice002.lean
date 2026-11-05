module

public import Lean.Elab.BuiltinEvalCommand
public meta import Lean.Elab.BuiltinEvalCommand
public import Lean.Util.CollectAxioms
public meta import Lean.Util.CollectAxioms
public import Lean.Util.FoldConsts
public meta import Lean.Util.FoldConsts
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Group.Int.Even
public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Order.Compact
public import paper_verification.lattice001

@[expose] public section


-- BEGIN ORIGINAL PaperVerification.HyperbolicStieltjes
section Source_HyperbolicStieltjes

-- original header: module
-- original header: public import PaperVerification.HyperbolicKernelIntegral
-- original header: public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation
-- original header: public import Mathlib.MeasureTheory.Function.JacobianOneDim
-- original header: @[expose] public section
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
end
end Source_HyperbolicStieltjes
-- END ORIGINAL PaperVerification.HyperbolicStieltjes


-- BEGIN ORIGINAL PaperVerification.HyperbolicScale
section Source_HyperbolicScale

-- original header: module
-- original header: public import PaperVerification.HyperbolicStieltjes
-- original header: public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
-- original header: public import Mathlib.Analysis.Normed.Group.Bounded
-- original header: @[expose] public section
/-! # Strict scale comparison

Differentiation of the compact resolvent integral is justified by a uniform
bound on a compact rectangle. The Stieltjes identities then give the exact
strict monotonicity in both weight ranges.
-/

noncomputable section

namespace PaperVerification.Hyperbolic

open Real Set MeasureTheory intervalIntegral Filter Topology

/-- A compact-rectangle form of differentiation under an interval integral. -/
theorem hasDerivAt_integral_of_compact_rectangle
    {a b l u x : ℝ} (hab : a ≤ b) (hx : x ∈ Ioo l u)
    {F F' : ℝ → ℝ → ℝ}
    (hF : ∀ y ∈ Icc l u, ContinuousOn (F y) (Icc a b))
    (hF' : ContinuousOn (fun p : ℝ × ℝ => F' p.1 p.2) (Icc l u ×ˢ Icc a b))
    (hd : ∀ y ∈ Icc l u, ∀ s ∈ Icc a b, HasDerivAt (fun y => F y s) (F' y s) y) :
    HasDerivAt (fun y => ∫ s in a..b, F y s) (∫ s in a..b, F' x s) x := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hF'
  have hxi : x ∈ Icc l u := ⟨hx.1.le, hx.2.le⟩
  have hF'x : ContinuousOn (F' x) (Icc a b) :=
    hF'.comp (continuousOn_const.prodMk continuousOn_id) (fun s hs => ⟨hxi, hs⟩)
  apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := fun _ => C) (Ioo_mem_nhds hx.1 hx.2) ?_
    ((hF x hxi).intervalIntegrable_of_Icc hab) ?_ ?_ intervalIntegrable_const ?_).2
  · filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    rw [uIoc_of_le hab]
    exact ((hF y ⟨hy.1.le, hy.2.le⟩).mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · rw [uIoc_of_le hab]
    exact (hF'x.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · apply Filter.Eventually.of_forall
    intro s hs y hy
    rw [uIoc_of_le hab] at hs
    exact hC (y, s) ⟨⟨hy.1.le, hy.2.le⟩, ⟨hs.1.le, hs.2⟩⟩
  · apply Filter.Eventually.of_forall
    intro s hs y hy
    apply hd y ⟨hy.1.le, hy.2.le⟩ s
    rw [uIoc_of_le hab] at hs
    exact ⟨hs.1.le, hs.2⟩

def resolventIntegral (a b r x : ℝ) : ℝ :=
  ∫ s in a..b, branchDensity a b r s * resolventKernel s x

def resolventDomain (a b : ℝ) : Set ℝ := Ioo 0 (min (a ^ 2) (1 / b ^ 2))

theorem resolventDomain_iff {a b x : ℝ} (hb : 0 < b) :
    x ∈ resolventDomain a b ↔ 0 < x ∧ x < a ^ 2 ∧ b ^ 2 * x < 1 := by
  have hb2 : 0 < b ^ 2 := sq_pos_of_ne_zero hb.ne'
  simp only [resolventDomain, mem_Ioo, lt_min_iff]
  constructor
  · rintro ⟨hx, hxa, hxb⟩
    exact ⟨hx, hxa, by simpa only [mul_comm] using (lt_div_iff₀ hb2).mp hxb⟩
  · rintro ⟨hx, hxa, hxb⟩
    exact ⟨hx, hxa, (lt_div_iff₀ hb2).mpr (by simpa only [mul_comm] using hxb)⟩

theorem continuousOn_resolventKernel_in_s {a b x : ℝ}
    (ha : 0 < a) (hx : 0 < x) (hxa : x < a ^ 2) (hxb : b ^ 2 * x < 1) :
    ContinuousOn (fun s => resolventKernel s x) (Icc a b) := by
  have hs0 : ∀ s ∈ Icc a b, s ≠ 0 := fun s hs => (ha.trans_le hs.1).ne'
  have hden : ∀ s ∈ Icc a b, (s ^ 2 - x) * (1 - s ^ 2 * x) ≠ 0 := by
    intro s hs
    obtain ⟨h₁, h₂⟩ := resolvent_denominators_pos ha hx hxa hxb hs
    exact mul_ne_zero h₁.ne' h₂.ne'
  unfold resolventKernel
  fun_prop (disch := aesop)

theorem continuousOn_density_resolventKernel {a b r x : ℝ}
    (ha : 0 < a) (hr : r ∈ Ioo 0 2) (hx : 0 < x)
    (hxa : x < a ^ 2) (hxb : b ^ 2 * x < 1) :
    ContinuousOn (fun s => branchDensity a b r s * resolventKernel s x) (Icc a b) :=
  (continuous_branchDensity a b r ⟨hr.1, by linarith [hr.2]⟩).continuousOn.mul
    (continuousOn_resolventKernel_in_s ha hx hxa hxb)

theorem hasDerivAt_resolventIntegral {a b r x : ℝ}
    (ha : 0 < a) (hab : a < b) (hr : r ∈ Ioo 0 2)
    (hx : x ∈ resolventDomain a b) :
    HasDerivAt (resolventIntegral a b r)
      (∫ s in a..b, branchDensity a b r s * resolventSlope s x) x := by
  have hb : 0 < b := ha.trans hab
  obtain ⟨hx0, hxa, hxb⟩ := (resolventDomain_iff hb).mp hx
  let M := min (a ^ 2) (1 / b ^ 2)
  let l := x / 2
  let u := (x + M) / 2
  have hxM : x < M := hx.2
  have hlu : x ∈ Ioo l u := by dsimp [l, u]; constructor <;> linarith
  have hdom : ∀ y ∈ Icc l u, y ∈ resolventDomain a b := by
    intro y hy
    change 0 < y ∧ y < M
    change x / 2 ≤ y ∧ y ≤ (x + M) / 2 at hy
    constructor <;> linarith only [hy.1, hy.2, hx0, hxM]
  have hcontF : ∀ y ∈ Icc l u,
      ContinuousOn (fun s => branchDensity a b r s * resolventKernel s y) (Icc a b) := by
    intro y hy
    obtain ⟨hy0, hya, hyb⟩ := (resolventDomain_iff hb).mp (hdom y hy)
    exact continuousOn_density_resolventKernel ha hr hy0 hya hyb
  have hcontF' : ContinuousOn
      (fun p : ℝ × ℝ => branchDensity a b r p.2 * resolventSlope p.2 p.1)
      (Icc l u ×ˢ Icc a b) := by
    apply ((continuous_branchDensity a b r ⟨hr.1, by linarith [hr.2]⟩).comp continuous_snd).continuousOn.mul
    unfold resolventSlope
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro p hp
      obtain ⟨hy0, hya, hyb⟩ := (resolventDomain_iff hb).mp (hdom p.1 hp.1)
      obtain ⟨h₁, h₂⟩ := resolvent_denominators_pos ha hy0 hya hyb hp.2
      exact mul_ne_zero (pow_ne_zero _ h₁.ne') (pow_ne_zero _ h₂.ne')
  exact hasDerivAt_integral_of_compact_rectangle hab.le hlu hcontF hcontF'
    (fun y hy s hs => by
      obtain ⟨hy0, hya, hyb⟩ := (resolventDomain_iff hb).mp (hdom y hy)
      obtain ⟨h₁, h₂⟩ := resolvent_denominators_pos ha hy0 hya hyb hs
      exact (hasDerivAt_resolventKernel s y (ha.trans_le hs.1).ne' h₁.ne' h₂.ne').const_mul _)

theorem strictAntiOn_resolventIntegral {a b r : ℝ}
    (ha : 0 < a) (hab : a < b) (hab1 : a * b < 1) (hr : r ∈ Ioo 0 2) :
    StrictAntiOn (resolventIntegral a b r) (resolventDomain a b) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo _ _)
    (fun x hx => (hasDerivAt_resolventIntegral ha hab hr hx).continuousAt.continuousWithinAt)
  intro x hx
  have hx' : x ∈ resolventDomain a b := interior_subset hx
  rw [(hasDerivAt_resolventIntegral ha hab hr hx').deriv]
  obtain ⟨hx0, hxa, hxb⟩ := (resolventDomain_iff (ha.trans hab)).mp hx'
  exact integral_resolventSlope_neg ha hab hab1 hr hx0 hxa hxb

theorem scale_square_mem_resolventDomain {a b z : ℝ}
    (ha : 0 < a) (hab : a < b) (hz : ScaleDomain a b z) :
    z ^ 2 ∈ resolventDomain a b := by
  apply (resolventDomain_iff (ha.trans hab)).mpr
  refine ⟨sq_pos_of_ne_zero hz.1.ne', (sq_lt_sq₀ hz.1.le ha.le).mpr hz.2.1, ?_⟩
  have hprod : 0 < b * z := mul_pos (ha.trans hab) hz.1
  have hsq : (b * z) ^ 2 < 1 :=
    (sq_lt_one_iff_abs_lt_one (b * z)).mpr (by rw [abs_of_pos hprod]; exact hz.2.2)
  simpa only [mul_pow] using hsq

theorem integral_kernel_difference {a b r z y : ℝ}
    (ha : 0 < a) (hab : a < b) (hr : r ∈ Ioo 0 2)
    (hz : z ∈ resolventDomain a b) (hy : y ∈ resolventDomain a b) :
    (∫ u in a..b, branchDensity a b r u * (resolventKernel u z - resolventKernel u y)) =
      resolventIntegral a b r z - resolventIntegral a b r y := by
  obtain ⟨hz0, hza, hzb⟩ := (resolventDomain_iff (ha.trans hab)).mp hz
  obtain ⟨hy0, hya, hyb⟩ := (resolventDomain_iff (ha.trans hab)).mp hy
  unfold resolventIntegral
  simp_rw [mul_sub]
  exact intervalIntegral.integral_sub
    ((continuousOn_density_resolventKernel ha hr hz0 hza hzb).intervalIntegrable_of_Icc hab.le)
    ((continuousOn_density_resolventKernel ha hr hy0 hya hyb).intervalIntegrable_of_Icc hab.le)

/-- Strict increase in the exponential scale for the entire lower-weight range. -/
theorem quarticTransform_lt_of_r_lt_one {a b r z y : ℝ}
    (ha : 0 < a) (hab : a < b) (hab1 : a * b < 1) (hr : r ∈ Ioo 0 1)
    (hz : ScaleDomain a b z) (hy : ScaleDomain a b y) (hzy : z < y) :
    quarticTransform z (branchPower a b r) < quarticTransform y (branchPower a b r) := by
  have hr2 : r ∈ Ioo 0 2 := ⟨hr.1, hr.2.trans (by norm_num)⟩
  have hz2 := scale_square_mem_resolventDomain ha hab hz
  have hy2 := scale_square_mem_resolventDomain ha hab hy
  have hsq : z ^ 2 < y ^ 2 := (sq_lt_sq₀ hz.1.le hy.1.le).mpr hzy
  have hdiff := strictAntiOn_resolventIntegral ha hab hab1 hr2 hz2 hy2 hsq
  apply sub_neg.mp
  rw [quarticTransform_difference_stieltjes01 ha hab hr hz hy,
    integral_kernel_difference ha hab hr2 hz2 hy2]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos (inv_pos.mpr (stieltjesNormalizer_pos hr)))
    (sub_pos.mpr hdiff)

/-- Strict decrease in the exponential scale for the entire upper-weight range. -/
theorem quarticTransform_lt_of_one_lt_r {a b r z y : ℝ}
    (ha : 0 < a) (hab : a < b) (hab1 : a * b < 1) (hr : r ∈ Ioo 1 2)
    (hz : ScaleDomain a b z) (hy : ScaleDomain a b y) (hzy : z < y) :
    quarticTransform y (branchPower a b r) < quarticTransform z (branchPower a b r) := by
  have hr2 : r ∈ Ioo 0 2 := ⟨zero_lt_one.trans hr.1, hr.2⟩
  have hz2 := scale_square_mem_resolventDomain ha hab hz
  have hy2 := scale_square_mem_resolventDomain ha hab hy
  have hsq : z ^ 2 < y ^ 2 := (sq_lt_sq₀ hz.1.le hy.1.le).mpr hzy
  have hdiff := strictAntiOn_resolventIntegral ha hab hab1 hr2 hz2 hy2 hsq
  apply sub_pos.mp
  rw [quarticTransform_difference_stieltjes12 ha hab hr hz hy,
    integral_kernel_difference ha hab hr2 hz2 hy2]
  exact mul_pos (inv_pos.mpr (stieltjesNormalizer_pos (by constructor <;> linarith [hr.1, hr.2])))
    (sub_pos.mpr hdiff)

end PaperVerification.Hyperbolic

#print axioms PaperVerification.Hyperbolic.strictAntiOn_resolventIntegral
#print axioms PaperVerification.Hyperbolic.quarticTransform_lt_of_r_lt_one
#print axioms PaperVerification.Hyperbolic.quarticTransform_lt_of_one_lt_r
end
end Source_HyperbolicScale
-- END ORIGINAL PaperVerification.HyperbolicScale


-- BEGIN ORIGINAL PaperVerification.HyperbolicExponential
section Source_HyperbolicExponential

-- original header: module
-- original header: public import PaperVerification.HyperbolicScale
-- original header: public import PaperVerification.HyperbolicTwoPoint
-- original header: @[expose] public section
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
end
end Source_HyperbolicExponential
-- END ORIGINAL PaperVerification.HyperbolicExponential


-- BEGIN ORIGINAL PaperVerification.HyperbolicLargeScale
section Source_HyperbolicLargeScale

-- original header: module
-- original header: public import PaperVerification.HyperbolicExponential
-- original header: public import PaperVerification.HyperbolicDeficits
-- original header: public import Mathlib.Analysis.Calculus.Deriv.Abs
-- original header: public import Mathlib.Analysis.Calculus.Deriv.Slope
-- original header: @[expose] public section
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
end
end Source_HyperbolicLargeScale
-- END ORIGINAL PaperVerification.HyperbolicLargeScale


-- BEGIN ORIGINAL PaperVerification.HyperbolicCompactMinimum
section Source_HyperbolicCompactMinimum

-- original header: module
-- original header: public import PaperVerification.HyperbolicLargeScale
-- original header: public import PaperVerification.HyperbolicBoundaryActual
-- original header: public import Mathlib.Topology.Order.Compact
-- original header: public import Mathlib.Analysis.Calculus.LocalExtr.Basic
-- original header: @[expose] public section
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
end
end Source_HyperbolicCompactMinimum
-- END ORIGINAL PaperVerification.HyperbolicCompactMinimum


-- BEGIN ORIGINAL PaperVerification.GeometricMeanMix
section Source_GeometricMeanMix

-- original header: module
-- original header: public import PaperVerification.GeometricMean
-- original header: public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
-- original header: public import Mathlib.Analysis.SpecialFunctions.Exp
-- original header: public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
-- original header: @[expose] public section
/-! # Geometric means on segments of probability measures

The exact multiplicative segment identity includes zero geometric means, rather
than assuming logarithmic integrability. This is the analytic reason a vanished
sinh term stays zero under every proper variation toward an interior atom.
-/

noncomputable section

namespace PaperVerification.Hyperbolic

open MeasureTheory Set Filter Topology

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [CompactSpace X] [OpensMeasurableSpace X]

/-- Convex combination of two probability measures. -/
def mixProbability (μ ν : ProbabilityMeasure X) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ProbabilityMeasure X :=
  ⟨ENNReal.ofReal (1 - t) • (μ : Measure X) + ENNReal.ofReal t • (ν : Measure X), by
    constructor
    simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add (sub_nonneg.mpr ht.2) ht.1]
    norm_num⟩

@[simp] theorem coe_mixProbability (μ ν : ProbabilityMeasure X) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    ((mixProbability μ ν t ht) : Measure X) =
      ENNReal.ofReal (1 - t) • (μ : Measure X) + ENNReal.ofReal t • (ν : Measure X) := rfl

theorem integral_mixProbability (f : C(X, ℝ)) (μ ν : ProbabilityMeasure X) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ x, f x ∂(mixProbability μ ν t ht)) =
      (1 - t) * (∫ x, f x ∂μ) + t * (∫ x, f x ∂ν) := by
  rw [coe_mixProbability, integral_add_measure
    ((integrable_continuousMap f μ).smul_measure ENNReal.ofReal_ne_top)
    ((integrable_continuousMap f ν).smul_measure ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure, ENNReal.toReal_ofReal (sub_nonneg.mpr ht.2),
    ENNReal.toReal_ofReal ht.1, smul_eq_mul]

theorem truncatedGeometricMoment_mix (k : ℝ) (f : C(X, ℝ))
    (μ ν : ProbabilityMeasure X) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    truncatedGeometricMoment k f (mixProbability μ ν t ht) n =
      truncatedGeometricMoment k f μ n ^ (1 - t) *
        truncatedGeometricMoment k f ν n ^ t := by
  unfold truncatedGeometricMoment
  rw [integral_mixProbability]
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.rpow_def_of_pos (Real.exp_pos _)]
  rw [Real.log_exp, Real.log_exp, ← Real.exp_add]
  congr 1
  ring

/-- Exact segment identity, valid at the endpoints and for zero geometric means. -/
theorem geometricMoment_mix (k : ℝ) (hk : 0 ≤ k) (f : C(X, ℝ))
    (μ ν : ProbabilityMeasure X) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    geometricMoment k f (mixProbability μ ν t ht) =
      geometricMoment k f μ ^ (1 - t) * geometricMoment k f ν ^ t := by
  have h₁ := ((tendsto_truncatedGeometricMoment k hk f μ).rpow_const
    (Or.inr (sub_nonneg.mpr ht.2))).mul
    ((tendsto_truncatedGeometricMoment k hk f ν).rpow_const (Or.inr ht.1))
  have h₂ := tendsto_truncatedGeometricMoment k hk f (mixProbability μ ν t ht)
  have heq : truncatedGeometricMoment k f (mixProbability μ ν t ht) =
      fun n => truncatedGeometricMoment k f μ n ^ (1 - t) *
        truncatedGeometricMoment k f ν n ^ t :=
    funext (truncatedGeometricMoment_mix k f μ ν t ht)
  rw [heq] at h₂
  exact tendsto_nhds_unique h₂ h₁

/-- A zero geometric moment remains zero under every proper convex variation. -/
theorem geometricMoment_mix_eq_zero (k : ℝ) (hk : 0 ≤ k) (f : C(X, ℝ))
    (μ ν : ProbabilityMeasure X) (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1)
    (hzero : geometricMoment k f μ = 0) :
    geometricMoment k f (mixProbability μ ν t ⟨ht.1, ht.2.le⟩) = 0 := by
  rw [geometricMoment_mix k hk f μ ν t ⟨ht.1, ht.2.le⟩, hzero,
    Real.zero_rpow (sub_pos.mpr ht.2).ne', zero_mul]

/-- A Dirac measure as a probability measure. -/
def diracProbability (p : X) : ProbabilityMeasure X := ⟨Measure.dirac p, inferInstance⟩

@[simp] theorem coe_diracProbability (p : X) :
    ((diracProbability p) : Measure X) = Measure.dirac p := rfl

theorem geometricMoment_dirac [MeasurableSingletonClass X]
    (k : ℝ) (hk : 0 ≤ k) (f : C(X, ℝ)) (p : X) (hfp : 0 ≤ f p) :
    geometricMoment k f (diracProbability p) = f p ^ k := by
  have hcut : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hm : Tendsto (fun n : ℕ => max (Real.exp (-(n : ℝ))) (f p)) atTop (𝓝 (f p)) := by
    simpa only [max_eq_right hfp] using hcut.max
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => f p) atTop (𝓝 (f p)))
  have hpow := hm.rpow_const (Or.inr hk)
  have hseq := tendsto_truncatedGeometricMoment k hk f (diracProbability p)
  have heq : truncatedGeometricMoment k f (diracProbability p) =
      fun n : ℕ => max (Real.exp (-(n : ℝ))) (f p) ^ k := by
    funext n
    simp only [truncatedGeometricMoment, coe_diracProbability, integral_dirac, truncatedLog,
      ContinuousMap.coe_mk]
    rw [Real.rpow_def_of_pos ((Real.exp_pos _).trans_le (le_max_left _ _))]
    congr 1
    ring
  rw [heq] at hseq
  exact tendsto_nhds_unique hseq hpow

/-- A smooth extension around t=0 of a proper geometric-mean segment. The zero
case is identically zero; it is not replaced by exp(log 0). -/
def momentSegment (a b t : ℝ) : ℝ :=
  if a = 0 then 0 else Real.exp ((1 - t) * Real.log a + t * Real.log b)

theorem momentSegment_eq_rpow (a b t : ℝ) (ha : 0 ≤ a) (hb : 0 < b) (ht : t < 1) :
    momentSegment a b t = a ^ (1 - t) * b ^ t := by
  by_cases haz : a = 0
  · simp only [momentSegment, haz, ↓reduceIte,
      Real.zero_rpow (sub_pos.mpr ht).ne', zero_mul]
  · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm haz)
    rw [momentSegment, if_neg haz, Real.rpow_def_of_pos hap, Real.rpow_def_of_pos hb,
      ← Real.exp_add]
    congr 1
    ring

@[simp] theorem momentSegment_zero (a b : ℝ) (ha : 0 ≤ a) : momentSegment a b 0 = a := by
  by_cases haz : a = 0
  · simp [momentSegment, haz]
  · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm haz)
    simp [momentSegment, haz, Real.exp_log hap]

theorem hasDerivAt_momentSegment_zero (a b : ℝ) (ha : 0 ≤ a) :
    HasDerivAt (momentSegment a b) (a * (Real.log b - Real.log a)) 0 := by
  by_cases haz : a = 0
  · subst a
    have hfun : momentSegment 0 b = fun _ : ℝ => 0 := by
      funext t
      exact if_pos rfl
    rw [hfun, zero_mul]
    exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm haz)
    have hd := ((((hasDerivAt_id (0 : ℝ)).const_sub 1).mul_const (Real.log a)).add
      ((hasDerivAt_id (0 : ℝ)).mul_const (Real.log b))).exp
    convert hd using 1 <;> (try funext t) <;>
      (try simp only [momentSegment, if_neg haz, sub_zero, one_mul, zero_mul,
        add_zero, Real.exp_log hap, Pi.add_apply, Pi.sub_apply, Pi.mul_apply,
        Function.comp_apply, id_eq]) <;> ring

theorem geometricMoment_mix_eq_momentSegment (k : ℝ) (hk : 0 ≤ k) (f : C(X, ℝ))
    (μ ν : ProbabilityMeasure X) (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1)
    (hν : 0 < geometricMoment k f ν) :
    geometricMoment k f (mixProbability μ ν t ⟨ht.1, ht.2.le⟩) =
      momentSegment (geometricMoment k f μ) (geometricMoment k f ν) t := by
  rw [momentSegment_eq_rpow _ _ _ (geometricMoment_nonneg k f μ) hν ht.2]
  exact geometricMoment_mix k hk f μ ν t ⟨ht.1, ht.2.le⟩

/-- The segment formula also includes a vanishing atom when the original
geometric moment is already zero. -/
theorem momentSegment_eq_rpow_of_admissible (a b t : ℝ) (ha : 0 ≤ a)
    (hb : a = 0 ∨ 0 < b) (ht : t < 1) :
    momentSegment a b t = a ^ (1 - t) * b ^ t := by
  rcases hb with haz | hb
  · simp only [momentSegment, haz, ↓reduceIte,
      Real.zero_rpow (sub_pos.mpr ht).ne', zero_mul]
  · exact momentSegment_eq_rpow a b t ha hb ht

theorem geometricMoment_mix_eq_momentSegment_of_admissible
    (k : ℝ) (hk : 0 ≤ k) (f : C(X, ℝ))
    (μ ν : ProbabilityMeasure X) (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1)
    (hν : geometricMoment k f μ = 0 ∨ 0 < geometricMoment k f ν) :
    geometricMoment k f (mixProbability μ ν t ⟨ht.1, ht.2.le⟩) =
      momentSegment (geometricMoment k f μ) (geometricMoment k f ν) t := by
  rw [momentSegment_eq_rpow_of_admissible _ _ _ (geometricMoment_nonneg k f μ) hν ht.2]
  exact geometricMoment_mix k hk f μ ν t ⟨ht.1, ht.2.le⟩

end PaperVerification.Hyperbolic

#print axioms PaperVerification.Hyperbolic.geometricMoment_mix
#print axioms PaperVerification.Hyperbolic.geometricMoment_mix_eq_zero
#print axioms PaperVerification.Hyperbolic.geometricMoment_dirac
#print axioms PaperVerification.Hyperbolic.hasDerivAt_momentSegment_zero
end
end Source_GeometricMeanMix
-- END ORIGINAL PaperVerification.GeometricMeanMix


-- BEGIN ORIGINAL PaperVerification.HyperbolicMeasure
section Source_HyperbolicMeasure

-- original header: module
-- original header: public import PaperVerification.GeometricMean
-- original header: public import PaperVerification.HyperbolicLocalization
-- original header: public import Mathlib.MeasureTheory.Measure.Prokhorov
-- original header: @[expose] public section
/-! # Weak compactness and existence for the hyperbolic variational problem

The probability measures are unrestricted Borel probability measures on the full
closed interval. The sinh terms use the truncation-defined geometric moment, so
endpoint atoms and divergent negative logarithmic integrals remain included.
-/

noncomputable section

namespace PaperVerification.Hyperbolic

open Real Set MeasureTheory Filter Topology

abbrev Interval (R : ℝ) := Set.Icc (0 : ℝ) R

def intervalCosh (R : ℝ) : C(Interval R, ℝ) :=
  ⟨fun p => Real.cosh (p : ℝ), Real.continuous_cosh.comp continuous_subtype_val⟩

def intervalReflectedCosh (R : ℝ) : C(Interval R, ℝ) :=
  ⟨fun p => Real.cosh (R - (p : ℝ)),
    Real.continuous_cosh.comp (continuous_const.sub continuous_subtype_val)⟩

def intervalSinh (R : ℝ) : C(Interval R, ℝ) :=
  ⟨fun p => Real.sinh (p : ℝ), Real.continuous_sinh.comp continuous_subtype_val⟩

def intervalReflectedSinh (R : ℝ) : C(Interval R, ℝ) :=
  ⟨fun p => Real.sinh (R - (p : ℝ)),
    Real.continuous_sinh.comp (continuous_const.sub continuous_subtype_val)⟩

def intervalCenteredLogCosh (R : ℝ) : C(Interval R, ℝ) :=
  ⟨fun p => Real.log (Real.cosh (2 * (p : ℝ) - R)),
    (Real.continuous_cosh.comp
      ((continuous_const.mul continuous_subtype_val).sub continuous_const)).log
        (fun p => (Real.cosh_pos _).ne')⟩

def hyperbolicNumerator (R : ℝ) (μ : ProbabilityMeasure (Interval R)) : ℝ :=
  geometricMoment 4 (intervalCosh R) μ + geometricMoment 4 (intervalReflectedCosh R) μ -
    geometricMoment 4 (intervalSinh R) μ - geometricMoment 4 (intervalReflectedSinh R) μ

/-- J in Section 4.1, the logarithm of the ratio in Theorem 3.1. -/
def hyperbolicObjective (R : ℝ) (μ : ProbabilityMeasure (Interval R)) : ℝ :=
  Real.log (hyperbolicNumerator R μ) - Real.log (2 * Real.cosh R) -
    ∫ p, intervalCenteredLogCosh R p ∂μ

theorem strictMono_real_tanh : StrictMono Real.tanh := by
  apply strictMono_of_deriv_pos
  intro p
  rw [(hasDerivAt_tanh p).deriv]
  linarith only [Real.tanh_sq_lt_one p]

theorem tanh_pos {R : ℝ} (hR : 0 < R) : 0 < Real.tanh R := by
  simpa only [Real.tanh_zero] using strictMono_real_tanh hR

theorem sinh_le_tanh_mul_cosh {R p : ℝ} (hp : p ≤ R) :
    Real.sinh p ≤ Real.tanh R * Real.cosh p := by
  have ht := strictMono_real_tanh.monotone hp
  rw [Real.tanh_eq_sinh_div_cosh p] at ht
  exact (div_le_iff₀ (Real.cosh_pos p)).mp ht

theorem geometricMoment_sinh_le (R : ℝ) (hR : 0 < R)
    (μ : ProbabilityMeasure (Interval R)) :
    geometricMoment 4 (intervalSinh R) μ ≤
      Real.tanh R ^ 4 * geometricMoment 4 (intervalCosh R) μ := by
  let scaled : C(Interval R, ℝ) :=
    ⟨fun p => Real.tanh R * intervalCosh R p, continuous_const.mul (intervalCosh R).continuous⟩
  have hmono := geometricMoment_mono 4 (by norm_num)
    (f := intervalSinh R) (g := scaled)
    (fun p => sinh_le_tanh_mul_cosh p.property.2) μ
  have hscale := geometricMoment_nat_const_mul_of_lower_bound 4 (intervalCosh R) μ
    (tanh_pos hR) (by norm_num : (0 : ℝ) < 1) (fun p => Real.one_le_cosh (p : ℝ))
  exact hmono.trans_eq hscale

theorem geometricMoment_reflectedSinh_le (R : ℝ) (hR : 0 < R)
    (μ : ProbabilityMeasure (Interval R)) :
    geometricMoment 4 (intervalReflectedSinh R) μ ≤
      Real.tanh R ^ 4 * geometricMoment 4 (intervalReflectedCosh R) μ := by
  let scaled : C(Interval R, ℝ) :=
    ⟨fun p => Real.tanh R * intervalReflectedCosh R p,
      continuous_const.mul (intervalReflectedCosh R).continuous⟩
  have hmono := geometricMoment_mono 4 (by norm_num)
    (f := intervalReflectedSinh R) (g := scaled)
    (fun p => sinh_le_tanh_mul_cosh (by linarith [p.property.1])) μ
  have hscale := geometricMoment_nat_const_mul_of_lower_bound 4 (intervalReflectedCosh R) μ
    (tanh_pos hR) (by norm_num : (0 : ℝ) < 1) (fun p => Real.one_le_cosh (R - (p : ℝ)))
  exact hmono.trans_eq hscale

theorem tanh_fourth_lt_one (R : ℝ) : Real.tanh R ^ 4 < 1 := by
  have h₁ := Real.tanh_sq_lt_one R
  have h₂ : 0 < (1 - Real.tanh R ^ 2) * (1 + Real.tanh R ^ 2) :=
    mul_pos (by linarith) (by nlinarith only [sq_nonneg (Real.tanh R)])
  nlinarith only [h₂]

/-- Uniform positive lower bound from Lemma 4.1, including the zero sinh means. -/
theorem hyperbolicNumerator_lower_bound (R : ℝ) (hR : 0 < R)
    (μ : ProbabilityMeasure (Interval R)) :
    2 * (1 - Real.tanh R ^ 4) ≤ hyperbolicNumerator R μ := by
  have hA := one_le_geometricMoment_of_one_le 4 (by norm_num) (intervalCosh R) μ
    (fun p => Real.one_le_cosh (p : ℝ))
  have hC := one_le_geometricMoment_of_one_le 4 (by norm_num) (intervalReflectedCosh R) μ
    (fun p => Real.one_le_cosh (R - (p : ℝ)))
  have hB := geometricMoment_sinh_le R hR μ
  have hD := geometricMoment_reflectedSinh_le R hR μ
  have hq : 0 ≤ 1 - Real.tanh R ^ 4 := (sub_pos.mpr (tanh_fourth_lt_one R)).le
  have h₁ := mul_nonneg hq (sub_nonneg.mpr hA)
  have h₂ := mul_nonneg hq (sub_nonneg.mpr hC)
  unfold hyperbolicNumerator
  nlinarith only [hB, hD, h₁, h₂]

theorem hyperbolicNumerator_pos (R : ℝ) (hR : 0 < R)
    (μ : ProbabilityMeasure (Interval R)) : 0 < hyperbolicNumerator R μ :=
  (mul_pos (by norm_num) (sub_pos.mpr (tanh_fourth_lt_one R))).trans_le
    (hyperbolicNumerator_lower_bound R hR μ)

theorem lowerSemicontinuous_hyperbolicNumerator (R : ℝ) :
    LowerSemicontinuous (hyperbolicNumerator R) := by
  have hA := continuous_geometricMoment_of_lower_bound 4 (by norm_num) (intervalCosh R)
    (by norm_num : (0 : ℝ) < 1) (fun p => Real.one_le_cosh (p : ℝ))
  have hC := continuous_geometricMoment_of_lower_bound 4 (by norm_num) (intervalReflectedCosh R)
    (by norm_num : (0 : ℝ) < 1) (fun p => Real.one_le_cosh (R - (p : ℝ)))
  have hB := upperSemicontinuous_geometricMoment 4 (intervalSinh R)
  have hD := upperSemicontinuous_geometricMoment 4 (intervalReflectedSinh R)
  have h := ((hA.lowerSemicontinuous.add hC.lowerSemicontinuous).add hB.neg).add hD.neg
  change LowerSemicontinuous (fun μ => geometricMoment 4 (intervalCosh R) μ +
    geometricMoment 4 (intervalReflectedCosh R) μ - geometricMoment 4 (intervalSinh R) μ -
      geometricMoment 4 (intervalReflectedSinh R) μ)
  have heq : (fun μ : ProbabilityMeasure (Interval R) =>
      geometricMoment 4 (intervalCosh R) μ + geometricMoment 4 (intervalReflectedCosh R) μ -
        geometricMoment 4 (intervalSinh R) μ - geometricMoment 4 (intervalReflectedSinh R) μ) =
      (fun μ => geometricMoment 4 (intervalCosh R) μ + geometricMoment 4 (intervalReflectedCosh R) μ +
        -(geometricMoment 4 (intervalSinh R) μ) + -(geometricMoment 4 (intervalReflectedSinh R) μ)) := by
    funext μ
    ring
  rw [heq]
  exact h

theorem lowerSemicontinuous_hyperbolicObjective (R : ℝ) (hR : 0 < R) :
    LowerSemicontinuous (hyperbolicObjective R) := by
  let δ : ℝ := 2 * (1 - Real.tanh R ^ 4)
  have hδ : 0 < δ := mul_pos (by norm_num) (sub_pos.mpr (tanh_fourth_lt_one R))
  have hclip : Continuous (fun t : ℝ => Real.log (max δ t)) :=
    (continuous_const.max continuous_id).log (fun t => (hδ.trans_le (le_max_left δ t)).ne')
  have hmono : Monotone (fun t : ℝ => Real.log (max δ t)) := by
    intro x y hxy
    exact Real.log_le_log (hδ.trans_le (le_max_left δ x)) (max_le_max_left δ hxy)
  have hlog := hclip.comp_lowerSemicontinuous
    (lowerSemicontinuous_hyperbolicNumerator R) hmono
  have heq : (fun t : ℝ => Real.log (max δ t)) ∘ hyperbolicNumerator R =
      fun μ => Real.log (hyperbolicNumerator R μ) := by
    funext μ
    dsimp only [Function.comp_apply]
    rw [max_eq_right (hyperbolicNumerator_lower_bound R hR μ)]
  rw [heq] at hlog
  have hrest : Continuous (fun μ : ProbabilityMeasure (Interval R) =>
      -Real.log (2 * Real.cosh R) - ∫ p, intervalCenteredLogCosh R p ∂μ) :=
    continuous_const.sub (ProbabilityMeasure.continuous_integral_continuousMap (intervalCenteredLogCosh R))
  convert hlog.add hrest.lowerSemicontinuous using 1
  ext μ
  unfold hyperbolicObjective
  ring

/-- The arbitrary-measure objective attains a global minimum on the full
probability-measure space. No finite-support assumption is made here. -/
theorem exists_minimizer_hyperbolicObjective (R : ℝ) (hR : 0 < R) :
    ∃ μ : ProbabilityMeasure (Interval R),
      ∀ ν : ProbabilityMeasure (Interval R), hyperbolicObjective R μ ≤ hyperbolicObjective R ν := by
  let p₀ : Interval R := ⟨0, ⟨le_rfl, hR.le⟩⟩
  let μ₀ : ProbabilityMeasure (Interval R) := ⟨Measure.dirac p₀, inferInstance⟩
  obtain ⟨μ, hμ, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn
    ⟨μ₀, mem_univ μ₀⟩ isCompact_univ
    ((lowerSemicontinuous_hyperbolicObjective R hR).lowerSemicontinuousOn univ)
  exact ⟨μ, fun ν => (isMinOn_iff.mp hmin) ν (mem_univ ν)⟩

end PaperVerification.Hyperbolic

#print axioms PaperVerification.Hyperbolic.hyperbolicNumerator_lower_bound
#print axioms PaperVerification.Hyperbolic.exists_minimizer_hyperbolicObjective
end
end Source_HyperbolicMeasure
-- END ORIGINAL PaperVerification.HyperbolicMeasure


-- BEGIN ORIGINAL PaperVerification.HyperbolicFirstVariation
section Source_HyperbolicFirstVariation

-- original header: module
-- original header: public import PaperVerification.HyperbolicMeasure
-- original header: public import PaperVerification.GeometricMeanMix
-- original header: public import PaperVerification.GeometricMeanLog
-- original header: public import Mathlib.Analysis.Calculus.Deriv.Slope
-- original header: @[expose] public section
/-! # First variation for arbitrary probability measures

All four geometric moments are varied exactly. Vanishing moments remain zero;
they are not differentiated through the undefined extended logarithm. The
resulting entropy identity proves that the lower first-variation bound is the
actual probability average of the potential.
-/

noncomputable section

namespace PaperVerification.Hyperbolic

open Real Set MeasureTheory Filter Topology

/-- The potential g associated to an arbitrary probability measure. -/
def measurePotential (R : ℝ) (μ : ProbabilityMeasure (Interval R)) (p : ℝ) : ℝ :=
  variationPotential R (geometricMoment 4 (intervalCosh R) μ)
    (geometricMoment 4 (intervalReflectedCosh R) μ)
    (geometricMoment 4 (intervalSinh R) μ)
    (geometricMoment 4 (intervalReflectedSinh R) μ) (hyperbolicNumerator R μ) p

/-- Its finite logarithmic-entropy average. -/
def potentialEntropy (R : ℝ) (μ : ProbabilityMeasure (Interval R)) : ℝ :=
  (geometricMoment 4 (intervalCosh R) μ * Real.log (geometricMoment 4 (intervalCosh R) μ) +
    geometricMoment 4 (intervalReflectedCosh R) μ * Real.log (geometricMoment 4 (intervalReflectedCosh R) μ) -
    geometricMoment 4 (intervalSinh R) μ * Real.log (geometricMoment 4 (intervalSinh R) μ) -
    geometricMoment 4 (intervalReflectedSinh R) μ * Real.log (geometricMoment 4 (intervalReflectedSinh R) μ)) /
      hyperbolicNumerator R μ - ∫ p, intervalCenteredLogCosh R p ∂μ

/-- Points where the first-variation potential has a finite endpoint limit. -/
def AdmissiblePoint (R : ℝ) (μ : ProbabilityMeasure (Interval R)) (p : Interval R) : Prop :=
  (geometricMoment 4 (intervalSinh R) μ = 0 ∨ 0 < (p : ℝ)) ∧
    (geometricMoment 4 (intervalReflectedSinh R) μ = 0 ∨ (p : ℝ) < R)

theorem intervalSinh_nonneg (R : ℝ) (p : Interval R) : 0 ≤ intervalSinh R p :=
  Real.sinh_nonneg_iff.mpr p.property.1

theorem intervalReflectedSinh_nonneg (R : ℝ) (p : Interval R) :
    0 ≤ intervalReflectedSinh R p :=
  Real.sinh_nonneg_iff.mpr (sub_nonneg.mpr p.property.2)

theorem ae_admissiblePoint (R : ℝ) (μ : ProbabilityMeasure (Interval R)) :
    ∀ᵐ p ∂(μ : Measure (Interval R)), AdmissiblePoint R μ p := by
  have hB : ∀ᵐ (p : Interval R) ∂(μ : Measure (Interval R)),
      geometricMoment 4 (intervalSinh R) μ = 0 ∨ 0 < (p : ℝ) := by
    by_cases hz : geometricMoment 4 (intervalSinh R) μ = 0
    · exact Filter.Eventually.of_forall (fun _ => Or.inl hz)
    · have hp : 0 < geometricMoment 4 (intervalSinh R) μ :=
        lt_of_le_of_ne (geometricMoment_nonneg 4 (intervalSinh R) μ) (Ne.symm hz)
      have hae := (ae_pos_and_integrable_log_of_geometricMoment_pos 4 (by norm_num)
        (intervalSinh R) μ (intervalSinh_nonneg R) hp).1
      filter_upwards [hae] with p hp
      exact Or.inr (Real.sinh_pos_iff.mp hp)
  have hD : ∀ᵐ (p : Interval R) ∂(μ : Measure (Interval R)),
      geometricMoment 4 (intervalReflectedSinh R) μ = 0 ∨ (p : ℝ) < R := by
    by_cases hz : geometricMoment 4 (intervalReflectedSinh R) μ = 0
    · exact Filter.Eventually.of_forall (fun _ => Or.inl hz)
    · have hp : 0 < geometricMoment 4 (intervalReflectedSinh R) μ :=
        lt_of_le_of_ne (geometricMoment_nonneg 4 (intervalReflectedSinh R) μ) (Ne.symm hz)
      have hae := (ae_pos_and_integrable_log_of_geometricMoment_pos 4 (by norm_num)
        (intervalReflectedSinh R) μ (intervalReflectedSinh_nonneg R) hp).1
      filter_upwards [hae] with p hp
      exact Or.inr (sub_pos.mp (Real.sinh_pos_iff.mp hp))
  exact hB.and hD

theorem integrable_measurePotential (R : ℝ) (μ : ProbabilityMeasure (Interval R)) :
    Integrable (fun p : Interval R => measurePotential R μ p) (μ : Measure (Interval R)) := by
  have hA := integrable_geometricMoment_mul_log 4 (by norm_num) (intervalCosh R) μ
    (fun p => (Real.cosh_pos (p : ℝ)).le)
  have hC := integrable_geometricMoment_mul_log 4 (by norm_num) (intervalReflectedCosh R) μ
    (fun p => (Real.cosh_pos (R - (p : ℝ))).le)
  have hB := integrable_geometricMoment_mul_log 4 (by norm_num) (intervalSinh R) μ (intervalSinh_nonneg R)
  have hD := integrable_geometricMoment_mul_log 4 (by norm_num) (intervalReflectedSinh R) μ
    (intervalReflectedSinh_nonneg R)
  exact ((((hA.add hC).sub hB).sub hD).const_mul (4 / hyperbolicNumerator R μ)).sub
    (integrable_continuousMap (intervalCenteredLogCosh R) μ)

theorem integral_measurePotential (R : ℝ) (hR : 0 < R)
    (μ : ProbabilityMeasure (Interval R)) :
    (∫ p : Interval R, measurePotential R μ p ∂μ) = potentialEntropy R μ := by
  have hAint := integrable_geometricMoment_mul_log 4 (by norm_num) (intervalCosh R) μ
    (fun p => (Real.cosh_pos (p : ℝ)).le)
  have hCint := integrable_geometricMoment_mul_log 4 (by norm_num) (intervalReflectedCosh R) μ
    (fun p => (Real.cosh_pos (R - (p : ℝ))).le)
  have hBint := integrable_geometricMoment_mul_log 4 (by norm_num) (intervalSinh R) μ (intervalSinh_nonneg R)
  have hDint := integrable_geometricMoment_mul_log 4 (by norm_num) (intervalReflectedSinh R) μ
    (intervalReflectedSinh_nonneg R)
  have hA := geometricMoment_mul_log_integral 4 (by norm_num) (intervalCosh R) μ
    (fun p => (Real.cosh_pos (p : ℝ)).le)
  have hC := geometricMoment_mul_log_integral 4 (by norm_num) (intervalReflectedCosh R) μ
    (fun p => (Real.cosh_pos (R - (p : ℝ))).le)
  have hB := geometricMoment_mul_log_integral 4 (by norm_num) (intervalSinh R) μ (intervalSinh_nonneg R)
  have hD := geometricMoment_mul_log_integral 4 (by norm_num) (intervalReflectedSinh R) μ
    (intervalReflectedSinh_nonneg R)
  have hACint : Integrable (fun p : Interval R =>
      geometricMoment 4 (intervalCosh R) μ * Real.log (intervalCosh R p) +
        geometricMoment 4 (intervalReflectedCosh R) μ * Real.log (intervalReflectedCosh R p))
      (μ : Measure (Interval R)) := hAint.add hCint
  have hACBint : Integrable (fun p : Interval R =>
      geometricMoment 4 (intervalCosh R) μ * Real.log (intervalCosh R p) +
        geometricMoment 4 (intervalReflectedCosh R) μ * Real.log (intervalReflectedCosh R p) -
        geometricMoment 4 (intervalSinh R) μ * Real.log (intervalSinh R p))
      (μ : Measure (Interval R)) := hACint.sub hBint
  have hACBDint : Integrable (fun p : Interval R =>
      geometricMoment 4 (intervalCosh R) μ * Real.log (intervalCosh R p) +
        geometricMoment 4 (intervalReflectedCosh R) μ * Real.log (intervalReflectedCosh R p) -
        geometricMoment 4 (intervalSinh R) μ * Real.log (intervalSinh R p) -
        geometricMoment 4 (intervalReflectedSinh R) μ * Real.log (intervalReflectedSinh R p))
      (μ : Measure (Interval R)) := hACBint.sub hDint
  change (∫ p, (4 / hyperbolicNumerator R μ) *
    (geometricMoment 4 (intervalCosh R) μ * Real.log (intervalCosh R p) +
    geometricMoment 4 (intervalReflectedCosh R) μ * Real.log (intervalReflectedCosh R p) -
    geometricMoment 4 (intervalSinh R) μ * Real.log (intervalSinh R p) -
    geometricMoment 4 (intervalReflectedSinh R) μ * Real.log (intervalReflectedSinh R p)) -
    intervalCenteredLogCosh R p ∂μ) = _
  rw [integral_sub (hACBDint.const_mul (4 / hyperbolicNumerator R μ))
      (integrable_continuousMap (intervalCenteredLogCosh R) μ), integral_const_mul,
    integral_sub hACBint hDint,
    integral_sub hACint hBint, integral_add hAint hCint]
  unfold potentialEntropy
  field_simp [(hyperbolicNumerator_pos R hR μ).ne']
  linarith only [hA, hC, hB, hD]

/-- A smooth real extension of the objective along variations toward p. -/
def objectiveSegment (R : ℝ) (μ : ProbabilityMeasure (Interval R)) (p : Interval R) (t : ℝ) : ℝ :=
  Real.log
    (momentSegment (geometricMoment 4 (intervalCosh R) μ) (intervalCosh R p ^ 4) t +
      momentSegment (geometricMoment 4 (intervalReflectedCosh R) μ) (intervalReflectedCosh R p ^ 4) t -
      momentSegment (geometricMoment 4 (intervalSinh R) μ) (intervalSinh R p ^ 4) t -
      momentSegment (geometricMoment 4 (intervalReflectedSinh R) μ) (intervalReflectedSinh R p ^ 4) t) -
    Real.log (2 * Real.cosh R) -
      ((1 - t) * (∫ q, intervalCenteredLogCosh R q ∂μ) + t * intervalCenteredLogCosh R p)

@[simp] theorem objectiveSegment_zero (R : ℝ) (μ : ProbabilityMeasure (Interval R)) (p : Interval R) :
    objectiveSegment R μ p 0 = hyperbolicObjective R μ := by
  simp only [objectiveSegment, momentSegment_zero _ _ (geometricMoment_nonneg 4 (intervalCosh R) μ),
    momentSegment_zero _ _ (geometricMoment_nonneg 4 (intervalReflectedCosh R) μ),
    momentSegment_zero _ _ (geometricMoment_nonneg 4 (intervalSinh R) μ),
    momentSegment_zero _ _ (geometricMoment_nonneg 4 (intervalReflectedSinh R) μ),
    sub_zero, one_mul, zero_mul, add_zero, hyperbolicObjective, hyperbolicNumerator]

theorem objectiveSegment_eq_mixture (R : ℝ) (μ : ProbabilityMeasure (Interval R))
    (p : Interval R) (hp : AdmissiblePoint R μ p) (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
    objectiveSegment R μ p t =
      hyperbolicObjective R (mixProbability μ (diracProbability p) t ⟨ht.1, ht.2.le⟩) := by
  have hA : geometricMoment 4 (intervalCosh R) (diracProbability p) = intervalCosh R p ^ 4 := by
    simpa only [Real.rpow_ofNat] using geometricMoment_dirac 4 (by norm_num)
      (intervalCosh R) p (Real.cosh_pos (p : ℝ)).le
  have hC : geometricMoment 4 (intervalReflectedCosh R) (diracProbability p) =
      intervalReflectedCosh R p ^ 4 := by
    simpa only [Real.rpow_ofNat] using geometricMoment_dirac 4 (by norm_num)
      (intervalReflectedCosh R) p (Real.cosh_pos (R - (p : ℝ))).le
  have hB : geometricMoment 4 (intervalSinh R) (diracProbability p) = intervalSinh R p ^ 4 := by
    simpa only [Real.rpow_ofNat] using geometricMoment_dirac 4 (by norm_num)
      (intervalSinh R) p (intervalSinh_nonneg R p)
  have hD : geometricMoment 4 (intervalReflectedSinh R) (diracProbability p) =
      intervalReflectedSinh R p ^ 4 := by
    simpa only [Real.rpow_ofNat] using geometricMoment_dirac 4 (by norm_num)
      (intervalReflectedSinh R) p (intervalReflectedSinh_nonneg R p)
  have hAp : geometricMoment 4 (intervalCosh R) μ = 0 ∨
      0 < geometricMoment 4 (intervalCosh R) (diracProbability p) :=
    Or.inr (by rw [hA]; exact pow_pos (Real.cosh_pos (p : ℝ)) 4)
  have hCp : geometricMoment 4 (intervalReflectedCosh R) μ = 0 ∨
      0 < geometricMoment 4 (intervalReflectedCosh R) (diracProbability p) :=
    Or.inr (by rw [hC]; exact pow_pos (Real.cosh_pos (R - (p : ℝ))) 4)
  have hBp : geometricMoment 4 (intervalSinh R) μ = 0 ∨
      0 < geometricMoment 4 (intervalSinh R) (diracProbability p) := by
    rcases hp.1 with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [hB]; exact pow_pos (Real.sinh_pos_iff.mpr h) 4)
  have hDp : geometricMoment 4 (intervalReflectedSinh R) μ = 0 ∨
      0 < geometricMoment 4 (intervalReflectedSinh R) (diracProbability p) := by
    rcases hp.2 with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [hD]; exact pow_pos (Real.sinh_pos_iff.mpr (sub_pos.mpr h)) 4)
  have hmixIntegral :
      (∫ q, intervalCenteredLogCosh R q ∂(mixProbability μ (diracProbability p) t ⟨ht.1, ht.2.le⟩)) =
        (1 - t) * (∫ q, intervalCenteredLogCosh R q ∂μ) + t * intervalCenteredLogCosh R p := by
    simpa only [coe_diracProbability, integral_dirac] using
      integral_mixProbability (intervalCenteredLogCosh R) μ (diracProbability p) t ⟨ht.1, ht.2.le⟩
  unfold objectiveSegment hyperbolicObjective hyperbolicNumerator
  rw [geometricMoment_mix_eq_momentSegment_of_admissible 4 (by norm_num) (intervalCosh R) μ
      (diracProbability p) t ht hAp,
    geometricMoment_mix_eq_momentSegment_of_admissible 4 (by norm_num) (intervalReflectedCosh R) μ
      (diracProbability p) t ht hCp,
    geometricMoment_mix_eq_momentSegment_of_admissible 4 (by norm_num) (intervalSinh R) μ
      (diracProbability p) t ht hBp,
    geometricMoment_mix_eq_momentSegment_of_admissible 4 (by norm_num) (intervalReflectedSinh R) μ
      (diracProbability p) t ht hDp, hA, hC, hB, hD, hmixIntegral]

/-- Exact first variation, valid at finite endpoints as well as in the interior. -/
theorem hasDerivAt_objectiveSegment_zero (R : ℝ) (hR : 0 < R)
    (μ : ProbabilityMeasure (Interval R)) (p : Interval R) :
    HasDerivAt (objectiveSegment R μ p)
      (measurePotential R μ p - potentialEntropy R μ) 0 := by
  have hA := hasDerivAt_momentSegment_zero
    (geometricMoment 4 (intervalCosh R) μ) (intervalCosh R p ^ 4)
    (geometricMoment_nonneg 4 (intervalCosh R) μ)
  have hC := hasDerivAt_momentSegment_zero
    (geometricMoment 4 (intervalReflectedCosh R) μ) (intervalReflectedCosh R p ^ 4)
    (geometricMoment_nonneg 4 (intervalReflectedCosh R) μ)
  have hB := hasDerivAt_momentSegment_zero
    (geometricMoment 4 (intervalSinh R) μ) (intervalSinh R p ^ 4)
    (geometricMoment_nonneg 4 (intervalSinh R) μ)
  have hD := hasDerivAt_momentSegment_zero
    (geometricMoment 4 (intervalReflectedSinh R) μ) (intervalReflectedSinh R p ^ 4)
    (geometricMoment_nonneg 4 (intervalReflectedSinh R) μ)
  have hnum := ((hA.add hC).sub hB).sub hD
  have hnum0 :
    momentSegment (geometricMoment 4 (intervalCosh R) μ) (intervalCosh R p ^ 4) 0 +
      momentSegment (geometricMoment 4 (intervalReflectedCosh R) μ) (intervalReflectedCosh R p ^ 4) 0 -
      momentSegment (geometricMoment 4 (intervalSinh R) μ) (intervalSinh R p ^ 4) 0 -
      momentSegment (geometricMoment 4 (intervalReflectedSinh R) μ) (intervalReflectedSinh R p ^ 4) 0 =
      hyperbolicNumerator R μ := by
    simp only [momentSegment_zero _ _ (geometricMoment_nonneg 4 (intervalCosh R) μ),
      momentSegment_zero _ _ (geometricMoment_nonneg 4 (intervalReflectedCosh R) μ),
      momentSegment_zero _ _ (geometricMoment_nonneg 4 (intervalSinh R) μ),
      momentSegment_zero _ _ (geometricMoment_nonneg 4 (intervalReflectedSinh R) μ), hyperbolicNumerator]
  have hnum_ne := hnum0.trans_ne (hyperbolicNumerator_pos R hR μ).ne'
  have hlast := (((hasDerivAt_id (0 : ℝ)).const_sub 1).mul_const
    (∫ q, intervalCenteredLogCosh R q ∂μ)).add
    ((hasDerivAt_id (0 : ℝ)).mul_const (intervalCenteredLogCosh R p))
  convert ((hnum.log hnum_ne).sub_const (Real.log (2 * Real.cosh R))).sub hlast using 1
  · rfl
  · simp only [Pi.add_apply, Pi.sub_apply]
    rw [hnum0]
    simp only [measurePotential, variationPotential, potentialEntropy,
      intervalCosh, intervalReflectedCosh, intervalSinh, intervalReflectedSinh,
      intervalCenteredLogCosh, ContinuousMap.coe_mk, Real.log_pow]
    field_simp [(hyperbolicNumerator_pos R hR μ).ne'] <;> ring

/-- The elementary right-derivative condition, stated without a tangent-cone assumption. -/
theorem derivative_nonneg_of_right_minimum {f : ℝ → ℝ} {d : ℝ}
    (hd : HasDerivAt f d 0) (hmin : ∀ t ∈ Ico (0 : ℝ) 1, f 0 ≤ f t) : 0 ≤ d := by
  apply ge_of_tendsto hd.tendsto_slope_zero_right
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with t ht0 ht1
  simp only [zero_add, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr ht0.le) (sub_nonneg.mpr (hmin t ⟨ht0.le, ht1⟩))

/-- The potential at every finite admissible point is at least its true average. -/
theorem potentialEntropy_le_measurePotential_of_minimizer
    (R : ℝ) (hR : 0 < R) (μ : ProbabilityMeasure (Interval R))
    (hmin : ∀ ν : ProbabilityMeasure (Interval R), hyperbolicObjective R μ ≤ hyperbolicObjective R ν)
    (p : Interval R) (hp : AdmissiblePoint R μ p) :
    potentialEntropy R μ ≤ measurePotential R μ p := by
  apply sub_nonneg.mp
  apply derivative_nonneg_of_right_minimum (hasDerivAt_objectiveSegment_zero R hR μ p)
  intro t ht
  rw [objectiveSegment_zero, objectiveSegment_eq_mixture R μ p hp t ht]
  exact hmin _

/-- A minimizing measure concentrates almost everywhere on the minimum-potential level. -/
theorem ae_measurePotential_eq_entropy_of_minimizer
    (R : ℝ) (hR : 0 < R) (μ : ProbabilityMeasure (Interval R))
    (hmin : ∀ ν : ProbabilityMeasure (Interval R), hyperbolicObjective R μ ≤ hyperbolicObjective R ν) :
    ∀ᵐ (p : Interval R) ∂(μ : Measure (Interval R)), measurePotential R μ p = potentialEntropy R μ := by
  have hnonneg : 0 ≤ᵐ[(μ : Measure (Interval R))]
      fun p : Interval R => measurePotential R μ p - potentialEntropy R μ := by
    filter_upwards [ae_admissiblePoint R μ] with p hp
    exact sub_nonneg.mpr (potentialEntropy_le_measurePotential_of_minimizer R hR μ hmin p hp)
  have hint := (integrable_measurePotential R μ).sub (integrable_const (potentialEntropy R μ))
  have hzero : (∫ p : Interval R, measurePotential R μ p - potentialEntropy R μ ∂μ) = 0 := by
    rw [integral_sub (integrable_measurePotential R μ) (integrable_const _),
      integral_measurePotential R hR μ]
    simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
      one_smul, sub_self]
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnonneg hint).mp hzero
  filter_upwards [hae] with p hp
  exact sub_eq_zero.mp hp

end PaperVerification.Hyperbolic

#print axioms PaperVerification.Hyperbolic.integral_measurePotential
#print axioms PaperVerification.Hyperbolic.potentialEntropy_le_measurePotential_of_minimizer
#print axioms PaperVerification.Hyperbolic.ae_measurePotential_eq_entropy_of_minimizer
end
end Source_HyperbolicFirstVariation
-- END ORIGINAL PaperVerification.HyperbolicFirstVariation


-- BEGIN ORIGINAL PaperVerification.MinimaLocalization
section Source_MinimaLocalization

-- original header: module
-- original header: public import Mathlib.Analysis.Convex.Deriv
-- original header: public import Mathlib.Analysis.Calculus.Deriv.Basic
-- original header: public import Mathlib.Tactic.Linarith
-- original header: public import Mathlib.Tactic.NormNum
-- original header: @[expose] public section
/-! # A rigorous support-localization calculus lemma

A function whose second derivative is a positive multiple of a strictly convex
function has at most two global minima. This supplies the sign-shape argument
used in Lemma 4.1 without assuming that the zero set of the second derivative
has already been classified. Endpoints are included; differentiability is
required only in the interior.
-/

noncomputable section

namespace PaperVerification.Hyperbolic

open Set

/-- Equal minimal endpoint values force a point of negative normalized curvature.
Strict convexity rules out the only alternative, a constant function on the interval. -/
theorem exists_negative_normalized_curvature
    {f h w : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b))
    (hf' : DifferentiableOn ℝ f (Ioo a b))
    (hf'' : DifferentiableOn ℝ (deriv f) (Ioo a b))
    (hw : ∀ x ∈ Ioo a b, 0 < w x)
    (heq : ∀ x ∈ Ioo a b, deriv (deriv f) x = w x * h x)
    (hh : StrictConvexOn ℝ (Ioo a b) h)
    (hmin : ∀ x ∈ Icc a b, f a ≤ f x) (hend : f b = f a) :
    ∃ x ∈ Ioo a b, h x < 0 := by
  by_contra hn
  have hnonneg : ∀ x ∈ Ioo a b, 0 ≤ h x := by
    intro x hx
    exact le_of_not_gt (fun hneg => hn ⟨x, hx, hneg⟩)
  have hconv : ConvexOn ℝ (Icc a b) f := by
    apply convexOn_of_deriv2_nonneg (convex_Icc a b) hf
    · simpa only [interior_Icc] using hf'
    · simpa only [interior_Icc] using hf''
    · intro x hx
      rw [interior_Icc] at hx
      change 0 ≤ deriv (deriv f) x
      rw [heq x hx]
      exact mul_nonneg (hw x hx).le (hnonneg x hx)
  have hconst : (Ioo a b).EqOn f (fun _ => f a) := by
    intro x hx
    apply le_antisymm
    · have hxseg : x ∈ segment ℝ a b := by
        rw [segment_eq_Icc hab.le]
        exact ⟨hx.1.le, hx.2.le⟩
      have hu := hconv.le_on_segment (left_mem_Icc.mpr hab.le)
        (right_mem_Icc.mpr hab.le) hxseg
      simpa only [hend, max_self] using hu
    · exact hmin x ⟨hx.1.le, hx.2.le⟩
  have hzero : ∀ x ∈ Ioo a b, h x = 0 := by
    intro x hx
    have hd := ((hconst.deriv isOpen_Ioo).deriv isOpen_Ioo) hx
    simp only [deriv_const', deriv_const] at hd
    rw [heq x hx] at hd
    exact (mul_eq_zero.mp hd).resolve_left (hw x hx).ne'
  let u : ℝ := (3 * a + b) / 4
  let v : ℝ := (a + 3 * b) / 4
  have hu : u ∈ Ioo a b := by dsimp [u]; constructor <;> linarith
  have hv : v ∈ Ioo a b := by dsimp [v]; constructor <;> linarith
  have huv : u ≠ v := by dsimp [u, v]; linarith
  have hm : (1 / 2 : ℝ) * u + (1 / 2 : ℝ) * v ∈ Ioo a b := by
    dsimp [u, v]
    constructor <;> linarith
  have hs := hh.2 hu hv huv (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  simp only [smul_eq_mul] at hs
  rw [hzero u hu, hzero v hv, hzero _ hm] at hs
  norm_num at hs

/-- There cannot be three ordered global minima. This version allows the outer
minima to be endpoints, which is essential for measures charging 0 or R. -/
theorem no_three_global_minima_of_strictConvex_normalized_curvature
    {f h w : ℝ → ℝ} {a b c : ℝ} (hab : a < b) (hbc : b < c)
    (hf : ContinuousOn f (Icc a c))
    (hf' : DifferentiableOn ℝ f (Ioo a c))
    (hf'' : DifferentiableOn ℝ (deriv f) (Ioo a c))
    (hw : ∀ x ∈ Ioo a c, 0 < w x)
    (heq : ∀ x ∈ Ioo a c, deriv (deriv f) x = w x * h x)
    (hh : StrictConvexOn ℝ (Ioo a c) h)
    (hmin : ∀ x ∈ Icc a c, f a ≤ f x)
    (hb : f b = f a) (hc : f c = f a) : False := by
  have hsub₁ : Ioo a b ⊆ Ioo a c := by
    intro x hx
    exact ⟨hx.1, hx.2.trans hbc⟩
  have hsub₂ : Ioo b c ⊆ Ioo a c := by
    intro x hx
    exact ⟨hab.trans hx.1, hx.2⟩
  obtain ⟨u, hu, hune⟩ := exists_negative_normalized_curvature hab
    (hf.mono (by intro x hx; exact ⟨hx.1, hx.2.trans hbc.le⟩))
    (hf'.mono hsub₁) (hf''.mono hsub₁)
    (fun x hx => hw x (hsub₁ hx)) (fun x hx => heq x (hsub₁ hx))
    (hh.subset hsub₁ (convex_Ioo a b))
    (fun x hx => hmin x ⟨hx.1, hx.2.trans hbc.le⟩) hb
  obtain ⟨v, hv, hvne⟩ := exists_negative_normalized_curvature hbc
    (hf.mono (by intro x hx; exact ⟨hab.le.trans hx.1, hx.2⟩))
    (hf'.mono hsub₂) (hf''.mono hsub₂)
    (fun x hx => hw x (hsub₂ hx)) (fun x hx => heq x (hsub₂ hx))
    (hh.subset hsub₂ (convex_Ioo b c))
    (fun x hx => by rw [hb]; exact hmin x ⟨hab.le.trans hx.1, hx.2⟩)
    (hc.trans hb.symm)
  have huv : u < v := hu.2.trans hv.1
  have huac : u ∈ Ioo a c := hsub₁ hu
  have hvac : v ∈ Ioo a c := hsub₂ hv
  have hsub : Icc u v ⊆ Icc a c := by
    intro x hx
    exact ⟨huac.1.le.trans hx.1, hx.2.trans hvac.2.le⟩
  have hnegative : ∀ x ∈ Ioo u v, h x < 0 := by
    intro x hx
    have hxseg : x ∈ segment ℝ u v := by
      rw [segment_eq_Icc huv.le]
      exact ⟨hx.1.le, hx.2.le⟩
    exact (hh.convexOn.le_on_segment huac hvac hxseg).trans_lt (max_lt hune hvne)
  have hconc : StrictConcaveOn ℝ (Icc u v) f := by
    apply strictConcaveOn_of_deriv2_neg (convex_Icc u v) (hf.mono hsub)
    intro x hx
    rw [interior_Icc] at hx
    have hxall : x ∈ Ioo a c := ⟨huac.1.trans hx.1, hx.2.trans hvac.2⟩
    change deriv (deriv f) x < 0
    rw [heq x hxall]
    exact mul_neg_of_pos_of_neg (hw x hxall) (hnegative x hx)
  have hbseg : b ∈ openSegment ℝ u v := by
    rw [openSegment_eq_Ioo huv]
    exact ⟨hu.2, hv.1⟩
  have hstrict := hconc.lt_on_openSegment (left_mem_Icc.mpr huv.le)
    (right_mem_Icc.mpr huv.le) huv.ne hbseg
  have hbu : f b ≤ f u := by rw [hb]; exact hmin u ⟨huac.1.le, huac.2.le⟩
  have hbv : f b ≤ f v := by rw [hb]; exact hmin v ⟨hvac.1.le, hvac.2.le⟩
  exact (not_lt_of_ge (le_min hbu hbv)) hstrict

end PaperVerification.Hyperbolic

#print axioms PaperVerification.Hyperbolic.no_three_global_minima_of_strictConvex_normalized_curvature
end
end Source_MinimaLocalization
-- END ORIGINAL PaperVerification.MinimaLocalization


-- BEGIN ORIGINAL PaperVerification.HyperbolicPotential
section Source_HyperbolicPotential

-- original header: module
-- original header: public import PaperVerification.HyperbolicLocalization
-- original header: public import PaperVerification.MinimaLocalization
-- original header: @[expose] public section
/-! # Localization for the exact hyperbolic first-variation potential

This file applies the general calculus lemma to the potential of Lemma 4.1,
including the finite endpoint cases B=0 and D=0. The measure-theoretic first
variation is separate; this file does not assume its conclusion as a theorem
about the Gaussian or hyperbolic inequality.
-/

noncomputable section

namespace PaperVerification.Hyperbolic

open Real Set

/-- Continuity on every interval on which the endpoint logarithms have finite
limits. A zero coefficient is handled before evaluating continuity of log sinh. -/
theorem continuousOn_variationPotential
    (R A C B D F a c : ℝ)
    (hB : B = 0 ∨ 0 < a) (hD : D = 0 ∨ c < R) :
    ContinuousOn (variationPotential R A C B D F) (Icc a c) := by
  have hcosh : Continuous (fun t : ℝ => Real.log (Real.cosh t)) :=
    Real.continuous_cosh.log (fun t => (Real.cosh_pos t).ne')
  have hcoshR : Continuous (fun t : ℝ => Real.log (Real.cosh (R - t))) :=
    hcosh.comp (continuous_const.sub continuous_id)
  have hcoshV : Continuous (fun t : ℝ => Real.log (Real.cosh (2 * t - R))) :=
    hcosh.comp ((continuous_const.mul continuous_id).sub continuous_const)
  have hBcont : ContinuousOn (fun t : ℝ => B * Real.log (Real.sinh t)) (Icc a c) := by
    rcases hB with rfl | ha
    · simpa only [zero_mul] using
        (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ))).continuousOn
    · exact continuousOn_const.mul (Real.continuous_sinh.continuousOn.log
        (fun t ht => Real.sinh_ne_zero.mpr (ne_of_gt (ha.trans_le ht.1))))
  have hDcont : ContinuousOn (fun t : ℝ => D * Real.log (Real.sinh (R - t))) (Icc a c) := by
    rcases hD with rfl | hc
    · simpa only [zero_mul] using
        (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ))).continuousOn
    · exact continuousOn_const.mul
        ((Real.continuous_sinh.comp (continuous_const.sub continuous_id)).continuousOn.log
          (fun t ht => Real.sinh_ne_zero.mpr (ne_of_gt (sub_pos.mpr (ht.2.trans_lt hc)))))
  exact (continuousOn_const.mul
    ((((continuousOn_const.mul hcosh.continuousOn).add
      (continuousOn_const.mul hcoshR.continuousOn)).sub hBcont).sub hDcont)).sub
        hcoshV.continuousOn

theorem differentiableOn_variationPotential (R A C B D F : ℝ) :
    DifferentiableOn ℝ (variationPotential R A C B D F) (Ioo 0 R) :=
  fun p hp => (hasDerivAt_variationPotential R A C B D F p hp).differentiableAt.differentiableWithinAt

theorem differentiableOn_deriv_variationPotential (R A C B D F : ℝ) :
    DifferentiableOn ℝ (deriv (variationPotential R A C B D F)) (Ioo 0 R) := by
  have hdiff : DifferentiableOn ℝ (variationDerivative R A C B D F) (Ioo 0 R) :=
    fun p hp => (hasDerivAt_variationDerivative R A C B D F p hp).differentiableAt.differentiableWithinAt
  apply hdiff.congr
  intro p hp
  exact (hasDerivAt_variationPotential R A C B D F p hp).deriv

/-- The actual potential in Lemma 4.1 cannot have three global minima. The
admissibility alternatives explicitly retain all finite endpoint cases. -/
theorem no_three_minima_variationPotential
    (R A C B D F a b c : ℝ)
    (hA : 0 < A) (hC : 0 < C) (hB : 0 ≤ B) (hD : 0 ≤ D) (hF : 0 < F)
    (ha : 0 ≤ a) (hc : c ≤ R) (hab : a < b) (hbc : b < c)
    (hBa : B = 0 ∨ 0 < a) (hDc : D = 0 ∨ c < R)
    (hmin : ∀ x ∈ Icc a c,
      variationPotential R A C B D F a ≤ variationPotential R A C B D F x)
    (hb : variationPotential R A C B D F b = variationPotential R A C B D F a)
    (hend : variationPotential R A C B D F c = variationPotential R A C B D F a) :
    False := by
  have hsub : Ioo a c ⊆ Ioo 0 R := by
    intro x hx
    exact ⟨ha.trans_lt hx.1, hx.2.trans_le hc⟩
  apply no_three_global_minima_of_strictConvex_normalized_curvature
    (f := variationPotential R A C B D F)
    (h := curvatureModel R A C B D F)
    (w := fun p => 4 / Real.cosh (2 * p - R) ^ 2)
    hab hbc (continuousOn_variationPotential R A C B D F a c hBa hDc)
    ((differentiableOn_variationPotential R A C B D F).mono hsub)
    ((differentiableOn_deriv_variationPotential R A C B D F).mono hsub)
    (fun p hp => div_pos (by norm_num) (pow_pos (Real.cosh_pos _) 2))
    (fun p hp => (deriv2_variationPotential R A C B D F p (hsub hp)).trans
      (variationSecondDerivative_eq_curvatureModel R A C B D F p hF.ne' (hsub hp)))
    ((strictConvexOn_curvatureModel R A C B D F hA hC hB hD hF).subset hsub
      (convex_Ioo a c)) hmin hb hend

end PaperVerification.Hyperbolic

#print axioms PaperVerification.Hyperbolic.no_three_minima_variationPotential
end
end Source_HyperbolicPotential
-- END ORIGINAL PaperVerification.HyperbolicPotential


-- BEGIN ORIGINAL PaperVerification.HyperbolicSupport
section Source_HyperbolicSupport

-- original header: module
-- original header: public import PaperVerification.HyperbolicFirstVariation
-- original header: public import PaperVerification.HyperbolicPotential
-- original header: public import Mathlib.MeasureTheory.Measure.Support
-- original header: public import Mathlib.MeasureTheory.Measure.Dirac.Basic
-- original header: @[expose] public section
/-! # Full support localization for minimizers

The exponential of minus the potential extends continuously across the singular
endpoints as a product of nonnegative real powers. This proves the support
statement, including accumulation at endpoints of measure zero, rather than
only an almost-everywhere statement.
-/

noncomputable section

namespace PaperVerification.Hyperbolic

open Real Set MeasureTheory Filter Topology

/-- Continuous exponential transform of the potential, with its correct zero
values at endpoints where the potential tends to positive infinity. -/
def potentialKernel (R A C B D F p : ℝ) : ℝ :=
  Real.cosh (2 * p - R) * Real.cosh p ^ (-(4 / F * A)) *
    Real.cosh (R - p) ^ (-(4 / F * C)) * Real.sinh p ^ (4 / F * B) *
      Real.sinh (R - p) ^ (4 / F * D)

theorem continuous_potentialKernel (R A C B D F : ℝ)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hF : 0 < F) :
    Continuous (potentialKernel R A C B D F) := by
  have hscale : 0 ≤ 4 / F := (div_pos (by norm_num) hF).le
  exact ((((Real.continuous_cosh.comp ((continuous_const.mul continuous_id).sub continuous_const)).mul
    (Real.continuous_cosh.rpow_const (fun p => Or.inl (Real.cosh_pos p).ne'))).mul
    ((Real.continuous_cosh.comp (continuous_const.sub continuous_id)).rpow_const
      (fun p => Or.inl (Real.cosh_pos (R - p)).ne'))).mul
    (Real.continuous_sinh.rpow_const (fun _ => Or.inr (mul_nonneg hscale hB)))).mul
    ((Real.continuous_sinh.comp (continuous_const.sub continuous_id)).rpow_const
      (fun _ => Or.inr (mul_nonneg hscale hD)))

private theorem rpow_eq_exp_log_mul_of_admissible (x k : ℝ) (h : 0 < x ∨ k = 0) :
    x ^ k = Real.exp (Real.log x * k) := by
  rcases h with h | rfl
  · exact Real.rpow_def_of_pos h _
  · simp only [Real.rpow_zero, mul_zero, Real.exp_zero]

theorem potentialKernel_eq_exp_neg (R A C B D F p : ℝ)
    (hB : B = 0 ∨ 0 < p) (hD : D = 0 ∨ p < R) :
    potentialKernel R A C B D F p = Real.exp (-variationPotential R A C B D F p) := by
  have hb : 0 < Real.sinh p ∨ 4 / F * B = 0 := by
    rcases hB with h | h
    · exact Or.inr (by rw [h, mul_zero])
    · exact Or.inl (Real.sinh_pos_iff.mpr h)
  have hd : 0 < Real.sinh (R - p) ∨ 4 / F * D = 0 := by
    rcases hD with h | h
    · exact Or.inr (by rw [h, mul_zero])
    · exact Or.inl (Real.sinh_pos_iff.mpr (sub_pos.mpr h))
  unfold potentialKernel
  rw [Real.rpow_def_of_pos (Real.cosh_pos p), Real.rpow_def_of_pos (Real.cosh_pos (R - p)),
    rpow_eq_exp_log_mul_of_admissible _ _ hb, rpow_eq_exp_log_mul_of_admissible _ _ hd]
  nth_rw 1 [← Real.exp_log (Real.cosh_pos (2 * p - R))]
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  unfold variationPotential
  ring

theorem admissible_of_potentialKernel_pos (R A C B D F : ℝ) (p : Interval R)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hF : 0 < F)
    (hK : 0 < potentialKernel R A C B D F p) :
    (B = 0 ∨ 0 < (p : ℝ)) ∧ (D = 0 ∨ (p : ℝ) < R) := by
  constructor
  · by_cases hz : B = 0
    · exact Or.inl hz
    · right
      by_contra hp
      have hp0 : (p : ℝ) = 0 := le_antisymm (le_of_not_gt hp) p.property.1
      have hb : 0 < 4 / F * B :=
        mul_pos (div_pos (by norm_num) hF) (lt_of_le_of_ne hB (Ne.symm hz))
      simp only [potentialKernel, hp0, Real.sinh_zero, Real.zero_rpow hb.ne', mul_zero,
        zero_mul] at hK
      exact lt_irrefl _ hK
  · by_cases hz : D = 0
    · exact Or.inl hz
    · right
      by_contra hp
      have hpR : (p : ℝ) = R := le_antisymm p.property.2 (le_of_not_gt hp)
      have hd : 0 < 4 / F * D :=
        mul_pos (div_pos (by norm_num) hF) (lt_of_le_of_ne hD (Ne.symm hz))
      simp only [potentialKernel, hpR, sub_self, Real.sinh_zero,
        Real.zero_rpow hd.ne', mul_zero] at hK
      exact lt_irrefl _ hK

def measureKernel (R : ℝ) (μ : ProbabilityMeasure (Interval R)) (p : ℝ) : ℝ :=
  potentialKernel R (geometricMoment 4 (intervalCosh R) μ)
    (geometricMoment 4 (intervalReflectedCosh R) μ)
    (geometricMoment 4 (intervalSinh R) μ)
    (geometricMoment 4 (intervalReflectedSinh R) μ) (hyperbolicNumerator R μ) p

theorem support_admissible_and_potential_eq_entropy
    (R : ℝ) (hR : 0 < R) (μ : ProbabilityMeasure (Interval R))
    (hmin : ∀ ν : ProbabilityMeasure (Interval R), hyperbolicObjective R μ ≤ hyperbolicObjective R ν)
    (p : Interval R) (hp : p ∈ (μ : Measure (Interval R)).support) :
    AdmissiblePoint R μ p ∧ measurePotential R μ p = potentialEntropy R μ := by
  have hcont : Continuous (fun q : Interval R => measureKernel R μ q) :=
    (continuous_potentialKernel R _ _ _ _ _
      (geometricMoment_nonneg 4 (intervalSinh R) μ)
      (geometricMoment_nonneg 4 (intervalReflectedSinh R) μ)
      (hyperbolicNumerator_pos R hR μ)).comp continuous_subtype_val
  have hae : ∀ᵐ (q : Interval R) ∂(μ : Measure (Interval R)),
      measureKernel R μ q = Real.exp (-potentialEntropy R μ) := by
    filter_upwards [ae_admissiblePoint R μ, ae_measurePotential_eq_entropy_of_minimizer R hR μ hmin]
      with q hq hlevel
    have he := potentialKernel_eq_exp_neg R (geometricMoment 4 (intervalCosh R) μ)
      (geometricMoment 4 (intervalReflectedCosh R) μ)
      (geometricMoment 4 (intervalSinh R) μ) (geometricMoment 4 (intervalReflectedSinh R) μ)
      (hyperbolicNumerator R μ) (q : ℝ) hq.1 hq.2
    change measureKernel R μ q = Real.exp (-measurePotential R μ q) at he
    rw [he, hlevel]
  have hclosed : IsClosed {q : Interval R | measureKernel R μ q = Real.exp (-potentialEntropy R μ)} :=
    isClosed_eq hcont continuous_const
  have heq := (Measure.support_subset_of_isClosed hclosed hae) hp
  have hpositive : 0 < measureKernel R μ p := heq.symm ▸ Real.exp_pos _
  have hadm : AdmissiblePoint R μ p :=
    admissible_of_potentialKernel_pos R _ _ _ _ _ p
      (geometricMoment_nonneg 4 (intervalSinh R) μ)
      (geometricMoment_nonneg 4 (intervalReflectedSinh R) μ)
      (hyperbolicNumerator_pos R hR μ) hpositive
  refine ⟨hadm, ?_⟩
  have hexp := (potentialKernel_eq_exp_neg R (geometricMoment 4 (intervalCosh R) μ)
    (geometricMoment 4 (intervalReflectedCosh R) μ)
    (geometricMoment 4 (intervalSinh R) μ) (geometricMoment 4 (intervalReflectedSinh R) μ)
    (hyperbolicNumerator R μ) (p : ℝ) hadm.1 hadm.2).symm.trans heq
  have hneg := Real.exp_injective hexp
  change -measurePotential R μ p = -potentialEntropy R μ at hneg
  linarith

/-- There are no three ordered support points of a minimizing probability measure. -/
theorem no_three_support_points_of_minimizer
    (R : ℝ) (hR : 0 < R) (μ : ProbabilityMeasure (Interval R))
    (hmin : ∀ ν : ProbabilityMeasure (Interval R), hyperbolicObjective R μ ≤ hyperbolicObjective R ν)
    (a b c : Interval R)
    (ha : a ∈ (μ : Measure (Interval R)).support)
    (hb : b ∈ (μ : Measure (Interval R)).support)
    (hc : c ∈ (μ : Measure (Interval R)).support) (hab : a < b) (hbc : b < c) : False := by
  obtain ⟨haadm, halevel⟩ := support_admissible_and_potential_eq_entropy R hR μ hmin a ha
  obtain ⟨hbadm, hblevel⟩ := support_admissible_and_potential_eq_entropy R hR μ hmin b hb
  obtain ⟨hcadm, hclevel⟩ := support_admissible_and_potential_eq_entropy R hR μ hmin c hc
  have hA := one_le_geometricMoment_of_one_le 4 (by norm_num) (intervalCosh R) μ
    (fun p => Real.one_le_cosh (p : ℝ))
  have hC := one_le_geometricMoment_of_one_le 4 (by norm_num) (intervalReflectedCosh R) μ
    (fun p => Real.one_le_cosh (R - (p : ℝ)))
  apply no_three_minima_variationPotential R
    (geometricMoment 4 (intervalCosh R) μ) (geometricMoment 4 (intervalReflectedCosh R) μ)
    (geometricMoment 4 (intervalSinh R) μ) (geometricMoment 4 (intervalReflectedSinh R) μ)
    (hyperbolicNumerator R μ) a b c (by linarith) (by linarith)
    (geometricMoment_nonneg 4 (intervalSinh R) μ)
    (geometricMoment_nonneg 4 (intervalReflectedSinh R) μ)
    (hyperbolicNumerator_pos R hR μ) a.property.1 c.property.2 hab hbc haadm.1 hcadm.2
  · intro x hx
    let q : Interval R := ⟨x, ⟨a.property.1.trans hx.1, hx.2.trans c.property.2⟩⟩
    have hq : AdmissiblePoint R μ q := by
      constructor
      · exact haadm.1.imp id (fun h => h.trans_le hx.1)
      · exact hcadm.2.imp id (fun h => hx.2.trans_lt h)
    change measurePotential R μ a ≤ measurePotential R μ q
    rw [halevel]
    exact potentialEntropy_le_measurePotential_of_minimizer R hR μ hmin q hq
  · exact hblevel.trans halevel.symm
  · exact hclevel.trans halevel.symm

private theorem subset_pair_of_no_three_ordered {α : Type*} [LinearOrder α]
    {s : Set α} (hno : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, a < b → b < c → False)
    {p q : α} (hp : p ∈ s) (hq : q ∈ s) (hpq : p < q) : s ⊆ {p, q} := by
  intro z hz
  by_cases hzp : z = p
  · simp only [hzp, mem_insert_iff, true_or]
  by_cases hzq : z = q
  · simp only [hzq, mem_insert_iff, mem_singleton_iff, or_true]
  by_cases hzp' : z < p
  · exact False.elim (hno z hz p hp q hq hzp' hpq)
  have hpz : p < z := lt_of_le_of_ne (le_of_not_gt hzp') (Ne.symm hzp)
  by_cases hzq' : z < q
  · exact False.elim (hno p hp z hz q hq hpz hzq')
  have hqz : q < z := lt_of_le_of_ne (le_of_not_gt hzq') (Ne.symm hzq)
  exact False.elim (hno p hp q hq z hz hpq hqz)

/-- Lemma 4.1: every global minimizer is supported on at most two points,
with no restriction on the original probability measure. -/
theorem support_subset_pair_of_minimizer
    (R : ℝ) (hR : 0 < R) (μ : ProbabilityMeasure (Interval R))
    (hmin : ∀ ν : ProbabilityMeasure (Interval R), hyperbolicObjective R μ ≤ hyperbolicObjective R ν) :
    ∃ p q : Interval R, (μ : Measure (Interval R)).support ⊆ {p, q} := by
  classical
  let s := (μ : Measure (Interval R)).support
  have hμ : (μ : Measure (Interval R)) ≠ 0 := by
    intro hz
    have hu : (μ : Measure (Interval R)) univ = 1 := measure_univ
    simpa [hz] using hu
  obtain ⟨p, hp⟩ := Measure.nonempty_support hμ
  by_cases hs : s.Subsingleton
  · refine ⟨p, p, ?_⟩
    intro q hq
    have hqp := hs hq hp
    simp only [hqp, mem_insert_iff, true_or]
  · have hex : ∃ q ∈ s, q ≠ p := by
      by_contra hn
      apply hs
      intro x hx y hy
      have hx' : x = p := by by_contra h; exact hn ⟨x, hx, h⟩
      have hy' : y = p := by by_contra h; exact hn ⟨y, hy, h⟩
      exact hx'.trans hy'.symm
    obtain ⟨q, hq, hqp⟩ := hex
    have hno : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, a < b → b < c → False :=
      fun a ha b hb c hc hab hbc => no_three_support_points_of_minimizer R hR μ hmin a b c ha hb hc hab hbc
    rcases lt_or_gt_of_ne hqp with hqp | hpq
    · exact ⟨q, p, subset_pair_of_no_three_ordered hno hq hp hqp⟩
    · exact ⟨p, q, subset_pair_of_no_three_ordered hno hp hq hpq⟩

end PaperVerification.Hyperbolic

#print axioms PaperVerification.Hyperbolic.support_subset_pair_of_minimizer
end
end Source_HyperbolicSupport
-- END ORIGINAL PaperVerification.HyperbolicSupport


-- BEGIN ORIGINAL PaperVerification.HyperbolicAtomic
section Source_HyperbolicAtomic

-- original header: module
-- original header: public import PaperVerification.HyperbolicSupport
-- original header: public import PaperVerification.HyperbolicCompactMinimum
-- original header: public import Mathlib.MeasureTheory.Measure.Dirac.Basic
-- original header: @[expose] public section
/-! # Exact atomic representation and the arbitrary-measure bridge

Support at two points is converted into an equality of Borel probability
measures with explicit real weights.  The geometric moment calculation keeps
zero values and zero weights, and consequently includes endpoint atoms.
-/

noncomputable section

namespace PaperVerification.Hyperbolic

open Real Set MeasureTheory Filter Topology

section MixtureLaws

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [CompactSpace X] [OpensMeasurableSpace X]

@[simp] theorem mixProbability_zero (μ ν : ProbabilityMeasure X) (h : (0 : ℝ) ∈ Icc 0 1) :
    mixProbability μ ν 0 h = μ := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [coe_mixProbability, sub_zero, ENNReal.ofReal_one, ENNReal.ofReal_zero,
    one_smul, zero_smul, add_zero]

@[simp] theorem mixProbability_one (μ ν : ProbabilityMeasure X) (h : (1 : ℝ) ∈ Icc 0 1) :
    mixProbability μ ν 1 h = ν := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [coe_mixProbability, sub_self, ENNReal.ofReal_one, ENNReal.ofReal_zero,
    one_smul, zero_smul, zero_add]

@[simp] theorem mixProbability_same (μ : ProbabilityMeasure X) (t : ℝ) (ht : t ∈ Icc 0 1) :
    mixProbability μ μ t ht = μ := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [coe_mixProbability, ← add_smul, ← ENNReal.ofReal_add (sub_nonneg.mpr ht.2) ht.1]
  simp only [sub_add_cancel, ENNReal.ofReal_one, one_smul]

theorem mixProbability_comm (μ ν : ProbabilityMeasure X) (t : ℝ) (ht : t ∈ Icc 0 1) :
    mixProbability μ ν t ht =
      mixProbability ν μ (1 - t) ⟨sub_nonneg.mpr ht.2, by linarith [ht.1]⟩ := by
  apply ProbabilityMeasure.toMeasure_injective
  erw [coe_mixProbability, coe_mixProbability]
  simp only [sub_sub_cancel, add_comm]

theorem geometricMoment_pair [MeasurableSingletonClass X]
    (k : ℝ) (hk : 0 ≤ k) (f : C(X, ℝ)) (p q : X)
    (hp : 0 ≤ f p) (hq : 0 ≤ f q) (t : ℝ) (ht : t ∈ Icc 0 1) :
    geometricMoment k f (mixProbability (diracProbability p) (diracProbability q) t ht) =
      f p ^ (k * (1 - t)) * f q ^ (k * t) := by
  rw [geometricMoment_mix k hk, geometricMoment_dirac k hk f p hp,
    geometricMoment_dirac k hk f q hq, ← Real.rpow_mul hp, ← Real.rpow_mul hq]

end MixtureLaws

theorem probability_eq_pair_mixture {R : ℝ} (μ : ProbabilityMeasure (Interval R))
    (p q : Interval R) (hs : (μ : Measure (Interval R)).support ⊆ {p, q}) :
    ∃ t : ℝ, ∃ ht : t ∈ Icc 0 1,
      μ = mixProbability (diracProbability p) (diracProbability q) t ht := by
  classical
  have hae : ∀ᵐ x ∂(μ : Measure (Interval R)), x = p ∨ x = q := by
    filter_upwards [(μ : Measure (Interval R)).support_mem_ae] with x hx
    simpa only [mem_insert_iff, mem_singleton_iff] using hs hx
  by_cases hpq : p = q
  · subst q
    have hae' : ∀ᵐ x ∂(μ : Measure (Interval R)), x ∈ ({p} : Finset (Interval R)) := by
      simpa only [or_self, Finset.mem_singleton] using hae
    have hm : (μ : Measure (Interval R)) = (μ : Measure (Interval R)) {p} • Measure.dirac p := by
      simpa only [Finset.sum_singleton] using Measure.ae_mem_finset_iff.mp hae'
    have hmass : (μ : Measure (Interval R)) {p} = 1 := by
      have h := congrArg (fun ν : Measure (Interval R) => ν univ) hm
      simpa only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one] using h.symm
    refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
    erw [mixProbability_zero]
    apply ProbabilityMeasure.toMeasure_injective
    rw [coe_diracProbability, hm, hmass, one_smul]
  · have hm := (Measure.ae_eq_or_eq_iff_eq_dirac_add_dirac hpq).mp hae
    have hpfin : (μ : Measure (Interval R)) {p} ≠ ⊤ := measure_ne_top _ _
    have hqfin : (μ : Measure (Interval R)) {q} ≠ ⊤ := measure_ne_top _ _
    have hmass : (μ : Measure (Interval R)) {p} + (μ : Measure (Interval R)) {q} = 1 := by
      have h := congrArg (fun ν : Measure (Interval R) => ν univ) hm
      simpa only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one] using h.symm
    have hmassR : ((μ : Measure (Interval R)) {p}).toReal + ((μ : Measure (Interval R)) {q}).toReal = 1 := by
      rw [← ENNReal.toReal_add hpfin hqfin, hmass, ENNReal.toReal_one]
    let t := ((μ : Measure (Interval R)) {q}).toReal
    have ht : t ∈ Icc 0 1 := ⟨ENNReal.toReal_nonneg, by
      have hp0 : 0 ≤ ((μ : Measure (Interval R)) {p}).toReal := ENNReal.toReal_nonneg
      dsimp [t]
      linarith⟩
    refine ⟨t, ht, ?_⟩
    apply ProbabilityMeasure.toMeasure_injective
    rw [coe_mixProbability, coe_diracProbability, coe_diracProbability]
    have hq' : ENNReal.ofReal t = (μ : Measure (Interval R)) {q} := ENNReal.ofReal_toReal hqfin
    have hp' : ENNReal.ofReal (1 - t) = (μ : Measure (Interval R)) {p} := by
      have hpt : 1 - t = ((μ : Measure (Interval R)) {p}).toReal := by dsimp [t]; linarith
      rw [hpt, ENNReal.ofReal_toReal hpfin]
    rw [hp', hq']
    exact hm

theorem ordered_pair_mixture_of_minimizer
    (R : ℝ) (hR : 0 < R) (μ : ProbabilityMeasure (Interval R))
    (hmin : ∀ ν : ProbabilityMeasure (Interval R), hyperbolicObjective R μ ≤ hyperbolicObjective R ν) :
    ∃ p q : Interval R, p ≤ q ∧ ∃ t : ℝ, ∃ ht : t ∈ Icc 0 1,
      μ = mixProbability (diracProbability p) (diracProbability q) t ht := by
  obtain ⟨p, q, hs⟩ := support_subset_pair_of_minimizer R hR μ hmin
  rcases le_total p q with hpq | hqp
  · obtain ⟨t, ht, hm⟩ := probability_eq_pair_mixture μ p q hs
    exact ⟨p, q, hpq, t, ht, hm⟩
  · have hs' : (μ : Measure (Interval R)).support ⊆ {q, p} := by simpa only [Set.pair_comm] using hs
    obtain ⟨t, ht, hm⟩ := probability_eq_pair_mixture μ q p hs'
    exact ⟨q, p, hqp, t, ht, hm⟩

theorem hyperbolicNumerator_pair (R : ℝ) (p q : Interval R) (t : ℝ) (ht : t ∈ Icc 0 1) :
    hyperbolicNumerator R (mixProbability (diracProbability p) (diracProbability q) t ht) =
      twoPointNumerator R p q (1 - t) := by
  have hpc : 0 ≤ intervalCosh R p := (Real.cosh_pos _).le
  have hqc : 0 ≤ intervalCosh R q := (Real.cosh_pos _).le
  have hpr : 0 ≤ intervalReflectedCosh R p := (Real.cosh_pos _).le
  have hqr : 0 ≤ intervalReflectedCosh R q := (Real.cosh_pos _).le
  have hps : 0 ≤ intervalSinh R p := Real.sinh_nonneg_iff.mpr p.property.1
  have hqs : 0 ≤ intervalSinh R q := Real.sinh_nonneg_iff.mpr q.property.1
  have hpt : 0 ≤ intervalReflectedSinh R p := Real.sinh_nonneg_iff.mpr (sub_nonneg.mpr p.property.2)
  have hqt : 0 ≤ intervalReflectedSinh R q := Real.sinh_nonneg_iff.mpr (sub_nonneg.mpr q.property.2)
  unfold hyperbolicNumerator
  rw [geometricMoment_pair 4 (by norm_num) _ p q hpc hqc t ht,
    geometricMoment_pair 4 (by norm_num) _ p q hpr hqr t ht,
    geometricMoment_pair 4 (by norm_num) _ p q hps hqs t ht,
    geometricMoment_pair 4 (by norm_num) _ p q hpt hqt t ht]
  simp only [twoPointNumerator, intervalCosh, intervalReflectedCosh, intervalSinh,
    intervalReflectedSinh, ContinuousMap.coe_mk, sub_sub_cancel]

theorem hyperbolicObjective_pair (R : ℝ) (p q : Interval R) (t : ℝ) (ht : t ∈ Icc 0 1) :
    hyperbolicObjective R (mixProbability (diracProbability p) (diracProbability q) t ht) =
      twoPointObjective R p q (1 - t) := by
  unfold hyperbolicObjective
  rw [hyperbolicNumerator_pair, integral_mixProbability]
  simp only [coe_diracProbability, integral_dirac]
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.cosh_pos R).ne']
  unfold twoPointObjective
  simp only [intervalCenteredLogCosh, ContinuousMap.coe_mk, sub_sub_cancel]
  ring

theorem hyperbolicObjective_pair_nonneg (R : ℝ) (p q : Interval R) (hpq : p ≤ q)
    (t : ℝ) (ht : t ∈ Icc 0 1) :
    0 ≤ hyperbolicObjective R (mixProbability (diracProbability p) (diracProbability q) t ht) := by
  have hw : 1 - t ∈ Icc (0 : ℝ) 1 := ⟨sub_nonneg.mpr ht.2, by linarith [ht.1]⟩
  rw [hyperbolicObjective_pair, twoPointObjective_eq_log_ratio p.property q.property hw]
  exact Real.log_nonneg (twoPointRatio_ge_one p.property q.property hpq hw)

def reflectInterval (R : ℝ) (p : Interval R) : Interval R :=
  ⟨R - (p : ℝ), ⟨sub_nonneg.mpr p.property.2, by linarith [p.property.1]⟩⟩

/-- Exactly the equality measures in Theorem 3.1. -/
def HyperbolicEquality (R : ℝ) (μ : ProbabilityMeasure (Interval R)) : Prop :=
  (∃ p : Interval R, μ = diracProbability p) ∨
    ∃ p : Interval R, μ = mixProbability (diracProbability p)
      (diracProbability (reflectInterval R p)) (1 / 2) ⟨by norm_num, by norm_num⟩

theorem hyperbolicObjective_dirac_zero (R : ℝ) (p : Interval R) :
    hyperbolicObjective R (diracProbability p) = 0 := by
  have h := hyperbolicObjective_pair R p p 0 ⟨le_rfl, zero_le_one⟩
  erw [mixProbability_zero] at h
  rw [h, twoPointObjective_eq_log_ratio p.property p.property
    (by norm_num : (1 - (0 : ℝ)) ∈ Icc 0 1), twoPointRatio_same p.property, Real.log_one]

theorem hyperbolicObjective_balanced_zero (R : ℝ) (p : Interval R) :
    hyperbolicObjective R (mixProbability (diracProbability p)
      (diracProbability (reflectInterval R p)) (1 / 2) ⟨by norm_num, by norm_num⟩) = 0 := by
  erw [hyperbolicObjective_pair, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
    twoPointObjective_eq_log_ratio p.property (reflectInterval R p).property
      (by norm_num : (1 / 2 : ℝ) ∈ Icc 0 1)]
  have he : twoPointRatio R p (reflectInterval R p) (1 / 2) = 1 :=
    (twoPointRatio_half_eq_one_iff _ _ _).mpr (Or.inr (by change (p : ℝ) + (R - (p : ℝ)) = R; ring))
  rw [he, Real.log_one]

theorem equality_of_pair_objective_zero (R : ℝ) (p q : Interval R) (hpq : p ≤ q)
    (t : ℝ) (ht : t ∈ Icc 0 1)
    (hzero : hyperbolicObjective R (mixProbability (diracProbability p) (diracProbability q) t ht) = 0) :
    HyperbolicEquality R (mixProbability (diracProbability p) (diracProbability q) t ht) := by
  have hw : 1 - t ∈ Icc (0 : ℝ) 1 := ⟨sub_nonneg.mpr ht.2, by linarith [ht.1]⟩
  rw [hyperbolicObjective_pair, twoPointObjective_eq_log_ratio p.property q.property hw] at hzero
  have heq : twoPointRatio R p q (1 - t) = 1 := by
    have h := congrArg Real.exp hzero
    rwa [Real.exp_log (twoPointRatio_pos p.property q.property hw), Real.exp_zero] at h
  rcases (twoPointRatio_eq_one_iff p.property q.property hpq hw).mp heq with h | h | h | ⟨h, hs⟩
  · have ht1 : t = 1 := by linarith
    subst t
    exact Or.inl ⟨q, mixProbability_one _ _ _⟩
  · have ht0 : t = 0 := by linarith
    subst t
    exact Or.inl ⟨p, mixProbability_zero _ _ _⟩
  · have hpq' : p = q := Subtype.ext h
    subst q
    exact Or.inl ⟨p, mixProbability_same _ _ _⟩
  · have ht' : t = 1 / 2 := by linarith
    have hq' : q = reflectInterval R p := Subtype.ext (by change (q : ℝ) = R - (p : ℝ); linarith)
    subst t
    subst q
    exact Or.inr ⟨p, rfl⟩

end PaperVerification.Hyperbolic

#print axioms PaperVerification.Hyperbolic.ordered_pair_mixture_of_minimizer
#print axioms PaperVerification.Hyperbolic.hyperbolicObjective_pair_nonneg
end
end Source_HyperbolicAtomic
-- END ORIGINAL PaperVerification.HyperbolicAtomic


-- BEGIN ORIGINAL PaperVerification.HyperbolicTheorem
section Source_HyperbolicTheorem

-- original header: module
-- original header: public import PaperVerification.HyperbolicAtomic
-- original header: public import PaperVerification.GeometricMeanExtended
-- original header: @[expose] public section
/-! # The full hyperbolic geometric-mean inequality

Theorem 3.1 is stated for every Borel probability measure on the entire closed
interval.  Geometric means at zero, endpoint atoms, and nonintegrable negative
logarithms are included by the previously verified truncation definition.
The equality condition is exactly a point mass or a balanced reflected pair.
-/

noncomputable section

namespace PaperVerification.Hyperbolic

open Real Set MeasureTheory

def intervalCenteredCosh (R : ℝ) : C(Interval R, ℝ) :=
  ⟨fun p => Real.cosh (2 * (p : ℝ) - R),
    Real.continuous_cosh.comp ((continuous_const.mul continuous_subtype_val).sub continuous_const)⟩

theorem geometricMean_centered_eq_exp_integral (R : ℝ) (μ : ProbabilityMeasure (Interval R)) :
    geometricMean (intervalCenteredCosh R) μ =
      Real.exp (∫ p, intervalCenteredLogCosh R p ∂μ) := by
  unfold geometricMean
  rw [geometricMoment_eq_exp_integral_of_lower_bound 1 zero_le_one _ μ
    (by norm_num : (0 : ℝ) < 1) (fun p => Real.one_le_cosh (2 * (p : ℝ) - R)), one_mul]
  rfl

/-- The unrestricted variational objective is nonnegative. -/
theorem hyperbolicObjective_nonneg (R : ℝ) (hR : 0 < R)
    (μ : ProbabilityMeasure (Interval R)) : 0 ≤ hyperbolicObjective R μ := by
  obtain ⟨ν, hmin⟩ := exists_minimizer_hyperbolicObjective R hR
  obtain ⟨p, q, hpq, t, ht, hν⟩ := ordered_pair_mixture_of_minimizer R hR ν hmin
  have hν0 : 0 ≤ hyperbolicObjective R ν := by
    rw [hν]
    exact hyperbolicObjective_pair_nonneg R p q hpq t ht
  exact hν0.trans (hmin μ)

/-- Equality in the unrestricted variational problem has exactly the two
measure-theoretic forms stated in the paper. -/
theorem hyperbolicObjective_eq_zero_iff_equality (R : ℝ) (hR : 0 < R)
    (μ : ProbabilityMeasure (Interval R)) :
    hyperbolicObjective R μ = 0 ↔ HyperbolicEquality R μ := by
  constructor
  · intro hzero
    have hmin : ∀ ν : ProbabilityMeasure (Interval R), hyperbolicObjective R μ ≤ hyperbolicObjective R ν := by
      intro ν
      rw [hzero]
      exact hyperbolicObjective_nonneg R hR ν
    obtain ⟨p, q, hpq, t, ht, hμ⟩ := ordered_pair_mixture_of_minimizer R hR μ hmin
    rw [hμ] at hzero ⊢
    exact equality_of_pair_objective_zero R p q hpq t ht hzero
  · rintro (⟨p, rfl⟩ | ⟨p, rfl⟩)
    · exact hyperbolicObjective_dirac_zero R p
    · exact hyperbolicObjective_balanced_zero R p

/-- The logarithmic normalization preserves the literal equality statement. -/
theorem hyperbolicObjective_eq_zero_iff (R : ℝ) (hR : 0 < R)
    (μ : ProbabilityMeasure (Interval R)) :
    hyperbolicObjective R μ = 0 ↔
      hyperbolicNumerator R μ = 2 * Real.cosh R * geometricMean (intervalCenteredCosh R) μ := by
  have hK : 0 < 2 * Real.cosh R := mul_pos (by norm_num) (Real.cosh_pos R)
  have hN := hyperbolicNumerator_pos R hR μ
  rw [geometricMean_centered_eq_exp_integral]
  constructor
  · intro hzero
    have hlog : Real.log (hyperbolicNumerator R μ) = Real.log (2 * Real.cosh R) +
        ∫ p, intervalCenteredLogCosh R p ∂μ := by
      unfold hyperbolicObjective at hzero
      linarith
    have h := congrArg Real.exp hlog
    simpa only [Real.exp_log hN, Real.exp_add, Real.exp_log hK] using h
  · intro heq
    unfold hyperbolicObjective
    rw [heq, Real.log_mul hK.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring

/-- Theorem 3.1, in the moment notation used by the theta transfer. -/
theorem hyperbolic_geometric_mean_inequality (R : ℝ) (hR : 0 < R)
    (μ : ProbabilityMeasure (Interval R)) :
    2 * Real.cosh R * geometricMean (intervalCenteredCosh R) μ ≤ hyperbolicNumerator R μ := by
  have hobj := hyperbolicObjective_nonneg R hR μ
  have hK : 0 < 2 * Real.cosh R := mul_pos (by norm_num) (Real.cosh_pos R)
  have hlog : Real.log (2 * Real.cosh R) + (∫ p, intervalCenteredLogCosh R p ∂μ) ≤
      Real.log (hyperbolicNumerator R μ) := by
    unfold hyperbolicObjective at hobj
    linarith
  have h := Real.exp_le_exp.mpr hlog
  rw [Real.exp_add, Real.exp_log hK, Real.exp_log (hyperbolicNumerator_pos R hR μ)] at h
  rw [geometricMean_centered_eq_exp_integral]
  exact h

/-- Theorem 3.1, with all four fourth powers written literally. -/
theorem hyperbolic_geometric_mean_inequality_literal (R : ℝ) (hR : 0 < R)
    (μ : ProbabilityMeasure (Interval R)) :
    2 * Real.cosh R * geometricMean (intervalCenteredCosh R) μ ≤
      geometricMean (intervalCosh R) μ ^ 4 + geometricMean (intervalReflectedCosh R) μ ^ 4 -
        geometricMean (intervalSinh R) μ ^ 4 - geometricMean (intervalReflectedSinh R) μ ^ 4 := by
  have h := hyperbolic_geometric_mean_inequality R hR μ
  unfold hyperbolicNumerator at h
  erw [geometricMoment_nat 4 (intervalCosh R) μ,
    geometricMoment_nat 4 (intervalReflectedCosh R) μ,
    geometricMoment_nat 4 (intervalSinh R) μ,
    geometricMoment_nat 4 (intervalReflectedSinh R) μ] at h
  exact h

/-- Theorem 3.1, exact equality for arbitrary probability measures. -/
theorem hyperbolic_geometric_mean_equality_iff (R : ℝ) (hR : 0 < R)
    (μ : ProbabilityMeasure (Interval R)) :
    hyperbolicNumerator R μ = 2 * Real.cosh R * geometricMean (intervalCenteredCosh R) μ ↔
      HyperbolicEquality R μ := by
  rw [← hyperbolicObjective_eq_zero_iff R hR μ]
  exact hyperbolicObjective_eq_zero_iff_equality R hR μ

theorem hyperbolic_geometric_mean_equality_literal_iff (R : ℝ) (hR : 0 < R)
    (μ : ProbabilityMeasure (Interval R)) :
    geometricMean (intervalCosh R) μ ^ 4 + geometricMean (intervalReflectedCosh R) μ ^ 4 -
        geometricMean (intervalSinh R) μ ^ 4 - geometricMean (intervalReflectedSinh R) μ ^ 4 =
      2 * Real.cosh R * geometricMean (intervalCenteredCosh R) μ ↔ HyperbolicEquality R μ := by
  have h := hyperbolic_geometric_mean_equality_iff R hR μ
  unfold hyperbolicNumerator at h
  erw [geometricMoment_nat 4 (intervalCosh R) μ,
    geometricMoment_nat 4 (intervalReflectedCosh R) μ,
    geometricMoment_nat 4 (intervalSinh R) μ,
    geometricMoment_nat 4 (intervalReflectedSinh R) μ] at h
  exact h

end PaperVerification.Hyperbolic

#print axioms PaperVerification.Hyperbolic.hyperbolic_geometric_mean_inequality_literal
#print axioms PaperVerification.Hyperbolic.hyperbolic_geometric_mean_equality_literal_iff
end
end Source_HyperbolicTheorem
-- END ORIGINAL PaperVerification.HyperbolicTheorem


-- BEGIN ORIGINAL PaperVerification.DimensionLift
section Source_DimensionLift

-- original header: module
-- original header: public import Mathlib.Analysis.MeanInequalitiesPow
-- original header: public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
-- original header: public import Mathlib.Tactic.Linarith
-- original header: public import Mathlib.Tactic.FieldSimp
-- original header: @[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

lemma rpow_sub_le_difference {x u k : ℝ} (hu : 0 ≤ u) (hux : u ≤ x) (hk : 1 ≤ k) :
    (x - u) ^ k ≤ x ^ k - u ^ k := by
  have h := Real.add_rpow_le_rpow_add (sub_nonneg.mpr hux) hu hk
  rw [sub_add_cancel] at h
  linarith

lemma strict_rpow_superadditive {a b k : ℝ} (ha : 0 < a) (hb : 0 < b) (hk : 1 < k) :
    a ^ k + b ^ k < (a + b) ^ k := by
  have hab : 0 < a + b := add_pos ha hb
  have hpa := Real.rpow_lt_self_of_lt_one (div_pos ha hab)
    ((div_lt_one hab).mpr (lt_add_of_pos_right _ hb)) hk
  have hpb := Real.rpow_lt_self_of_lt_one (div_pos hb hab)
    ((div_lt_one hab).mpr (lt_add_of_pos_left _ ha)) hk
  rw [Real.div_rpow ha.le hab.le] at hpa
  rw [Real.div_rpow hb.le hab.le] at hpb
  have hs : a / (a + b) + b / (a + b) = 1 := by
    rw [← add_div, div_self hab.ne']
  apply (div_lt_one (Real.rpow_pos_of_pos hab k)).mp
  rw [add_div]
  linarith

lemma rpow_sub_eq_difference_iff {x u k : ℝ} (hu : 0 ≤ u) (hux : u < x)
    (hk : 1 < k) : (x - u) ^ k = x ^ k - u ^ k ↔ u = 0 := by
  constructor
  · intro heq
    by_contra hne
    have hu' : 0 < u := lt_of_le_of_ne hu (Ne.symm hne)
    have hs := strict_rpow_superadditive (sub_pos.mpr hux) hu' hk
    rw [sub_add_cancel] at hs
    linarith
  · rintro rfl
    simp [Real.zero_rpow (lt_trans zero_lt_one hk).ne']

lemma rpow_midpoint_lower {a b k : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hk : 1 ≤ k) :
    2 * ((a + b) / 2) ^ k ≤ a ^ k + b ^ k := by
  have hconv := (convexOn_rpow hk).2
  have h := hconv ha hb
    (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  simp only [smul_eq_mul] at h
  rw [show (1 / 2 : ℝ) * a + (1 / 2) * b = (a + b) / 2 by ring] at h
  linarith

lemma rpow_midpoint_strict {a b k : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≠ b)
    (hk : 1 < k) : 2 * ((a + b) / 2) ^ k < a ^ k + b ^ k := by
  have hconv := (strictConvexOn_rpow hk).2
  have h := hconv ha hb hab
    (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  simp only [smul_eq_mul] at h
  rw [show (1 / 2 : ℝ) * a + (1 / 2) * b = (a + b) / 2 by ring] at h
  linarith

/-- The power inequality used for every real dimension ratio k≥1 in Theorem 3.3. -/
theorem dimension_lift_bound {X Y U V q k : ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hXU : U ≤ X) (hYV : V ≤ Y)
    (hq : 0 ≤ q) (hk : 1 ≤ k) (hbase : 2 * q ≤ X + Y - U - V) :
    2 * q ^ k ≤ X ^ k + Y ^ k - U ^ k - V ^ k := by
  have hx := rpow_sub_le_difference hU hXU hk
  have hy := rpow_sub_le_difference hV hYV hk
  have hm := rpow_midpoint_lower (sub_nonneg.mpr hXU) (sub_nonneg.mpr hYV) hk
  have hq' : q ≤ ((X - U) + (Y - V)) / 2 := by linarith
  have hp := Real.rpow_le_rpow hq hq' (le_trans zero_le_one hk)
  linarith

/-- All equality conditions survive the passage from eight to higher dimension. -/
theorem dimension_lift_equality {X Y U V q k : ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hXU : U < X) (hYV : V < Y)
    (hq : 0 < q) (hk : 1 < k) (hbase : 2 * q ≤ X + Y - U - V) :
    X ^ k + Y ^ k - U ^ k - V ^ k = 2 * q ^ k ↔
      U = 0 ∧ V = 0 ∧ X = q ∧ Y = q := by
  have hx := rpow_sub_le_difference hU hXU.le hk.le
  have hy := rpow_sub_le_difference hV hYV.le hk.le
  have hm := rpow_midpoint_lower (sub_nonneg.mpr hXU.le) (sub_nonneg.mpr hYV.le) hk.le
  have hq' : q ≤ ((X - U) + (Y - V)) / 2 := by linarith
  have hp := Real.rpow_le_rpow hq.le hq' (le_trans zero_le_one hk.le)
  constructor
  · intro heq
    have huEq : (X - U) ^ k = X ^ k - U ^ k := by linarith
    have hvEq : (Y - V) ^ k = Y ^ k - V ^ k := by linarith
    have hU0 := (rpow_sub_eq_difference_iff hU hXU hk).mp huEq
    have hV0 := (rpow_sub_eq_difference_iff hV hYV hk).mp hvEq
    subst U
    subst V
    simp only [sub_zero, Real.zero_rpow (lt_trans zero_lt_one hk).ne'] at heq hq' hp
    have hXY : X = Y := by
      by_contra hne
      have hs := rpow_midpoint_strict hXU.le hYV.le hne hk
      linarith
    have hXq : X = q := by
      apply (Real.rpow_left_inj hXU.le hq.le (lt_trans zero_lt_one hk).ne').mp
      rw [← hXY] at heq
      linarith
    exact ⟨rfl, rfl, hXq, hXY.symm.trans hXq⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    simp [Real.zero_rpow (lt_trans zero_lt_one hk).ne', two_mul]

end PaperVerification.ColdSpots
end
end Source_DimensionLift
-- END ORIGINAL PaperVerification.DimensionLift


-- BEGIN ORIGINAL PaperVerification.Gaussian
section Source_Gaussian

-- original header: module
-- original header: public import Mathlib.Analysis.SpecialFunctions.Exp
-- original header: public import Mathlib.Analysis.Normed.Ring.InfiniteSum
-- original header: public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
-- original header: public import Mathlib.Topology.Algebra.InfiniteSum.Order
-- original header: public import Mathlib.Algebra.Group.Int.Even
-- original header: public import Mathlib.Algebra.Ring.Periodic
-- original header: public import Mathlib.Tactic.Linarith
-- original header: public import Mathlib.Tactic.NormNum
-- original header: public import Mathlib.Tactic.Ring
-- original header: public import Mathlib.Tactic.Positivity
-- original header: @[expose] public section
/-!
# Gaussian sums used in the cold-spots manuscript

The sums in this file are actual infinite series over the integers. In particular,
convergence is proved before positivity or rearrangements are used. Nothing in this
file assumes a cold-spot inequality.
-/

noncomputable section

open scoped BigOperators

namespace PaperVerification.ColdSpots

/-- The one-dimensional Gaussian lattice sum, in the manuscript's normalization. -/
def gaussian (α t : ℝ) : ℝ :=
  ∑' z : ℤ, Real.exp (-α * ((z : ℝ) - t) ^ 2)

/-- The parity character of the integer lattice, with values in the reals. -/
def paritySign (z : ℤ) : ℝ := if Even z then 1 else -1

/-- The alternating Gaussian series of Section 2. -/
def alternatingGaussian (α t : ℝ) : ℝ :=
  ∑' z : ℤ, paritySign z * Real.exp (-α * ((z : ℝ) - t) ^ 2)

lemma summable_gaussian_nat {α : ℝ} (hα : 0 < α) :
    Summable (fun n : ℕ ↦ Real.exp (-α * (n : ℝ) ^ 2)) := by
  apply Real.summable_exp_nat_mul_of_ge (neg_lt_zero.mpr hα)
  intro n
  exact_mod_cast (show n ≤ n ^ 2 by simpa only [pow_two] using Nat.le_mul_self n)

lemma summable_gaussian_zero {α : ℝ} (hα : 0 < α) :
    Summable (fun z : ℤ ↦ Real.exp (-α * (z : ℝ) ^ 2)) := by
  apply summable_int_iff_summable_nat_and_neg.mpr
  constructor
  · simpa using summable_gaussian_nat hα
  · simpa using summable_gaussian_nat hα

/-- A translated Gaussian is dominated by a constant times a centered Gaussian. -/
lemma gaussian_term_bound (α : ℝ) (hα : 0 ≤ α) (t z : ℝ) :
    Real.exp (-α * (z - t) ^ 2) ≤
      Real.exp (α * t ^ 2) * Real.exp (-(α / 2) * z ^ 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg hα (sq_nonneg (z - 2 * t))]

lemma summable_gaussian {α : ℝ} (hα : 0 < α) (t : ℝ) :
    Summable (fun z : ℤ ↦ Real.exp (-α * ((z : ℝ) - t) ^ 2)) := by
  refine ((summable_gaussian_zero (half_pos hα)).mul_left
    (Real.exp (α * t ^ 2))).of_nonneg_of_le (fun _ ↦ (Real.exp_pos _).le) ?_
  intro z
  exact gaussian_term_bound α hα.le t z

lemma hasSum_gaussian {α : ℝ} (hα : 0 < α) (t : ℝ) :
    HasSum (fun z : ℤ ↦ Real.exp (-α * ((z : ℝ) - t) ^ 2)) (gaussian α t) := by
  unfold gaussian
  exact (summable_gaussian hα t).hasSum

lemma norm_paritySign (z : ℤ) : ‖paritySign z‖ = 1 := by
  unfold paritySign
  split_ifs <;> norm_num

lemma paritySign_zero : paritySign 0 = 1 := by simp [paritySign]

lemma paritySign_neg (z : ℤ) : paritySign (-z) = paritySign z := by
  simp [paritySign]

lemma paritySign_add (z w : ℤ) : paritySign (z + w) = paritySign z * paritySign w := by
  by_cases hz : Even z <;> by_cases hw : Even w <;>
    simp [paritySign, Int.even_add, hz, hw]

lemma paritySign_add_one (z : ℤ) : paritySign (z + 1) = -paritySign z := by
  rw [paritySign_add]
  have h1 : paritySign 1 = -1 := by norm_num [paritySign]
  rw [h1, mul_neg_one]

lemma summable_alternatingGaussian {α : ℝ} (hα : 0 < α) (t : ℝ) :
    Summable (fun z : ℤ ↦ paritySign z * Real.exp (-α * ((z : ℝ) - t) ^ 2)) := by
  apply (summable_gaussian hα t).of_norm_bounded
  intro z
  have hs : |paritySign z| = 1 := by
    simpa only [Real.norm_eq_abs] using norm_paritySign z
  simp [norm_mul, Real.norm_eq_abs, hs, abs_of_pos (Real.exp_pos _)]

lemma hasSum_alternatingGaussian {α : ℝ} (hα : 0 < α) (t : ℝ) :
    HasSum (fun z : ℤ ↦ paritySign z * Real.exp (-α * ((z : ℝ) - t) ^ 2))
      (alternatingGaussian α t) := by
  unfold alternatingGaussian
  exact (summable_alternatingGaussian hα t).hasSum

lemma gaussian_pos {α : ℝ} (hα : 0 < α) (t : ℝ) : 0 < gaussian α t := by
  exact (summable_gaussian hα t).tsum_pos
    (fun z ↦ (Real.exp_pos _).le) 0 (Real.exp_pos _)

lemma alternatingGaussian_lt {α : ℝ} (hα : 0 < α) (t : ℝ) :
    alternatingGaussian α t < gaussian α t := by
  have hsum := (summable_gaussian hα t).sub (summable_alternatingGaussian hα t)
  have hp : 0 < ∑' z : ℤ, (Real.exp (-α * ((z : ℝ) - t) ^ 2) -
      paritySign z * Real.exp (-α * ((z : ℝ) - t) ^ 2)) := by
    refine hsum.tsum_pos ?_ (1 : ℤ) ?_
    · intro z
      unfold paritySign
      split_ifs <;> nlinarith [Real.exp_pos (-α * ((z : ℝ) - t) ^ 2)]
    · norm_num [paritySign]
      positivity
  rw [(summable_gaussian hα t).tsum_sub (summable_alternatingGaussian hα t)] at hp
  exact sub_pos.mp hp

lemma neg_gaussian_lt_alternatingGaussian {α : ℝ} (hα : 0 < α) (t : ℝ) :
    -gaussian α t < alternatingGaussian α t := by
  have hsum := (summable_gaussian hα t).add (summable_alternatingGaussian hα t)
  have hp : 0 < ∑' z : ℤ, (Real.exp (-α * ((z : ℝ) - t) ^ 2) +
      paritySign z * Real.exp (-α * ((z : ℝ) - t) ^ 2)) := by
    refine hsum.tsum_pos ?_ (0 : ℤ) ?_
    · intro z
      unfold paritySign
      split_ifs <;> nlinarith [Real.exp_pos (-α * ((z : ℝ) - t) ^ 2)]
    · norm_num [paritySign]
      positivity
  rw [(summable_gaussian hα t).tsum_add (summable_alternatingGaussian hα t)] at hp
  change 0 < gaussian α t + alternatingGaussian α t at hp
  linarith

lemma abs_alternatingGaussian_lt {α : ℝ} (hα : 0 < α) (t : ℝ) :
    |alternatingGaussian α t| < gaussian α t :=
  abs_lt.mpr ⟨neg_gaussian_lt_alternatingGaussian hα t, alternatingGaussian_lt hα t⟩

lemma gaussian_even (α t : ℝ) : gaussian α (-t) = gaussian α t := by
  unfold gaussian
  rw [← (Equiv.neg ℤ).tsum_eq]
  apply tsum_congr
  intro z
  congr 1
  simp only [Equiv.neg_apply, Int.cast_neg]
  ring

lemma gaussian_int_period (α t : ℝ) (k : ℤ) :
    gaussian α (t + k) = gaussian α t := by
  unfold gaussian
  rw [← (Equiv.addRight k).tsum_eq]
  apply tsum_congr
  intro z
  congr 1
  simp only [Equiv.coe_addRight, Int.cast_add]
  ring

lemma gaussian_one_period (α : ℝ) : Function.Periodic (gaussian α) 1 := by
  intro t
  simpa using gaussian_int_period α t 1

lemma alternatingGaussian_even (α t : ℝ) :
    alternatingGaussian α (-t) = alternatingGaussian α t := by
  unfold alternatingGaussian
  rw [← (Equiv.neg ℤ).tsum_eq]
  apply tsum_congr
  intro z
  simp only [Equiv.neg_apply, paritySign_neg, Int.cast_neg]
  congr 2
  ring

lemma alternatingGaussian_antiperiod (α t : ℝ) :
    alternatingGaussian α (t + 1) = -alternatingGaussian α t := by
  unfold alternatingGaussian
  rw [← (Equiv.addRight (1 : ℤ)).tsum_eq, ← tsum_neg]
  apply tsum_congr
  intro z
  simp only [Equiv.coe_addRight, paritySign_add_one, Int.cast_add, Int.cast_one]
  rw [show (z : ℝ) + 1 - (t + 1) = (z : ℝ) - t by ring]
  ring

lemma alternatingGaussian_half (α : ℝ) : alternatingGaussian α (1 / 2) = 0 := by
  have h := alternatingGaussian_antiperiod α (-(1 / 2))
  rw [alternatingGaussian_even] at h
  norm_num at h
  linarith

end PaperVerification.ColdSpots
end
end Source_Gaussian
-- END ORIGINAL PaperVerification.Gaussian


-- BEGIN ORIGINAL PaperVerification.LatticeDefs
section Source_LatticeDefs

-- original header: module
-- original header: public import Mathlib.Analysis.InnerProductSpace.PiL2
-- original header: public import Mathlib.Algebra.Group.Int.Even
-- original header: public import Mathlib.Algebra.BigOperators.Fin
-- original header: @[expose] public section
/-!
# Coordinate definitions for the lattices in the cold-spots manuscript

`sqDist` is the sum of the coordinate squares, hence the squared Euclidean
distance, not the squared norm on the unbundled function space.
`dPlusSet` is exactly D_n ∪ (D_n + (1/2,...,1/2)).
-/

noncomputable section

open scoped BigOperators

namespace PaperVerification.ColdSpots

def intVec {n : ℕ} (z : Fin n → ℤ) : Fin n → ℝ := fun i ↦ (z i : ℝ)

def sqDist {n : ℕ} (x y : Fin n → ℝ) : ℝ := ∑ i, (x i - y i) ^ 2

def dSet (n : ℕ) : Set (Fin n → ℝ) :=
  {x | ∃ z : Fin n → ℤ, Even (∑ i, z i) ∧ x = intVec z}

def dPlusSet (n : ℕ) : Set (Fin n → ℝ) :=
  {x | ∃ z : Fin n → ℤ, Even (∑ i, z i) ∧
    (x = intVec z ∨ x = fun i ↦ (z i : ℝ) + 1 / 2)}

def squaredDepth {n : ℕ} (L : Set (Fin n → ℝ)) (x : Fin n → ℝ) : ℝ :=
  sInf ((fun z ↦ sqDist x z) '' L)

def IsDeepHole {n : ℕ} (L : Set (Fin n → ℝ)) (x : Fin n → ℝ) : Prop :=
  ∀ y, squaredDepth L y ≤ squaredDepth L x

lemma sqDist_nonneg {n : ℕ} (x y : Fin n → ℝ) : 0 ≤ sqDist x y :=
  Finset.sum_nonneg fun i _ ↦ sq_nonneg _

lemma sqDist_comm {n : ℕ} (x y : Fin n → ℝ) : sqDist x y = sqDist y x := by
  apply Finset.sum_congr rfl
  intro i _
  exact sub_sq_comm (x i) (y i)

/-- The coordinate expression is exactly the squared Euclidean norm. -/
theorem sqDist_eq_euclidean_norm_sq {n : ℕ} (x y : Fin n → ℝ) :
    sqDist x y =
      ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) - WithLp.toLp 2 y‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

lemma zero_mem_dPlusSet (n : ℕ) : 0 ∈ dPlusSet n := by
  refine ⟨0, by simp, Or.inl ?_⟩
  ext i
  simp [intVec]

lemma dPlusSet_nonempty (n : ℕ) : (dPlusSet n).Nonempty :=
  ⟨0, zero_mem_dPlusSet n⟩

lemma squaredDepth_nonneg {n : ℕ} (L : Set (Fin n → ℝ)) (hL : L.Nonempty)
    (x : Fin n → ℝ) : 0 ≤ squaredDepth L x := by
  exact le_csInf (hL.image _) (by rintro r ⟨z, hz, rfl⟩; exact sqDist_nonneg _ _)

lemma squaredDepth_le {n : ℕ} {L : Set (Fin n → ℝ)} (x : Fin n → ℝ)
    {z : Fin n → ℝ} (hz : z ∈ L) : squaredDepth L x ≤ sqDist x z := by
  exact csInf_le ⟨0, by rintro r ⟨w, hw, rfl⟩; exact sqDist_nonneg _ _⟩ ⟨z, hz, rfl⟩

end PaperVerification.ColdSpots
end
end Source_LatticeDefs
-- END ORIGINAL PaperVerification.LatticeDefs


-- Kernel-environment audit: every mathematical source body precedes this command.
set_option maxHeartbeats 0 in
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let kenv := env.checked.get
  let entries := kenv.constants.foldStage2
    (fun rows name ci => rows.push (name, ci)) (#[] : Array (Name × ConstantInfo))
  let kind : ConstantInfo → String := fun ci => match ci with
    | .axiomInfo _ => "axiom"
    | .defnInfo _ => "definition"
    | .thmInfo _ => "theorem"
    | .opaqueInfo _ => "opaque"
    | .quotInfo _ => "quotient"
    | .ctorInfo _ => "constructor"
    | .recInfo _ => "recursor"
    | .inductInfo _ => "inductive"
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut rows : Array Json := #[]
  let mut failures : Array Json := #[]
  for (name, ci) in entries do
    if ci.isUnsafe then
      failures := failures.push (Json.mkObj [
        ("declaration", toJson name.toString),
        ("unsafe_declaration", toJson true)])
    let deps := ci.getUsedConstantsAsSet.toArray.qsort Name.lt
    let mut dependencyRows : Array Json := #[]
    for dep in deps do
      match kenv.find? dep with
      | none =>
        failures := failures.push (Json.mkObj [
          ("declaration", toJson name.toString),
          ("missing_dependency", toJson dep.toString)])
      | some info =>
        let origin := match env.getModuleIdxFor? dep with
          | some idx => env.header.moduleNames[idx]!.toString
          | none => env.mainModule.toString
        dependencyRows := dependencyRows.push (Json.mkObj [
          ("name", toJson dep.toString), ("kind", toJson (kind info)),
          ("module", toJson origin)])
    let axioms ← Lean.collectAxioms name
    let bad := axioms.filter (fun ax => !allowed.contains ax)
    if !bad.isEmpty then
      failures := failures.push (Json.mkObj [
        ("declaration", toJson name.toString),
        ("unapproved_axioms", toJson (bad.map Name.toString))])
    rows := rows.push (Json.mkObj [
      ("name", toJson name.toString), ("kind", toJson (kind ci)),
      ("unsafe", toJson ci.isUnsafe),
      ("type", toJson (toString ci.type)),
      ("level_parameters", toJson (ci.levelParams.map Name.toString)),
      ("has_body", toJson (ci.value? (allowOpaque := true)).isSome),
      ("dependencies", Json.arr dependencyRows),
      ("axioms", toJson (axioms.map Name.toString))])
  let sourceHash ← IO.getEnv "PAPER_VERIFICATION_SOURCE_SHA256"
  let fingerprint ← IO.getEnv "PAPER_VERIFICATION_FINGERPRINT"
  let document := Json.mkObj [
    ("schema", toJson (1 : Nat)),
    ("module", toJson env.mainModule.toString),
    ("source_sha256", toJson sourceHash),
    ("fingerprint", toJson fingerprint),
    ("kernel_environment", toJson true),
    ("declarations", Json.arr rows),
    ("failures", Json.arr failures),
    ("passed", toJson failures.isEmpty)]
  let target := (← IO.getEnv "PAPER_VERIFICATION_AUDIT_PATH").getD ".lake/build/paper-audit/PaperVerification_Lattice002.json"
  let path : System.FilePath := target
  if let some parent := path.parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile path (document.compress ++ "\n")
  if !failures.isEmpty then
    throwError "Kernel declaration audit rejected {failures.size} dependency/axiom findings; see {target}"
  logInfo m!"Kernel declaration audit passed for {rows.size} declarations; see {target}"
