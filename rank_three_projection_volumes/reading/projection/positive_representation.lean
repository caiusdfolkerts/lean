module

public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Abel

@[expose] public section
set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped NNReal CompactlySupported

namespace RankThreeProjection.PositiveRepresentation

/-!
This file supplies the functional-analytic construction of positive measures
used for mixed area measures. Its input is an additive, positively homogeneous
functional on a cone of continuous functions, monotone in pointwise order.
The order unit is the constant function one. Hahn–Banach and the
Riesz–Markov–Kakutani theorem are proved theorems in Mathlib.
-/

variable {X B : Type*} [TopologicalSpace X] [compactX : CompactSpace X]
  [AddCommMonoid B] [Module ℝ≥0 B]

variable (h : B →ₗ[ℝ≥0] C(X, ℝ))

/-- The real vector space of differences of functions in the cone. -/
def differenceSpace : Submodule ℝ C(X, ℝ) where
  carrier := {f | ∃ a b : B, f = h a - h b}
  zero_mem' := ⟨0, 0, by simp⟩
  add_mem' := by
    rintro f g ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    exact ⟨a + c, b + d, by simp only [map_add]; abel⟩
  smul_mem' := by
    rintro r f ⟨a, b, rfl⟩
    by_cases hr : 0 ≤ r
    · refine ⟨NNReal.mk r hr • a, NNReal.mk r hr • b, ?_⟩
      simp only [map_smul, NNReal.smul_def, NNReal.coe_mk, smul_sub]
    · have hr' : 0 ≤ -r := neg_nonneg.mpr (le_of_not_ge hr)
      refine ⟨NNReal.mk (-r) hr' • b, NNReal.mk (-r) hr' • a, ?_⟩
      simp only [map_smul, NNReal.smul_def, NNReal.coe_mk, neg_smul, smul_sub]
      abel

variable (F : B →ₗ[ℝ≥0] ℝ)
  (hmono : ∀ a b : B, h a ≤ h b → F a ≤ F b)

include hmono in
theorem difference_value_unique {a b c d : B}
    (heq : h a - h b = h c - h d) :
    F a - F b = F c - F d := by
  have heq' : h (a + d) = h (c + b) := by
    simp only [map_add]
    exact sub_eq_sub_iff_add_eq_add.mp heq
  have h₁ := hmono (a + d) (c + b) heq'.le
  have h₂ := hmono (c + b) (a + d) heq'.symm.le
  simp only [map_add] at h₁ h₂
  linarith

def first (f : differenceSpace h) : B := f.property.choose
def second (f : differenceSpace h) : B := f.property.choose_spec.choose

private theorem representation (f : differenceSpace h) :
    (f : C(X, ℝ)) = h (first h f) - h (second h f) :=
  f.property.choose_spec.choose_spec

def value (f : differenceSpace h) : ℝ :=
  F (first h f) - F (second h f)

include hmono in
private theorem value_eq (f : differenceSpace h) (a b : B)
    (hf : (f : C(X, ℝ)) = h a - h b) : value h F f = F a - F b := by
  exact difference_value_unique h F hmono ((representation h f).symm.trans hf)

/-- The cone functional has a well-defined real-linear extension to differences. -/
def differenceLinear : differenceSpace h →ₗ[ℝ] ℝ where
  toFun := value h F
  map_add' f g := by
    obtain ⟨a, b, hf⟩ := f.property
    obtain ⟨c, d, hg⟩ := g.property
    have hfg : ((f + g : differenceSpace h) : C(X, ℝ)) =
        h (a + c) - h (b + d) := by
      change (f : C(X, ℝ)) + (g : C(X, ℝ)) = _
      rw [hf, hg, map_add, map_add]
      abel
    rw [value_eq h F hmono (f + g) (a + c) (b + d) hfg,
      value_eq h F hmono f a b hf, value_eq h F hmono g c d hg,
      map_add, map_add]
    ring
  map_smul' r f := by
    obtain ⟨a, b, hf⟩ := f.property
    by_cases hr : 0 ≤ r
    · let c : ℝ≥0 := NNReal.mk r hr
      have hrf : ((r • f : differenceSpace h) : C(X, ℝ)) =
          h (c • a) - h (c • b) := by
        change r • (f : C(X, ℝ)) = _
        rw [hf, map_smul, map_smul]
        simp only [c, NNReal.smul_def, NNReal.coe_mk, smul_sub]
      rw [value_eq h F hmono (r • f) (c • a) (c • b) hrf,
        value_eq h F hmono f a b hf, map_smul, map_smul]
      change r * F a - r * F b = r * (F a - F b)
      ring
    · have hr' : 0 ≤ -r := neg_nonneg.mpr (le_of_not_ge hr)
      let c : ℝ≥0 := NNReal.mk (-r) hr'
      have hrf : ((r • f : differenceSpace h) : C(X, ℝ)) =
          h (c • b) - h (c • a) := by
        change r • (f : C(X, ℝ)) = _
        rw [hf, map_smul, map_smul]
        simp only [c, NNReal.smul_def, NNReal.coe_mk, neg_smul, smul_sub]
        abel
      rw [value_eq h F hmono (r • f) (c • b) (c • a) hrf,
        value_eq h F hmono f a b hf, map_smul, map_smul]
      change (-r) * F b - (-r) * F a = r * (F a - F b)
      ring

theorem differenceLinear_apply (f : differenceSpace h) (a b : B)
    (hf : (f : C(X, ℝ)) = h a - h b) :
    differenceLinear h F hmono f = F a - F b :=
  value_eq h F hmono f a b hf

theorem differenceLinear_mono (f g : differenceSpace h)
    (hfg : (f : C(X, ℝ)) ≤ (g : C(X, ℝ))) :
    differenceLinear h F hmono f ≤ differenceLinear h F hmono g := by
  obtain ⟨a, b, hf⟩ := f.property
  obtain ⟨c, d, hg⟩ := g.property
  have hab : h (a + d) ≤ h (c + b) := by
    rw [map_add, map_add]
    rw [hf, hg] at hfg
    intro x
    have hx := hfg x
    change h a x - h b x ≤ h c x - h d x at hx
    change h a x + h d x ≤ h c x + h b x
    linarith
  have hm := hmono (a + d) (c + b) hab
  rw [map_add, map_add] at hm
  rw [differenceLinear_apply h F hmono f a b hf,
    differenceLinear_apply h F hmono g c d hg]
  linarith

variable (ball : B) (hball : h ball = 1)

private def oneInSpace : differenceSpace h :=
  ⟨1, ball, 0, by simp [hball]⟩

private theorem value_one :
    differenceLinear h F hmono (oneInSpace h ball hball) = F ball := by
  rw [differenceLinear_apply h F hmono _ ball 0]
  · simp
  · simp [oneInSpace, hball]

include hmono hball in
theorem value_ball_nonnegative : 0 ≤ F ball := by
  have hzero : h 0 ≤ h ball := by
    rw [map_zero, hball]
    intro x
    change (0 : ℝ) ≤ 1
    exact zero_le_one
  have hm := hmono 0 ball hzero
  simpa only [map_zero] using hm

include hball in
theorem differenceLinear_norm_bound (f : differenceSpace h) :
    ‖differenceLinear h F hmono f‖ ≤ F ball * ‖f‖ := by
  let o : differenceSpace h := oneInSpace h ball hball
  have hfupper : (f : C(X, ℝ)) ≤ ((‖f‖ • o : differenceSpace h) : C(X, ℝ)) := by
    intro x
    simpa [o, oneInSpace] using (f : C(X, ℝ)).apply_le_norm x
  have hflower : (((-‖f‖) • o : differenceSpace h) : C(X, ℝ)) ≤
      (f : C(X, ℝ)) := by
    intro x
    simpa [o, oneInSpace] using (f : C(X, ℝ)).neg_norm_le_apply x
  have hu := differenceLinear_mono h F hmono f (‖f‖ • o) hfupper
  have hl := differenceLinear_mono h F hmono ((-‖f‖) • o) f hflower
  have ho : differenceLinear h F hmono o = F ball := value_one h F hmono ball hball
  rw [map_smul, ho] at hu hl
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · simpa only [smul_eq_mul, neg_mul, mul_comm] using hl
  · simpa only [smul_eq_mul, mul_comm] using hu

set_option backward.isDefEq.respectTransparency false in
include compactX hmono hball in
/-- A monotone cone functional with an order unit extends to a positive
continuous functional on all continuous functions. -/
theorem exists_positive_extension :
    ∃ Λ : C(X, ℝ) →ₚ[ℝ] ℝ, ∀ a : B, Λ (h a) = F a := by
  have hnonneg : 0 ≤ F ball := value_ball_nonnegative h F hmono ball hball
  let c : ℝ≥0 := NNReal.mk (F ball) hnonneg
  let p : Seminorm ℝ C(X, ℝ) := c • normSeminorm ℝ C(X, ℝ)
  have hp (v : C(X, ℝ)) : p v = F ball * ‖v‖ := by
    simp only [p, smul_apply, coe_normSeminorm, NNReal.smul_def,
      smul_eq_mul, c, NNReal.coe_mk]
  have hfbound (v : differenceSpace h) : differenceLinear h F hmono v ≤ p v := by
    rw [hp]
    exact (le_abs_self _).trans (by
      simpa only [Real.norm_eq_abs, Submodule.norm_coe] using
        differenceLinear_norm_bound h F hmono ball hball v)
  obtain ⟨g, hg, hgbound⟩ := Module.Dual.exists_extension_of_le_seminorm_real
    (differenceSpace h) (differenceLinear h F hmono) (p := p) hfbound
  have hgball : g 1 = F ball := by
    have hs := hg (oneInSpace h ball hball)
    exact hs.trans (value_one h F hmono ball hball)
  have hgpos : ∀ v : C(X, ℝ), 0 ≤ v → 0 ≤ g v := by
    intro v hv
    let r : ℝ := ‖v‖
    have hr : 0 ≤ r := norm_nonneg v
    have hvnorm : ‖v - r • (1 : C(X, ℝ))‖ ≤ r := by
      rw [ContinuousMap.norm_le _ hr]
      intro x
      rw [Real.norm_eq_abs, abs_le]
      have hlow := hv x
      change (0 : ℝ) ≤ v x at hlow
      have hhigh := v.apply_le_norm x
      change v x ≤ r at hhigh
      change -r ≤ v x - r * 1 ∧ v x - r * 1 ≤ r
      constructor <;> linarith
    have hbound := hgbound (v - r • (1 : C(X, ℝ)))
    rw [hp] at hbound
    have hupper : |g (v - r • (1 : C(X, ℝ)))| ≤ F ball * r :=
      hbound.trans (mul_le_mul_of_nonneg_left hvnorm hnonneg)
    have hlower := (abs_le.mp hupper).1
    rw [map_sub, map_smul, hgball] at hlower
    change -(F ball * r) ≤ g v - r * F ball at hlower
    linarith
  let Λ : C(X, ℝ) →ₚ[ℝ] ℝ :=
    { g with
      monotone' := by
        intro v w hvw
        have hp := hgpos (w - v) (sub_nonneg.mpr hvw)
        rw [map_sub] at hp
        change g v ≤ g w
        exact sub_nonneg.mp hp }
  refine ⟨Λ, ?_⟩
  intro a
  let a' : differenceSpace h := ⟨h a, a, 0, by simp⟩
  have he := hg a'
  change g (h a) = F a
  exact he.trans (by
    change differenceLinear h F hmono a' = F a
    rw [differenceLinear_apply h F hmono a' a 0 (by simp [a'])]
    simp)

include compactX hmono hball in
/-- Existence of a finite positive Borel measure representing every value of
the original cone functional. No measure representation is assumed. -/
theorem exists_representing_measure [T2Space X] [MeasurableSpace X] [BorelSpace X] :
    ∃ μ : Measure X, IsFiniteMeasure μ ∧
      ∀ a : B, (∫ x, h a x ∂μ) = F a := by
  obtain ⟨Λ, hΛ⟩ := exists_positive_extension h F hmono ball hball
  let Λc : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
    { toFun := fun f => Λ f.toContinuousMap
      map_add' := fun f g => by exact map_add Λ f.toContinuousMap g.toContinuousMap
      map_smul' := fun r f => by exact map_smul Λ r f.toContinuousMap
      monotone' := fun f g hfg => Λ.monotone' hfg }
  refine ⟨RealRMK.rieszMeasure Λc, inferInstance, ?_⟩
  intro a
  let f : C_c(X, ℝ) := CompactlySupportedContinuousMap.continuousMapEquiv (h a)
  exact (RealRMK.integral_rieszMeasure Λc f).trans (hΛ a)

end RankThreeProjection.PositiveRepresentation
