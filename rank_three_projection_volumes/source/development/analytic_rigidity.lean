module

public import development.alexandrov_fenchel
public import development.compactification
public import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Convex.Body
public import Mathlib.Analysis.Convex.Gauge
public import Mathlib.Analysis.Convex.Join
public import Mathlib.Analysis.Convex.Quasiconvex
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Module.Dual
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Multilinear.Basis
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Measure.FiniteMeasure
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import TauCeti.MeasureTheory.Constructions.HaarToSphere
public import TauCeti.MeasureTheory.Group.Measure
public import TauCeti.MeasureTheory.Measure.Lebesgue.BrunnMinkowski.Quantile
public import TauCeti.Probability.Quantile

set_option autoImplicit false

#assert_standard_axioms VolumePolynomials.mixedVolume_alexandrovFenchel

/- Source module: Projection.KneserSuss. SHA256: aab41f3314fc4c6ba23e05f4dcec5930b4cd3c5dd9eb7623d006c7cacbe9b965 -/
section DevelopmentSource0
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/







@[expose] public section
set_option autoImplicit false
noncomputable section

/-!
# The Kneser–Süss integral bound

This public supplement preserves the proof of the private Kneser–Süss
inequality in the pinned TauCeti source, commit
`06d5bb4e3ebb737dc6538567f5c53bf8800b9362`, file
`MeasureTheory/Measure/Lebesgue/BrunnMinkowski/Equality.lean`.
The theorem body is unchanged; only its visibility and enclosing namespace
are changed. No equality or stability assertion is imported as an assumption.

Original complete source SHA-256: `8cbd41fb3e547a401871d7e0d6ab5da7e43abd5301e6e74adf1b03535d9bfc0b`.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set TauCeti
open scoped ENNReal Pointwise RealInnerProductSpace

namespace RankThreeProjection.KneserSuss

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {e : E} {K L : Set E}

/-- **The Kneser–Süss integral inequality.** Along the weighted height quantile
`z = (1 - θ) z_K + θ z_L`, the derivative `z'` times the weighted geometric mean of the section
volumes of `K` at `z_K τ` and of `L` at `z_L τ`, integrated over `Ioo 0 1`, is at most the volume of
`(1 - θ) • K + θ • L`. -/
theorem setLIntegral_ofReal_le_volume_smul_add_smul (hK : Convex ℝ K)
    (hKb : Bornology.IsBounded K) (hKm : MeasurableSet K) (hK0 : volume K ≠ 0)
    (hL : Convex ℝ L) (hLb : Bornology.IsBounded L) (hLm : MeasurableSet L)
    (hL0 : volume L ≠ 0) (he : ‖e‖ = 1) {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1) :
    ∫⁻ τ in Ioo 0 1, ENNReal.ofReal
      (((1 - θ) * (volume.real K / volume.real {y : (ℝ ∙ e)ᗮ |
          (y : E) + ((volume[|K]).map fun x ↦ ⟪e, x⟫).quantile τ • e ∈ K}) +
        θ * (volume.real L / volume.real {y : (ℝ ∙ e)ᗮ |
          (y : E) + ((volume[|L]).map fun x ↦ ⟪e, x⟫).quantile τ • e ∈ L})) *
      (volume.real {y : (ℝ ∙ e)ᗮ |
          (y : E) + ((volume[|K]).map fun x ↦ ⟪e, x⟫).quantile τ • e ∈ K} ^ (1 - θ) *
        volume.real {y : (ℝ ∙ e)ᗮ |
          (y : E) + ((volume[|L]).map fun x ↦ ⟪e, x⟫).quantile τ • e ∈ L} ^ θ)) ≤
      volume ((1 - θ) • K + θ • L) := by
  set zK := ((volume[|K]).map fun x ↦ ⟪e, x⟫).quantile
  set zL := ((volume[|L]).map fun x ↦ ⟪e, x⟫).quantile
  set a : ℝ → ℝ := fun τ ↦ volume.real {y : (ℝ ∙ e)ᗮ | (y : E) + zK τ • e ∈ K}
  set b : ℝ → ℝ := fun τ ↦ volume.real {y : (ℝ ∙ e)ᗮ | (y : E) + zL τ • e ∈ L}
  set M := (1 - θ) • K + θ • L
  have ha (τ : ℝ) (hτ : τ ∈ Ioo 0 1) : 0 < a τ :=
    hK.volume_real_hyperplaneSection_quantile_pos hKb hK0 he hτ
  have hb (τ : ℝ) (hτ : τ ∈ Ioo 0 1) : 0 < b τ :=
    hL.volume_real_hyperplaneSection_quantile_pos hLb hL0 he hτ
  -- The weighted quantile `z` is strictly increasing with positive derivative `z'`.
  set z : ℝ → ℝ := fun τ ↦ (1 - θ) * zK τ + θ * zL τ
  set z' : ℝ → ℝ := fun τ ↦ (1 - θ) * (volume.real K / a τ) + θ * (volume.real L / b τ)
  have hz' (τ : ℝ) (hτ : τ ∈ Ioo 0 1) : HasDerivAt z (z' τ) τ :=
    ((hK.hasDerivAt_quantile_map_inner_cond hKb hKm hK0 he hτ).const_mul (1 - θ)).add
      ((hL.hasDerivAt_quantile_map_inner_cond hLb hLm hL0 he hτ).const_mul θ)
  have hzpos (τ : ℝ) (hτ : τ ∈ Ioo 0 1) : 0 < z' τ := by
    have hKr : 0 < volume.real K := ENNReal.toReal_pos hK0 hKb.measure_lt_top.ne
    have hLr : 0 < volume.real L := ENNReal.toReal_pos hL0 hLb.measure_lt_top.ne
    exact add_pos (mul_pos (by linarith) (div_pos hKr (ha τ hτ)))
      (mul_pos hθ₀ (div_pos hLr (hb τ hτ)))
  have hzmono : StrictMonoOn z (Ioo 0 1) := by
    intro s hs t ht hst
    have hK' := strictMonoOn_quantile _ (continuous_cdf_map_inner_cond he hK0
      hKb.measure_lt_top.ne) hs ht hst
    have hL' := strictMonoOn_quantile _ (continuous_cdf_map_inner_cond he hL0
      hLb.measure_lt_top.ne) hs ht hst
    simp only [z]
    nlinarith
  -- Pointwise, the integrand is bounded by the change-of-variables integrand along `z`, by
  -- Brunn–Minkowski in the hyperplane.
  have hpt (τ : ℝ) (hτ : τ ∈ Ioo 0 1) : ENNReal.ofReal (z' τ * (a τ ^ (1 - θ) * b τ ^ θ)) ≤
      ENNReal.ofReal |z' τ| * volume {y : (ℝ ∙ e)ᗮ | (y : E) + z τ • e ∈ M} := by
    rw [abs_of_pos (hzpos τ hτ), ENNReal.ofReal_mul (hzpos τ hτ).le,
      ENNReal.ofReal_mul (Real.rpow_nonneg (ha τ hτ).le _),
      ← ENNReal.ofReal_rpow_of_nonneg (ha τ hτ).le (by linarith),
      ← ENNReal.ofReal_rpow_of_nonneg (hb τ hτ).le hθ₀.le, ofReal_measureReal
        (hKb.volume_hyperplaneSection_lt_top e _).ne, ofReal_measureReal
        (hLb.volume_hyperplaneSection_lt_top e _).ne]
    exact mul_le_mul_right
      (volume_hyperplaneSection_rpow_mul_volume_hyperplaneSection_rpow_le e hKm hLm hθ₀ hθ₁ _ _) _
  -- Change variables along `z`, then apply Cavalieri's formula to the convex set `M`.
  refine (setLIntegral_mono' measurableSet_Ioo hpt).trans ?_
  rw [← lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo
    (fun τ hτ ↦ (hz' τ hτ).hasDerivWithinAt) hzmono.injOn
    (fun ζ ↦ volume {y : (ℝ ∙ e)ᗮ | (y : E) + ζ • e ∈ M})]
  refine (setLIntegral_le_lintegral _ _).trans_eq ?_
  rw [← volume_eq_lintegral_volume_hyperplaneSection e he
    (((hK.smul _).add (hL.smul _)).nullMeasurableSet (μ := volume))]

end RankThreeProjection.KneserSuss
end
end
end DevelopmentSource0

/- Source module: Projection.AMGMAlgebra. SHA256: 768edf949962931422ebba5163da07d71b7329ba869560e72ed899d524cd501d -/
section DevelopmentSource1






@[expose] public section

set_option autoImplicit false

namespace Projection

/-- The algebraic form of quantitative AMGM. The positive number `s` is specified
by its defining square equation, so the argument works in every ordered field. -/
theorem quantitative_amgm_of_square {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] (x y M s : R)
    (hx : 0 < x) (hy : 0 < y) (hxM : x ≤ M) (hyM : y ≤ M)
    (hs : 0 < s) (hs2 : s ^ 2 = x * y) :
    (x - y) ^ 2 / (8 * M ^ 2) ≤ (x + y) / (2 * s) - 1 := by
  have hM : 0 < M := lt_of_lt_of_le hx hxM
  have hsM : s ≤ M := by
    apply (sq_le_sq₀ hs.le hM.le).mp
    rw [hs2, pow_two]
    exact mul_le_mul hxM hyM hy.le hM.le
  have h2s : 0 < 2 * s := mul_pos zero_lt_two hs
  have ht : 0 < x + y + 2 * s := by linarith
  have hd : 0 < 2 * s * (x + y + 2 * s) := mul_pos h2s ht
  have hbound : 2 * s * (x + y + 2 * s) ≤ 8 * M ^ 2 := by
    calc
      2 * s * (x + y + 2 * s) ≤ (2 * M) * (4 * M) :=
        mul_le_mul (by linarith) (by linarith) ht.le (by linarith)
      _ = 8 * M ^ 2 := by ring
  calc
    (x - y) ^ 2 / (8 * M ^ 2) ≤
        (x - y) ^ 2 / (2 * s * (x + y + 2 * s)) :=
      div_le_div_of_nonneg_left (sq_nonneg (x - y)) hd hbound
    _ = (x + y) / (2 * s) - 1 := by
      apply (div_eq_iff hd.ne').mpr
      symm
      calc
        ((x + y) / (2 * s) - 1) * (2 * s * (x + y + 2 * s)) =
            (((x + y) / (2 * s) - 1) * (2 * s)) * (x + y + 2 * s) :=
          (mul_assoc _ _ _).symm
        _ = (x + y - 2 * s) * (x + y + 2 * s) := by
          rw [sub_mul, div_mul_cancel₀ _ h2s.ne', one_mul]
        _ = (x - y) ^ 2 := by nlinarith [hs2]

end Projection
end
end DevelopmentSource1

/- Source module: Projection.QuantitativeAMGM. SHA256: 6cb383d5843465bfcdae88d77f41c201cda6105e6b51a0b0f87837215ab7700c -/
section DevelopmentSource2





@[expose] public section

set_option autoImplicit false

namespace Projection

/-- A quantitative arithmetic--geometric mean inequality on a bounded positive interval.
The constant depends only on the common upper bound; no positive lower bound on either
variable is required. -/
theorem quantitative_amgm (x y M : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hxM : x ≤ M) (hyM : y ≤ M) :
    (x - y) ^ 2 / (8 * M ^ 2) ≤
      (x + y) / (2 * Real.sqrt (x * y)) - 1 := by
  exact quantitative_amgm_of_square x y M (Real.sqrt (x * y)) hx hy hxM hyM
    (Real.sqrt_pos.mpr (mul_pos hx hy)) (Real.sq_sqrt (mul_nonneg hx.le hy.le))

end Projection
end
end DevelopmentSource2

/- Source module: Projection.QuantileEnergy. SHA256: 57d1438638640de9639652aefedc3548cea29cb16f15534dc22dce41250ee9de -/
section DevelopmentSource3









@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory ProbabilityTheory TauCeti
open scoped Pointwise RealInnerProductSpace

namespace RankThreeProjection.QuantileStability

/-- The exact normalized arithmetic–geometric mean integrand. -/
def midpointRatio (x y : ℝ) : ℝ := (x + y) / (2 * Real.sqrt (x * y))

private theorem one_le_midpointRatio {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    1 ≤ midpointRatio x y := by
  have h := Projection.quantitative_amgm x y (x + y) hx hy
    (by linarith) (by linarith)
  have hz : 0 ≤ (x - y) ^ 2 / (8 * (x + y) ^ 2) :=
    div_nonneg (sq_nonneg _) (mul_nonneg (by linarith) (sq_nonneg _))
  change _ ≤ midpointRatio x y - 1 at h
  linarith

/-- The Kneser–Süss bound controls the squared difference of the two quantile
derivatives on every compact probability interval. The right side is the
actual volume deficit, so a deficit `o(t²)` gives energy `o(t²)`. -/
theorem midpoint_gap_energy_le (x y : ℝ → ℝ) (c V M a b : ℝ)
    (hc : 0 < c) (hV : 0 ≤ V) (hM : 0 < M)
    (hcx : ContinuousOn x (Ioo (0 : ℝ) 1))
    (hcy : ContinuousOn y (Ioo (0 : ℝ) 1))
    (hx : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < x t)
    (hy : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < y t)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1)
    (hxM : ∀ t ∈ Icc a b, x t ≤ M) (hyM : ∀ t ∈ Icc a b, y t ≤ M)
    (hKS : (∫⁻ t in Ioo (0 : ℝ) 1,
      ENNReal.ofReal (c * midpointRatio (x t) (y t))) ≤ ENNReal.ofReal V) :
    c / (8 * M ^ 2) * (∫ t in Icc a b, (x t - y t) ^ 2) ≤ V - c := by
  let U := Ioo (0 : ℝ) 1
  let g : ℝ → ℝ := fun t => c * midpointRatio (x t) (y t)
  letI : IsFiniteMeasure (volume.restrict U) := ⟨by simp [U, Real.volume_Ioo]⟩
  have hsub : Icc a b ⊆ U := fun t ht => ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩
  have hbase (t : ℝ) (ht : t ∈ U) : c ≤ g t := by
    have h := mul_le_mul_of_nonneg_left (one_le_midpointRatio (hx t ht) (hy t ht)) hc.le
    simpa only [mul_one, g] using h
  have hgnonneg : 0 ≤ᵐ[volume.restrict U] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact hc.le.trans (hbase t ht)
  have hgcont : ContinuousOn g U := by
    apply continuousOn_const.mul
    apply (hcx.add hcy).div ((hcx.mul hcy).sqrt.const_mul 2)
    intro t ht
    exact mul_ne_zero (by linarith)
      (Real.sqrt_pos.mpr (mul_pos (hx t ht) (hy t ht))).ne'
  have hgi : IntegrableOn g U :=
    ⟨(hgcont.aemeasurable measurableSet_Ioo).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal hgnonneg).mpr
        (hKS.trans_lt ENNReal.ofReal_lt_top)⟩
  have hIg : (∫ t in U, g t) ≤ V := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hKS
    rw [← ofReal_integral_eq_lintegral_ofReal hgi hgnonneg,
      ENNReal.toReal_ofReal (integral_nonneg_of_ae hgnonneg),
      ENNReal.toReal_ofReal hV] at h
    exact h
  have hgapint : IntegrableOn (fun t => g t - c) U := hgi.sub (integrable_const c)
  have hgapnonneg : 0 ≤ᵐ[volume.restrict U] (fun t => g t - c) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact sub_nonneg.mpr (hbase t ht)
  have hgap : (∫ t in U, g t - c) ≤ V - c := by
    rw [integral_sub hgi (integrable_const c)]
    have hcI : (∫ _t in U, c) = c := by simp [U, Real.volume_Ioo]
    rw [hcI]
    exact sub_le_sub_right hIg c
  have henergyint : IntegrableOn
      (fun t => (c / (8 * M ^ 2)) * (x t - y t) ^ 2) (Icc a b) :=
    (((hcx.mono hsub).sub (hcy.mono hsub)).pow 2 |>.const_mul _).integrableOn_Icc
  have hpoint (t : ℝ) (ht : t ∈ Icc a b) :
      (c / (8 * M ^ 2)) * (x t - y t) ^ 2 ≤ g t - c := by
    have h := mul_le_mul_of_nonneg_left
      (Projection.quantitative_amgm (x t) (y t) M (hx t (hsub ht))
        (hy t (hsub ht)) (hxM t ht) (hyM t ht)) hc.le
    change _ ≤ c * (midpointRatio (x t) (y t) - 1) at h
    calc
      (c / (8 * M ^ 2)) * (x t - y t) ^ 2 =
          c * ((x t - y t) ^ 2 / (8 * M ^ 2)) := by ring
      _ ≤ c * (midpointRatio (x t) (y t) - 1) := h
      _ = g t - c := by dsimp only [g]; ring
  have hsmall := setIntegral_mono_on henergyint (hgapint.mono_set hsub)
    measurableSet_Icc hpoint
  have hlarge := setIntegral_mono_set hgapint hgapnonneg
    (Filter.Eventually.of_forall (fun t ht => hsub ht))
  rw [integral_const_mul] at hsmall
  exact hsmall.trans (hlarge.trans hgap)

private theorem midpoint_integrand_identity (v w a b : ℝ)
    (hv : 0 < v) (hw : 0 < w) (ha : 0 < a) (hb : 0 < b) :
    ((v / a + w / b) / 2) * (Real.sqrt a * Real.sqrt b) =
      Real.sqrt (v * w) * midpointRatio (v / a) (w / b) := by
  have hs : Real.sqrt ((v / a) * (w / b)) =
      Real.sqrt (v * w) / (Real.sqrt a * Real.sqrt b) := by
    rw [div_mul_div_comm, Real.sqrt_div (mul_nonneg hv.le hw.le), Real.sqrt_mul ha.le]
  unfold midpointRatio
  rw [hs]
  field_simp [(Real.sqrt_pos.mpr (mul_pos hv hw)).ne',
    (Real.sqrt_pos.mpr ha).ne', (Real.sqrt_pos.mpr hb).ne']
  <;> ring

section ConvexBodies

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def heightQuantile (K : Set E) (e : E) : ℝ → ℝ :=
  ((volume[|K]).map fun x => ⟪e, x⟫).quantile

def sectionAtQuantile (K : Set E) (e : E) (t : ℝ) : ℝ :=
  volume.real {y : (ℝ ∙ e)ᗮ | (y : E) + heightQuantile K e t • e ∈ K}

def heightQuantileSlope (K : Set E) (e : E) (t : ℝ) : ℝ :=
  volume.real K / sectionAtQuantile K e t

theorem hasDerivAt_heightQuantile (K : ConvexBody E) {e : E} (he : ‖e‖ = 1)
    (hK : volume (K : Set E) ≠ 0) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (heightQuantile (K : Set E) e)
      (heightQuantileSlope (K : Set E) e t) t :=
  K.convex.hasDerivAt_quantile_map_inner_cond K.isCompact.isBounded
    K.isCompact.measurableSet hK he ht

theorem heightQuantileSlope_pos (K : ConvexBody E) {e : E} (he : ‖e‖ = 1)
    (hK : volume (K : Set E) ≠ 0) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < heightQuantileSlope (K : Set E) e t :=
  div_pos (ENNReal.toReal_pos hK K.isCompact.measure_lt_top.ne)
    (K.convex.volume_real_hyperplaneSection_quantile_pos K.isCompact.isBounded hK he ht)

theorem continuousOn_heightQuantileSlope (K : ConvexBody E) {e : E} (he : ‖e‖ = 1)
    (hK : volume (K : Set E) ≠ 0) :
    ContinuousOn (heightQuantileSlope (K : Set E) e) (Ioo (0 : ℝ) 1) := by
  exact continuousOn_const.div
    (K.convex.continuousOn_volume_real_hyperplaneSection_quantile K.isCompact.isBounded hK he)
    (fun t ht =>
      (K.convex.volume_real_hyperplaneSection_quantile_pos K.isCompact.isBounded hK he ht).ne')

theorem continuousOn_heightQuantile (K : ConvexBody E) {e : E} (he : ‖e‖ = 1)
    (hK : volume (K : Set E) ≠ 0) :
    ContinuousOn (heightQuantile (K : Set E) e) (Ioo (0 : ℝ) 1) :=
  HasDerivAt.continuousOn (fun _ ht => hasDerivAt_heightQuantile K he hK ht)

theorem integrableOn_heightQuantile (K : ConvexBody E) (e : E)
    (hK : volume (K : Set E) ≠ 0) :
    IntegrableOn (heightQuantile (K : Set E) e) (Ioo (0 : ℝ) 1) :=
  integrableOn_quantile_map_inner_cond e K.isCompact.isBounded K.isCompact.measurableSet hK

theorem integral_heightQuantile (K : ConvexBody E) (e : E)
    (hK : volume (K : Set E) ≠ 0) :
    (∫ t in Ioo (0 : ℝ) 1, heightQuantile (K : Set E) e t) =
      ∫ x, ⟪e, x⟫ ∂volume[|(K : Set E)] := by
  haveI := cond_isProbabilityMeasure_of_finite hK K.isCompact.measure_lt_top.ne
  change (∫ t in Ioo (0 : ℝ) 1,
    ((volume[|(K : Set E)]).map fun x => ⟪e, x⟫).quantile t) = _
  rw [Measure.setIntegral_quantile_eq_integral]
  exact integral_map (continuous_const.inner continuous_id).measurable.aemeasurable
    aestronglyMeasurable_id

/-- Quantitative Kneser–Süss for actual compact convex bodies, with no
assumed relation between height quantiles and sections. -/
theorem convexBody_midpoint_quantile_energy (K L : ConvexBody E)
    {e : E} (he : ‖e‖ = 1) (hK : volume (K : Set E) ≠ 0)
    (hL : volume (L : Set E) ≠ 0) (M a b : ℝ) (hM : 0 < M)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1)
    (hxM : ∀ t ∈ Icc a b, heightQuantileSlope (K : Set E) e t ≤ M)
    (hyM : ∀ t ∈ Icc a b, heightQuantileSlope (L : Set E) e t ≤ M) :
    Real.sqrt (volume.real (K : Set E) * volume.real (L : Set E)) / (8 * M ^ 2) *
        (∫ t in Icc a b,
          (heightQuantileSlope (K : Set E) e t - heightQuantileSlope (L : Set E) e t) ^ 2) ≤
      volume.real (((1 / 2 : ℝ) • K + (1 / 2 : ℝ) • L : ConvexBody E) : Set E) -
        Real.sqrt (volume.real (K : Set E) * volume.real (L : Set E)) := by
  let V := volume.real (K : Set E)
  let W := volume.real (L : Set E)
  have hV : 0 < V := ENNReal.toReal_pos hK K.isCompact.measure_lt_top.ne
  have hW : 0 < W := ENNReal.toReal_pos hL L.isCompact.measure_lt_top.ne
  have hsectionK (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      0 < sectionAtQuantile (K : Set E) e t :=
    K.convex.volume_real_hyperplaneSection_quantile_pos K.isCompact.isBounded hK he ht
  have hsectionL (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      0 < sectionAtQuantile (L : Set E) e t :=
    L.convex.volume_real_hyperplaneSection_quantile_pos L.isCompact.isBounded hL he ht
  apply midpoint_gap_energy_le
    (heightQuantileSlope (K : Set E) e) (heightQuantileSlope (L : Set E) e)
    (Real.sqrt (V * W)) _ M a b (Real.sqrt_pos.mpr (mul_pos hV hW))
    measureReal_nonneg hM
  · exact continuousOn_const.div
      (K.convex.continuousOn_volume_real_hyperplaneSection_quantile
        K.isCompact.isBounded hK he) (fun t ht => (hsectionK t ht).ne')
  · exact continuousOn_const.div
      (L.convex.continuousOn_volume_real_hyperplaneSection_quantile
        L.isCompact.isBounded hL he) (fun t ht => (hsectionL t ht).ne')
  · exact fun t ht => div_pos hV (hsectionK t ht)
  · exact fun t ht => div_pos hW (hsectionL t ht)
  · exact ha
  · exact hab
  · exact hb
  · exact hxM
  · exact hyM
  · have hKS := KneserSuss.setLIntegral_ofReal_le_volume_smul_add_smul
      K.convex K.isCompact.isBounded K.isCompact.measurableSet hK
      L.convex L.isCompact.isBounded L.isCompact.measurableSet hL he
      (θ := (1 / 2 : ℝ)) (by linarith) (by linarith)
    have hone : (1 : ℝ) - 1 / 2 = 1 / 2 := by ring
    rw [hone] at hKS
    have hsame :
        (∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal
          (Real.sqrt (V * W) * midpointRatio
            (heightQuantileSlope (K : Set E) e t) (heightQuantileSlope (L : Set E) e t))) =
        ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal
          (((1 / 2 : ℝ) * (V / sectionAtQuantile (K : Set E) e t) +
              (1 / 2 : ℝ) * (W / sectionAtQuantile (L : Set E) e t)) *
            (sectionAtQuantile (K : Set E) e t ^ (1 / 2 : ℝ) *
              sectionAtQuantile (L : Set E) e t ^ (1 / 2 : ℝ))) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      congr 1
      rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
      have hid := midpoint_integrand_identity V W
        (sectionAtQuantile (K : Set E) e t) (sectionAtQuantile (L : Set E) e t)
        hV hW (hsectionK t ht) (hsectionL t ht)
      dsimp only [heightQuantileSlope]
      convert hid.symm using 1 <;> ring
    rw [hsame,
      ofReal_measureReal (((1 / 2 : ℝ) • K + (1 / 2 : ℝ) • L).isCompact.measure_lt_top.ne)]
    simpa only [V, W, sectionAtQuantile, heightQuantile,
      ConvexBody.coe_add, ConvexBody.coe_smul]
      using hKS

end ConvexBodies
end RankThreeProjection.QuantileStability
end
end
end DevelopmentSource3

/- Source module: Projection.QuasiconcaveQuantiles. SHA256: 3edf77bad4d1e3981d20ec373e4872ff39968d7c58a30140263c1afcb5094e42 -/
section DevelopmentSource4









@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory

namespace RankThreeProjection.QuantileStability

/-- At every point of a quasiconcave density, at least one entire tail is
bounded above by the density at that point. No choice of a maximizer or
regularity at the endpoints is needed. -/
theorem quasiconcave_one_sided_bound (f : ℝ → ℝ) {l s r : ℝ}
    (hf : QuasiconcaveOn ℝ (Icc l r) f) (hs : s ∈ Icc l r) :
    (∀ x ∈ Icc l s, f x ≤ f s) ∨ (∀ x ∈ Icc s r, f x ≤ f s) := by
  by_cases hleft : ∀ x ∈ Icc l s, f x ≤ f s
  · exact Or.inl hleft
  · right
    push_neg at hleft
    obtain ⟨x, hx, hfx⟩ := hleft
    intro y hy
    by_contra hfy
    have hy' : f s < f y := lt_of_not_ge hfy
    have hmid := (hf.convex_gt (f s)).ordConnected.out
      ⟨⟨hx.1, hx.2.trans hs.2⟩, hfx⟩
      ⟨⟨hs.1.trans hy.1, hy.2⟩, hy'⟩ ⟨hx.2, hy.1⟩
    exact (lt_irrefl (f s)) hmid.2

/-- The smaller cumulative mass divided by the local density is at most
the width of the support interval. This elementary bound controls the tails
of convex-body height quantiles uniformly. -/
theorem quasiconcave_tail_integral_bound (f : ℝ → ℝ) {l s r : ℝ}
    (hf : QuasiconcaveOn ℝ (Icc l r) f) (hs : s ∈ Icc l r)
    (hfs : 0 ≤ f s)
    (hleft : IntervalIntegrable f volume l s)
    (hright : IntervalIntegrable f volume s r) :
    min (∫ x in l..s, f x) (∫ x in s..r, f x) ≤ (r - l) * f s := by
  rcases quasiconcave_one_sided_bound f hf hs with h | h
  · have hI := intervalIntegral.integral_mono_on hs.1 hleft
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => f s) volume l s) h
    rw [intervalIntegral.integral_const, smul_eq_mul] at hI
    exact (min_le_left _ _).trans (hI.trans
      (mul_le_mul_of_nonneg_right (sub_le_sub_right hs.2 l) hfs))
  · have hI := intervalIntegral.integral_mono_on hs.2 hright
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => f s) volume s r) h
    rw [intervalIntegral.integral_const, smul_eq_mul] at hI
    exact (min_le_right _ _).trans (hI.trans
      (mul_le_mul_of_nonneg_right (sub_le_sub_left hs.1 r) hfs))

/-- In probability coordinates, the preceding bound says
`min(τ,1−τ) * z'(τ) ≤ width`, where `z' = totalMass / density`. -/
theorem quasiconcave_inverse_density_bound (f : ℝ → ℝ) {l s r V τ : ℝ}
    (hf : QuasiconcaveOn ℝ (Icc l r) f) (hs : s ∈ Icc l r)
    (hfs : 0 < f s) (hV : 0 ≤ V)
    (hleft : IntervalIntegrable f volume l s)
    (hright : IntervalIntegrable f volume s r)
    (hF : (∫ x in l..s, f x) = τ * V)
    (hG : (∫ x in s..r, f x) = (1 - τ) * V) :
    min τ (1 - τ) * (V / f s) ≤ r - l := by
  have h := quasiconcave_tail_integral_bound f hf hs hfs.le hleft hright
  rw [hF, hG, ← min_mul_of_nonneg _ _ hV] at h
  rw [← mul_div_assoc, div_le_iff₀ hfs]
  exact h

/-- A weighted derivative bound gives a uniform modulus for multiplicative
changes of small probability levels. Unlike a global derivative bound, this
remains useful arbitrarily close to the endpoint `τ = 0`. -/
theorem quantile_multiplicative_increment
    (q v : ℝ → ℝ) (W : ℝ) (hW : 0 ≤ W)
    (hderiv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt q (v t) t)
    (hv : ∀ t ∈ Ioo (0 : ℝ) 1, 0 ≤ v t)
    (hweighted : ∀ t ∈ Ioo (0 : ℝ) 1, min t (1 - t) * v t ≤ W)
    {t Λ r : ℝ} (ht : 0 < t) (ht2 : t ≤ 1 / 2)
    (hΛ1 : 1 ≤ Λ) (hΛ2 : Λ ≤ 3 / 2) (hr : r ∈ Icc (t / Λ) (Λ * t)) :
    |q r - q t| ≤ 2 * W * (Λ - 1) := by
  have hΛ : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ1
  have hsub : Icc (t / Λ) (Λ * t) ⊆ Ioo (0 : ℝ) 1 := by
    intro x hx
    exact ⟨(div_pos ht hΛ).trans_le hx.1, by nlinarith [hx.2]⟩
  have htmem : t ∈ Icc (t / Λ) (Λ * t) := by
    constructor
    · exact (div_le_iff₀ hΛ).mpr (by nlinarith)
    · nlinarith
  have hbound (x : ℝ) (hx : x ∈ Icc (t / Λ) (Λ * t)) :
      ‖v x‖ ≤ 2 * W / t := by
    have hxI := hsub hx
    have hx0 := hv x hxI
    have hxmin : t / 2 ≤ min x (1 - x) := by
      have hxΛ : t ≤ x * Λ := (div_le_iff₀ hΛ).mp hx.1
      apply le_min
      · nlinarith [hxI.1]
      · nlinarith [hx.2]
    have hw := (mul_le_mul_of_nonneg_right hxmin hx0).trans (hweighted x hxI)
    rw [Real.norm_eq_abs, abs_of_nonneg hx0, le_div_iff₀ ht]
    nlinarith
  have hLip := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (hderiv x (hsub hx)).hasDerivWithinAt) hbound (convex_Icc _ _) htmem hr
  have hlow : t * (2 - Λ) ≤ t / Λ := by
    apply (le_div_iff₀ hΛ).mpr
    nlinarith [mul_nonneg ht.le (sq_nonneg (Λ - 1))]
  have hdist : |r - t| ≤ t * (Λ - 1) := by
    rw [abs_le]
    constructor
    · nlinarith [hlow.trans hr.1]
    · nlinarith [hr.2]
  have hC : 0 ≤ 2 * W / t := div_nonneg (mul_nonneg zero_le_two hW) ht.le
  have h := hLip.trans (mul_le_mul_of_nonneg_left hdist hC)
  have he : (2 * W / t) * (t * (Λ - 1)) = 2 * W * (Λ - 1) := by
    calc
      _ = (2 * W * (Λ - 1)) * (t / t) := by ring
      _ = _ := by rw [div_self ht.ne', mul_one]
  simpa only [Real.norm_eq_abs, he] using h

end RankThreeProjection.QuantileStability
end
end
end DevelopmentSource4

/- Source module: Projection.HeightDensity. SHA256: 31909b3f8296a47b73f7b7b52fb4d25729b129f940841708a591c2add3458bf2 -/
section DevelopmentSource5







@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory ProbabilityTheory TauCeti
open scoped Pointwise RealInnerProductSpace

namespace RankThreeProjection.QuantileStability

/-- Extending a nonnegative concave-root density by zero preserves
quasiconcavity, including at the ends of its support. -/
theorem quasiconcave_zero_extension_of_concave_rpow
    (f : ℝ → ℝ) (S : Set ℝ) (p : ℝ) (hp : 0 < p)
    (hf : ∀ x, 0 ≤ f x) (hzero : ∀ x ∉ S, f x = 0)
    (hroot : ConcaveOn ℝ S (fun x => f x ^ p)) :
    QuasiconcaveOn ℝ univ f := by
  rw [quasiconcaveOn_iff_min_le]
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  by_cases hmin : min (f x) (f y) ≤ 0
  · exact hmin.trans (hf _)
  have hminpos : 0 < min (f x) (f y) := lt_of_not_ge hmin
  have hx : x ∈ S := by
    by_contra hn
    have h := hminpos.trans_le (min_le_left _ _)
    rw [hzero x hn] at h
    exact (lt_irrefl (0 : ℝ)) h
  have hy : y ∈ S := by
    by_contra hn
    have h := hminpos.trans_le (min_le_right _ _)
    rw [hzero y hn] at h
    exact (lt_irrefl (0 : ℝ)) h
  apply (Real.rpow_le_rpow_iff hminpos.le (hf _) hp).mp
  calc
    min (f x) (f y) ^ p =
        a * min (f x) (f y) ^ p + b * min (f x) (f y) ^ p := by
          rw [← add_mul, hab, one_mul]
    _ ≤ a * f x ^ p + b * f y ^ p :=
      add_le_add
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hminpos.le (min_le_left _ _) hp.le) ha)
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hminpos.le (min_le_right _ _) hp.le) hb)
    _ ≤ _ := hroot.2 hx hy ha hb hab

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def heightDensity (K : Set E) (e : E) (s : ℝ) : ℝ :=
  volume.real {y : (ℝ ∙ e)ᗮ | (y : E) + s • e ∈ K}

theorem heightDensity_zero_off_image (K : ConvexBody E) {e : E} (he : ‖e‖ = 1)
    (s : ℝ) (hs : s ∉ (fun x => ⟪e, x⟫) '' (K : Set E)) :
    heightDensity (K : Set E) e s = 0 := by
  have hempty : {y : (ℝ ∙ e)ᗮ | (y : E) + s • e ∈ (K : Set E)} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro y hy
    exact hs ⟨(y : E) + s • e, hy, inner_add_smul e he y s⟩
  simp only [heightDensity, hempty, measureReal_empty]

theorem heightDensity_quasiconcave (K : ConvexBody E) {e : E} (he : ‖e‖ = 1)
    (hdim : 2 ≤ Module.finrank ℝ E) :
    QuasiconcaveOn ℝ univ (heightDensity (K : Set E) e) := by
  have hp : (0 : ℝ) < (((Module.finrank ℝ E - 1 : ℕ) : ℝ)⁻¹) := by
    apply inv_pos.mpr
    exact Nat.cast_pos.mpr (show 0 < Module.finrank ℝ E - 1 by omega)
  exact quasiconcave_zero_extension_of_concave_rpow
    (heightDensity (K : Set E) e) ((fun x => ⟪e, x⟫) '' (K : Set E)) _ hp
    (fun _ => measureReal_nonneg) (heightDensity_zero_off_image K he)
    (K.convex.concaveOn_volume_real_hyperplaneSection_rpow he
      (fun s => (K.isCompact.isBounded.volume_hyperplaneSection_lt_top e s).ne))

theorem heightDensity_integrable (K : ConvexBody E) {e : E} (he : ‖e‖ = 1) :
    Integrable (heightDensity (K : Set E) e) := by
  apply integrable_toReal_of_lintegral_ne_top
    (measurable_volume_hyperplaneSection e he K.isCompact.measurableSet).aemeasurable
  rw [← volume_eq_lintegral_volume_hyperplaneSection e he K.isCompact.measurableSet.nullMeasurableSet]
  exact K.isCompact.measure_lt_top.ne

/-- Cavalieri's formula expressed with real interval integrals. -/
theorem integral_heightDensity (K : ConvexBody E) {e : E} (he : ‖e‖ = 1)
    {l r : ℝ} (hlr : l ≤ r) :
    (∫ s in l..r, heightDensity (K : Set E) e s) =
      volume.real {x ∈ (K : Set E) | ⟪e, x⟫ ∈ Ioc l r} := by
  rw [intervalIntegral.integral_of_le hlr]
  change (∫ s in Ioc l r,
      (volume {y : (ℝ ∙ e)ᗮ | (y : E) + s • e ∈ (K : Set E)}).toReal) = _
  rw [integral_toReal
    (measurable_volume_hyperplaneSection e he K.isCompact.measurableSet).aemeasurable
    (Filter.Eventually.of_forall
      (fun s => K.isCompact.isBounded.volume_hyperplaneSection_lt_top e s))]
  exact congrArg ENNReal.toReal
    (volume_sep_inner_mem_eq_setLIntegral e he K.isCompact.measurableSet.nullMeasurableSet
      measurableSet_Ioc).symm

/-- Actual convex-body height quantiles obey the uniform weighted derivative
bound. The proof uses Brunn's concavity principle and Cavalieri's formula,
rather than an assumed density or section regularity hypothesis. -/
theorem weighted_heightQuantileSlope_le (K : ConvexBody E) {e : E} (he : ‖e‖ = 1)
    (hdim : 2 ≤ Module.finrank ℝ E) (hK : volume (K : Set E) ≠ 0)
    (R : ℝ) (hR : ∀ x ∈ (K : Set E), ‖x‖ < R)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    min t (1 - t) * heightQuantileSlope (K : Set E) e t ≤ 2 * R := by
  let s := heightQuantile (K : Set E) e t
  let V := volume.real (K : Set E)
  have hV : 0 < V := ENNReal.toReal_pos hK K.isCompact.measure_lt_top.ne
  have hheight (x : E) (hx : x ∈ (K : Set E)) : -R < ⟪e, x⟫ ∧ ⟪e, x⟫ < R := by
    have h := (abs_real_inner_le_norm e x).trans_lt (by simpa only [he, one_mul] using hR x hx)
    exact abs_lt.mp h
  obtain ⟨x, hx, hxs⟩ := K.convex.quantile_map_inner_cond_mem_image_interior he hK
    K.isCompact.measure_lt_top.ne ht
  have hs : s ∈ Ioo (-R) R := by
    dsimp only [s, heightQuantile]
    rw [← hxs]
    exact hheight x (interior_subset hx)
  have hR0 : 0 < R := by linarith [hs.1, hs.2]
  have hleft := (heightDensity_integrable K he).intervalIntegrable (a := -R) (b := s)
  have hright := (heightDensity_integrable K he).intervalIntegrable (a := s) (b := R)
  have hF : (∫ z in -R..s, heightDensity (K : Set E) e z) = t * V := by
    rw [integral_heightDensity K he hs.1.le]
    have hset : {x ∈ (K : Set E) | ⟪e, x⟫ ∈ Ioc (-R) s} =
        {x ∈ (K : Set E) | ⟪e, x⟫ ≤ s} := by
      ext x
      exact and_congr_right (fun hx => ⟨And.right, fun h => ⟨(hheight x hx).1, h⟩⟩)
    rw [hset]
    haveI := cond_isProbabilityMeasure_of_finite hK K.isCompact.measure_lt_top.ne
    have hq := Measure.cdf_quantile
      ((volume[|(K : Set E)]).map fun x => ⟪e, x⟫)
      (continuous_cdf_map_inner_cond he hK K.isCompact.measure_lt_top.ne) ht.1 ht.2
    rw [cdf_map_inner_cond hK K.isCompact.measure_lt_top.ne] at hq
    exact (div_eq_iff hV.ne').mp hq
  have htotal : (∫ z in -R..R, heightDensity (K : Set E) e z) = V := by
    rw [integral_heightDensity K he (by linarith)]
    have hset : {x ∈ (K : Set E) | ⟪e, x⟫ ∈ Ioc (-R) R} = (K : Set E) := by
      ext x
      exact ⟨And.left, fun hx => ⟨hx, (hheight x hx).1, (hheight x hx).2.le⟩⟩
    rw [hset]
  have hG : (∫ z in s..R, heightDensity (K : Set E) e z) = (1 - t) * V := by
    have hsum := intervalIntegral.integral_add_adjacent_intervals hleft hright
    rw [hF, htotal] at hsum
    linarith
  have hfs : 0 < heightDensity (K : Set E) e s :=
    K.convex.volume_real_hyperplaneSection_quantile_pos K.isCompact.isBounded hK he ht
  have hq := quasiconcave_inverse_density_bound (heightDensity (K : Set E) e)
    (Convex.quasiconcaveOn_restrict (heightDensity_quasiconcave K he hdim)
      (subset_univ _) (convex_Icc _ _)) ⟨hs.1.le, hs.2.le⟩ hfs hV.le
    hleft hright hF hG
  change min t (1 - t) * (V / heightDensity (K : Set E) e s) ≤ _
  convert hq using 1 <;> ring

/-- A common outer-radius bound alone gives a common derivative bound on
every compact probability interval, uniformly as the bodies vary. -/
theorem heightQuantileSlope_le_of_radius (K : ConvexBody E) {e : E} (he : ‖e‖ = 1)
    (hdim : 2 ≤ Module.finrank ℝ E) (hK : volume (K : Set E) ≠ 0)
    (R : ℝ) (hR : ∀ x ∈ (K : Set E), ‖x‖ < R)
    {a b t : ℝ} (ha : 0 < a) (hb : b < 1) (ht : t ∈ Icc a b) :
    heightQuantileSlope (K : Set E) e t ≤ 2 * R / min a (1 - b) := by
  have htI : t ∈ Ioo (0 : ℝ) 1 := ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩
  have hp : 0 < min a (1 - b) := lt_min ha (sub_pos.mpr hb)
  have hnonneg : 0 ≤ heightQuantileSlope (K : Set E) e t :=
    div_nonneg measureReal_nonneg measureReal_nonneg
  have hmin : min a (1 - b) ≤ min t (1 - t) :=
    min_le_min ht.1 (sub_le_sub_left ht.2 1)
  have h := (mul_le_mul_of_nonneg_right hmin hnonneg).trans
    (weighted_heightQuantileSlope_le K he hdim hK R hR htI)
  exact (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using h)

end RankThreeProjection.QuantileStability
end
end
end DevelopmentSource5

/- Source module: Projection.QuantileLimit. SHA256: 21971c8f95b75eda08795bdbe8a4b1bfb0506d9f5df9d9c43335883f50f97523 -/
section DevelopmentSource6










@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace RankThreeProjection.QuantileStability

/-- The elementary integral Cauchy–Schwarz inequality, obtained by integrating
a square. The hypotheses explicitly include both required integrabilities. -/
theorem integral_sq_le_mass_mul_integral_sq
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → ℝ) (hf : Integrable f μ) (hf2 : Integrable (fun x => f x ^ 2) μ)
    (hm : 0 < μ.real univ) :
    (∫ x, f x ∂μ) ^ 2 ≤ μ.real univ * ∫ x, f x ^ 2 ∂μ := by
  let I := ∫ x, f x ∂μ
  let J := ∫ x, f x ^ 2 ∂μ
  let m := μ.real univ
  let c := I / m
  have hc : c * m = I := div_mul_cancel₀ _ hm.ne'
  have hnonneg : 0 ≤ ∫ x, (f x - c) ^ 2 ∂μ :=
    integral_nonneg (fun _ => sq_nonneg _)
  have he : (∫ x, (f x - c) ^ 2 ∂μ) = J - 2 * c * I + c ^ 2 * m := by
    calc
      _ = ∫ x, (f x ^ 2 - (2 * c) * f x) + c ^ 2 ∂μ := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun _ => by ring)
      _ = _ := by
        have hAdd := integral_add (hf2.sub (hf.const_mul (2 * c)))
          (integrable_const (c ^ 2))
        simp only [Pi.sub_apply] at hAdd
        rw [hAdd, integral_sub hf2 (hf.const_mul (2 * c)),
          integral_const_mul, integral_const]
        change J - (2 * c) * I + m * c ^ 2 = _
        ring
  rw [he] at hnonneg
  have hp := mul_nonneg hnonneg hm.le
  have he' : (J - 2 * c * I + c ^ 2 * m) * m = m * J - I ^ 2 := by
    rw [← hc]
    ring
  rw [he'] at hp
  exact sub_nonneg.mp hp

/-- A one-dimensional energy bound controls oscillation. No Sobolev
completion or boundary regularity theorem is used. -/
theorem oscillation_sq_le_interval_energy (f v : ℝ → ℝ) {a b : ℝ}
    (hab : a ≤ b)
    (hderiv : ∀ x ∈ Icc a b, HasDerivAt f (v x) x)
    (hcont : ContinuousOn v (Icc a b)) :
    (f b - f a) ^ 2 ≤ (b - a) * ∫ x in Icc a b, v x ^ 2 := by
  rcases hab.lt_or_eq with hab | rfl
  · let μ : Measure ℝ := volume.restrict (Icc a b)
    letI : IsFiniteMeasure μ := ⟨by simp [μ, Real.volume_Icc]⟩
    have hm : μ.real univ = b - a := by
      simp [μ, Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (sub_pos.mpr hab).le]
    have hCS := integral_sq_le_mass_mul_integral_sq μ v hcont.integrableOn_Icc
      (hcont.pow 2).integrableOn_Icc (by rw [hm]; exact sub_pos.mpr hab)
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (by simpa only [uIcc_of_le hab.le] using hderiv) (hcont.intervalIntegrable_of_Icc hab.le)
    have hI : (∫ x in Icc a b, v x) = f b - f a := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le]
      exact hFTC
    change (∫ x in Icc a b, v x) ^ 2 ≤ μ.real univ *
      ∫ x in Icc a b, v x ^ 2 at hCS
    rw [hI, hm] at hCS
    exact hCS
  · simp

/-- An energy `o(t²)` makes the corresponding oscillation `o(t)`. -/
theorem tendsto_scaled_oscillation_of_energy
    (f v : ℝ → ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hderiv : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ∀ x ∈ Icc a b, HasDerivAt (f t) (v t x) x)
    (hcont : ∀ᶠ t in 𝓝[>] (0 : ℝ), ContinuousOn (v t) (Icc a b))
    (henergy : Tendsto
      (fun t : ℝ => (∫ x in Icc a b, v t x ^ 2) / t ^ 2) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun t : ℝ => (f t b - f t a) / t) (𝓝[>] 0) (𝓝 0) := by
  have hbound : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ((f t b - f t a) / t) ^ 2 ≤
        (b - a) * ((∫ x in Icc a b, v t x ^ 2) / t ^ 2) := by
    filter_upwards [hderiv, hcont] with t hd hc
    have h := div_le_div_of_nonneg_right
      (oscillation_sq_le_interval_energy (f t) (v t) hab hd hc) (sq_nonneg t)
    simpa only [div_pow, mul_div_assoc] using h
  have hsquare : Tendsto (fun t : ℝ => ((f t b - f t a) / t) ^ 2)
      (𝓝[>] 0) (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun _ => sq_nonneg _)) hbound
      (by simpa only [mul_zero] using tendsto_const_nhds.mul henergy)
  have habs := Real.continuous_sqrt.continuousAt.tendsto.comp hsquare
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero,
    Real.norm_eq_abs] using habs

/-- A bounded family whose pairwise oscillations vanish has a unique limit
once its mean is prescribed. The conclusion includes convergence in `L¹`,
which is what is needed for the ridge-test argument. -/
theorem mean_determines_flat_limit
    {ι X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {l : Filter ι} [l.IsCountablyGenerated]
    (F : ι → X → ℝ) (x₀ : X) (C c : ℝ)
    (hmeas : ∀ᶠ i in l, AEStronglyMeasurable (F i) μ)
    (hbound : ∀ᶠ i in l, ∀ᵐ x ∂μ, ‖F i x‖ ≤ C)
    (hbound₀ : ∀ᶠ i in l, ‖F i x₀‖ ≤ C)
    (hosc : ∀ᵐ x ∂μ, Tendsto (fun i => F i x - F i x₀) l (𝓝 0))
    (hmean : Tendsto (fun i => ∫ x, F i x ∂μ) l (𝓝 c)) :
    Tendsto (fun i => F i x₀) l (𝓝 c) ∧
      (∀ᵐ x ∂μ, Tendsto (fun i => F i x) l (𝓝 c)) ∧
      Tendsto (fun i => ∫ x, ‖F i x - c‖ ∂μ) l (𝓝 0) := by
  have hint : ∀ᶠ i in l, Integrable (F i) μ := by
    filter_upwards [hmeas, hbound] with i hi hb
    exact (integrable_const C).mono' hi hb
  have hGmeas : ∀ᶠ i in l, AEStronglyMeasurable (fun x => F i x - F i x₀) μ :=
    hmeas.mono (fun i hi => hi.sub aestronglyMeasurable_const)
  have hGbound : ∀ᶠ i in l, ∀ᵐ x ∂μ, ‖F i x - F i x₀‖ ≤ 2 * C := by
    filter_upwards [hbound, hbound₀] with i hi hi₀
    filter_upwards [hi] with x hx
    have h := (norm_sub_le (F i x) (F i x₀)).trans (add_le_add hx hi₀)
    linarith
  have hGlim : Tendsto (fun i => ∫ x, F i x - F i x₀ ∂μ) l (𝓝 0) := by
    simpa only [integral_zero] using
      tendsto_integral_filter_of_dominated_convergence (fun _ : X => 2 * C)
        hGmeas hGbound (integrable_const (2 * C)) hosc
  have hsplit : (fun i => ∫ x, F i x - F i x₀ ∂μ) =ᶠ[l]
      (fun i => (∫ x, F i x ∂μ) - F i x₀) := by
    filter_upwards [hint] with i hi
    rw [integral_sub hi (integrable_const (F i x₀))]
    simp
  have hdiff := Filter.Tendsto.congr' hsplit hGlim
  have h₀ : Tendsto (fun i => F i x₀) l (𝓝 c) := by
    simpa only [sub_sub_cancel, sub_zero] using hmean.sub hdiff
  have hpoint : ∀ᵐ x ∂μ, Tendsto (fun i => F i x) l (𝓝 c) := by
    filter_upwards [hosc] with x hx
    simpa only [sub_add_cancel, zero_add] using hx.add h₀
  refine ⟨h₀, hpoint, ?_⟩
  have hNmeas : ∀ᶠ i in l, AEStronglyMeasurable (fun x => ‖F i x - c‖) μ :=
    hmeas.mono (fun i hi => (hi.sub aestronglyMeasurable_const).norm)
  have hNbound : ∀ᶠ i in l, ∀ᵐ x ∂μ, ‖‖F i x - c‖‖ ≤ C + ‖c‖ := by
    filter_upwards [hbound] with i hi
    filter_upwards [hi] with x hx
    rw [norm_norm]
    exact (norm_sub_le _ _).trans (add_le_add hx le_rfl)
  have hNlim : ∀ᵐ x ∂μ, Tendsto (fun i => ‖F i x - c‖) l (𝓝 (0 : ℝ)) := by
    filter_upwards [hpoint] with x hx
    simpa only [sub_self, norm_zero] using
      (hx.sub (tendsto_const_nhds : Tendsto (fun _ : ι => c) l (𝓝 c))).norm
  simpa only [integral_zero] using
    tendsto_integral_filter_of_dominated_convergence (fun _ : X => C + ‖c‖)
      hNmeas hNbound (integrable_const (C + ‖c‖)) hNlim

/-- Integration preserves a unit Lipschitz estimate for the difference
quotient. This turns the centered quantile `L¹` limit into cosine and sine
first-variation identities without differentiating the test functions. -/
theorem integral_lipschitz_difference_quotient_le
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f g : X → ℝ) (ψ : ℝ → ℝ) (t : ℝ)
    (hψ : ∀ x y : ℝ, |ψ x - ψ y| ≤ |x - y|)
    (hfi : Integrable (fun x => ψ (f x)) μ)
    (hgi : Integrable (fun x => ψ (g x)) μ)
    (hdi : Integrable (fun x => (g x - f x) / t) μ) :
    |((∫ x, ψ (g x) ∂μ) - ∫ x, ψ (f x) ∂μ) / t| ≤
      ∫ x, |(g x - f x) / t| ∂μ := by
  rw [← integral_sub hgi hfi, ← integral_div]
  calc
    _ ≤ ∫ x, |(ψ (g x) - ψ (f x)) / t| ∂μ := by
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (fun x => (ψ (g x) - ψ (f x)) / t)
    _ ≤ _ := by
      apply integral_mono ((hgi.sub hfi).div_const t).norm hdi.norm
      intro x
      simp only [Real.norm_eq_abs, abs_div]
      exact div_le_div_of_nonneg_right (hψ (g x) (f x)) (abs_nonneg t)

/-- The right derivative at zero, in the convenient quotient form used by
the quantile and volume-polynomial arguments. -/
theorem hasDerivWithinAt_Ici_zero_iff_div {f : ℝ → ℝ} {c : ℝ}
    (hf0 : f 0 = 0) :
    HasDerivWithinAt f c (Ici 0) 0 ↔
      Tendsto (fun t : ℝ => f t / t) (𝓝[>] 0) (𝓝 c) := by
  have hset : Ici (0 : ℝ) \ {0} = Ioi 0 := by
    ext t
    simp only [Set.mem_sdiff, mem_Ici, mem_singleton_iff, mem_Ioi]
    exact ⟨fun h => lt_of_le_of_ne h.1 (Ne.symm h.2), fun h => ⟨h.le, h.ne'⟩⟩
  have hslope : slope f 0 = (fun t : ℝ => f t / t) := by
    funext t
    simp only [slope_def_field, hf0, sub_zero]
  rw [hasDerivWithinAt_iff_tendsto_slope, hset, hslope]

end RankThreeProjection.QuantileStability
end
end
end DevelopmentSource6

/- Source module: Projection.SupportFunctions. SHA256: 71661acf222112140ed5e6e8c5fef48a41fe5082c1ed602ef3da22d013730b1a -/
section DevelopmentSource7






@[expose] public section
set_option autoImplicit false
noncomputable section

open Set Metric
open scoped Pointwise NNReal

namespace RankThreeProjection
open VolumePolynomials

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Unit functionals; in Euclidean space these are the usual unit normal vectors
under the Riesz isometry. Using the dual avoids a choice of coordinates. -/
abbrev NormalSphere (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  {f : E →L[ℝ] ℝ // ‖f‖ = 1}

namespace Support
open BodySupport

@[simp] theorem point_zero (f : E →L[ℝ] ℝ) :
    support (pointBody (0 : E)) f = 0 := by
  apply le_antisymm
  · apply support_le
    intro x hx
    have hx' : x = 0 := hx
    simp [hx']
  · simpa using le_support (pointBody (0 : E)) f (show (0 : E) ∈ pointBody 0 from rfl)

theorem add (A B : ConvexBody E) (f : E →L[ℝ] ℝ) :
    support (A + B) f = support A f + support B f := by
  apply le_antisymm
  · apply support_le
    rintro _ ⟨x, hx, y, hy, rfl⟩
    rw [map_add]
    exact add_le_add (le_support A f hx) (le_support B f hy)
  · obtain ⟨x, hx, hfx⟩ := exists_support A f
    obtain ⟨y, hy, hfy⟩ := exists_support B f
    simpa only [map_add, hfx, hfy] using
      le_support (A + B) f (Set.add_mem_add hx hy)

theorem smul_body (A : ConvexBody E) (f : E →L[ℝ] ℝ)
    {r : ℝ} (hr : 0 ≤ r) : support (r • A) f = r * support A f := by
  apply le_antisymm
  · apply support_le
    rintro _ ⟨x, hx, rfl⟩
    simpa only [map_smul, smul_eq_mul] using
      mul_le_mul_of_nonneg_left (le_support A f hx) hr
  · obtain ⟨x, hx, hfx⟩ := exists_support A f
    simpa only [map_smul, smul_eq_mul, hfx] using
      le_support (r • A) f (smul_mem_smul_set hx)

theorem smul_functional (A : ConvexBody E) (f : E →L[ℝ] ℝ)
    {r : ℝ} (hr : 0 ≤ r) : support A (r • f) = r * support A f := by
  apply le_antisymm
  · apply support_le
    intro x hx
    exact mul_le_mul_of_nonneg_left (le_support A f hx) hr
  · obtain ⟨x, hx, hfx⟩ := exists_support A f
    simpa only [ContinuousLinearMap.smul_apply, smul_eq_mul, hfx] using
      le_support A (r • f) hx

theorem sub_le (A : ConvexBody E) (f g : E →L[ℝ] ℝ) :
    support A f - support A g ≤ support A (f - g) := by
  obtain ⟨x, hx, hfx⟩ := exists_support A f
  have hg := le_support A g hx
  have hfg := le_support A (f - g) hx
  simp only [ContinuousLinearMap.sub_apply] at hfg
  rw [← hfx]
  linarith

theorem dist_bound (A : ConvexBody E) (f g : E →L[ℝ] ℝ) :
    dist (support A f) (support A g) ≤ dist A (pointBody 0) * dist f g := by
  have hfg := (sub_le A f g).trans
    (support_le_add_norm_mul_dist A (pointBody 0) (f - g))
  have hgf := (sub_le A g f).trans
    (support_le_add_norm_mul_dist A (pointBody 0) (g - f))
  simp only [point_zero, zero_add] at hfg hgf
  rw [norm_sub_rev g f] at hgf
  rw [Real.dist_eq, dist_eq_norm, abs_le]
  constructor <;> nlinarith

theorem continuous_in_functional (A : ConvexBody E) :
    Continuous (fun f : E →L[ℝ] ℝ => support A f) := by
  apply LipschitzWith.continuous (K := ⟨dist A (pointBody 0), dist_nonneg⟩)
  exact LipschitzWith.of_dist_le_mul (dist_bound A)

end Support

/-- The support function of an actual body, restricted to unit functionals. -/
def supportContinuous (A : ConvexBody E) : C(NormalSphere E, ℝ) where
  toFun u := BodySupport.support A u.val
  continuous_toFun := (Support.continuous_in_functional A).comp continuous_subtype_val

@[simp] theorem supportContinuous_apply (A : ConvexBody E) (u : NormalSphere E) :
    supportContinuous A u = BodySupport.support A u.val := rfl

@[simp] theorem supportContinuous_zero :
    supportContinuous (0 : ConvexBody E) = 0 := by
  ext u
  exact Support.point_zero u.val

@[simp] theorem supportContinuous_add (A B : ConvexBody E) :
    supportContinuous (A + B) = supportContinuous A + supportContinuous B := by
  ext u
  exact Support.add A B u.val

@[simp] theorem supportContinuous_smul (r : ℝ≥0) (A : ConvexBody E) :
    supportContinuous (r • A) = r • supportContinuous A := by
  ext u
  exact Support.smul_body A u.val r.property

/-- Support functions preserve addition and nonnegative homogeneity. -/
def supportLinear : ConvexBody E →ₗ[ℝ≥0] C(NormalSphere E, ℝ) where
  toFun := supportContinuous
  map_add' := supportContinuous_add
  map_smul' := supportContinuous_smul

theorem supportContinuous_mono {A B : ConvexBody E} (hAB : A ≤ B) :
    supportContinuous A ≤ supportContinuous B := by
  intro u
  exact BodySupport.support_le A u.val
    (fun x hx => BodySupport.le_support B u.val (hAB hx))

/-- Unit normal values retain the entire body, including degenerate bodies. -/
theorem le_of_supportContinuous_le {A B : ConvexBody E}
    (hAB : supportContinuous A ≤ supportContinuous B) : A ≤ B := by
  intro x hx
  apply BodySupport.mem_iff_le_support B |>.mpr
  intro f
  by_cases hf : f = 0
  · subst f
    have hzero : BodySupport.support B (0 : E →L[ℝ] ℝ) = 0 := by
      apply le_antisymm
      · exact BodySupport.support_le B 0 (fun _ _ => le_rfl)
      · obtain ⟨y, hy⟩ := B.nonempty
        exact BodySupport.le_support B 0 hy
    simp [hzero]
  · have hnorm : 0 < ‖f‖ := norm_pos_iff.mpr hf
    let u : NormalSphere E := ⟨‖f‖⁻¹ • f, by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnorm)]
      exact inv_mul_cancel₀ hnorm.ne'⟩
    have hu : ‖f‖ • u.val = f := by
      simp only [u, smul_smul, mul_inv_cancel₀ hnorm.ne', one_smul]
    have hs := (BodySupport.le_support A u.val hx).trans (hAB u)
    have hs' := mul_le_mul_of_nonneg_left hs hnorm.le
    change ‖f‖ * u.val x ≤ ‖f‖ * BodySupport.support B u.val at hs'
    calc
      f x = ‖f‖ * u.val x := by
        simpa only [ContinuousLinearMap.smul_apply, smul_eq_mul] using
          (congrArg (fun g : E →L[ℝ] ℝ => g x) hu).symm
      _ ≤ ‖f‖ * BodySupport.support B u.val := hs'
      _ = BodySupport.support B f := by
        rw [← Support.smul_functional B u.val hnorm.le, hu]

theorem supportContinuous_injective :
    Function.Injective (supportContinuous (E := E)) := by
  intro A B h
  exact le_antisymm (le_of_supportContinuous_le h.le)
    (le_of_supportContinuous_le h.symm.le)

section FiniteDimension
variable [FiniteDimensional ℝ E]

instance normalSphereCompact : CompactSpace (NormalSphere E) := by
  have heq : {f : E →L[ℝ] ℝ | ‖f‖ = 1} = Metric.sphere 0 1 := by
    ext f
    simp [Metric.mem_sphere, dist_zero_right]
  exact isCompact_iff_compactSpace.mp (heq ▸ isCompact_sphere (0 : E →L[ℝ] ℝ) 1)

/-- The actual closed unit ball, as a compact convex body. -/
def unitBall : ConvexBody E where
  carrier := closedBall 0 1
  convex' := convex_closedBall (0 : E) 1
  isCompact' := isCompact_closedBall 0 1
  nonempty' := ⟨0, by simp⟩

set_option backward.isDefEq.respectTransparency false in
theorem supportContinuous_unitBall :
    supportContinuous (unitBall (E := E)) = 1 := by
  ext u
  simp only [supportContinuous_apply, ContinuousMap.one_apply]
  apply le_antisymm
  · apply BodySupport.support_le
    intro x hx
    change x ∈ closedBall (0 : E) 1 at hx
    have hx' : ‖x‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    calc
      u.val x ≤ ‖u.val x‖ := le_abs_self _
      _ ≤ ‖u.val‖ * ‖x‖ := u.val.le_opNorm x
      _ ≤ 1 := by simpa only [u.property, one_mul] using hx'
  · have hm := BodySupport.support_margin_of_closedBall_subset
      (unitBall (E := E)) zero_lt_one (Subset.rfl) u.val
    simpa only [map_zero, zero_add, one_mul, u.property] using hm

end FiniteDimension
end RankThreeProjection
end
end
end DevelopmentSource7

/- Source module: Projection.PositiveRepresentation. SHA256: a0f7c825625d8272f31ffbdc18d4ef667a606d2118089d21e7579775ff08cabe -/
section DevelopmentSource8









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
end
end
end DevelopmentSource8

/- Source module: Projection.SupportDensity. SHA256: 8cd5a61cfceb669b91f6ac6a6988fa64be20b3a1ab5e0f1081799cd0d75336f5 -/
section DevelopmentSource9









@[expose] public section
set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory
open scoped Pointwise NNReal Topology

namespace RankThreeProjection
open VolumePolynomials

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem convexJoin_eq_image (A B : ConvexBody E) :
    convexJoin ℝ (A : Set E) (B : Set E) =
      (fun p : ℝ × E × E => (1 - p.1) • p.2.1 + p.1 • p.2.2) ''
        (Icc (0 : ℝ) 1 ×ˢ ((A : Set E) ×ˢ (B : Set E))) := by
  ext z
  constructor
  · intro hz
    obtain ⟨a, ha, b, hb, hz⟩ := mem_convexJoin.mp hz
    rw [segment_eq_image] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    exact ⟨(t, a, b), ⟨ht, ha, hb⟩, rfl⟩
  · rintro ⟨⟨t, a, b⟩, ⟨ht, ha, hb⟩, rfl⟩
    apply mem_convexJoin.mpr
    refine ⟨a, ha, b, hb, ?_⟩
    rw [segment_eq_image]
    exact ⟨t, ht, rfl⟩

/-- The convex hull of the union of two actual compact convex bodies. -/
def joinBody (A B : ConvexBody E) : ConvexBody E where
  carrier := convexJoin ℝ (A : Set E) (B : Set E)
  convex' := A.convex.convexJoin B.convex
  isCompact' := by
    rw [convexJoin_eq_image]
    exact (isCompact_Icc.prod (A.isCompact.prod B.isCompact)).image (by fun_prop)
  nonempty' := A.nonempty.mono (subset_convexJoin_left B.nonempty)

theorem supportContinuous_join (A B : ConvexBody E) :
    supportContinuous (joinBody A B) = supportContinuous A ⊔ supportContinuous B := by
  ext u
  change BodySupport.support (joinBody A B) u.val =
    max (BodySupport.support A u.val) (BodySupport.support B u.val)
  apply le_antisymm
  · apply BodySupport.support_le
    intro z hz
    obtain ⟨a, ha, b, hb, r, t, hr, ht, hrt, rfl⟩ := mem_convexJoin.mp hz
    rw [map_add, map_smul, map_smul]
    change r * u.val a + t * u.val b ≤ _
    have ha' := (BodySupport.le_support A u.val ha).trans
      (le_max_left (BodySupport.support A u.val) (BodySupport.support B u.val))
    have hb' := (BodySupport.le_support B u.val hb).trans
      (le_max_right (BodySupport.support A u.val) (BodySupport.support B u.val))
    calc
      _ ≤ r * max (BodySupport.support A u.val) (BodySupport.support B u.val) +
          t * max (BodySupport.support A u.val) (BodySupport.support B u.val) :=
        add_le_add (mul_le_mul_of_nonneg_left ha' hr) (mul_le_mul_of_nonneg_left hb' ht)
      _ = _ := by rw [← add_mul, hrt, one_mul]
  · apply max_le
    · exact supportContinuous_mono (subset_convexJoin_left B.nonempty) u
    · exact supportContinuous_mono (subset_convexJoin_right A.nonempty) u

@[simp] theorem supportContinuous_point (v : E) (u : NormalSphere E) :
    supportContinuous (pointBody v) u = u.val v := by
  apply le_antisymm
  · apply BodySupport.support_le
    intro x hx
    have hx' : x = v := hx
    simp [hx']
  · exact BodySupport.le_support (pointBody v) u.val (show v ∈ pointBody v from rfl)

variable [FiniteDimensional ℝ E]

abbrev SupportSpace := PositiveRepresentation.differenceSpace (supportLinear (E := E))

private theorem max_difference (a b c d : ℝ) :
    max (a - b) (c - d) = max (a + d) (c + b) - (b + d) := by
  rcases le_total (a - b) (c - d) with h | h
  · rw [max_eq_right h, max_eq_right (by linarith : a + d ≤ c + b)]
    ring
  · rw [max_eq_left h, max_eq_left (by linarith : c + b ≤ a + d)]
    ring

theorem supportSpace_sup {f g : C(NormalSphere E, ℝ)}
    (hf : f ∈ SupportSpace (E := E)) (hg : g ∈ SupportSpace (E := E)) :
    f ⊔ g ∈ SupportSpace (E := E) := by
  obtain ⟨a, b, rfl⟩ := hf
  obtain ⟨c, d, rfl⟩ := hg
  refine ⟨joinBody (a + d) (c + b), b + d, ?_⟩
  change (supportContinuous a - supportContinuous b) ⊔
      (supportContinuous c - supportContinuous d) =
    supportContinuous (joinBody (a + d) (c + b)) - supportContinuous (b + d)
  simp only [supportContinuous_join, supportContinuous_add]
  ext u
  simp only [ContinuousMap.sub_apply, ContinuousMap.add_apply, ContinuousMap.sup_apply]
  exact max_difference _ _ _ _

theorem supportSpace_inf {f g : C(NormalSphere E, ℝ)}
    (hf : f ∈ SupportSpace (E := E)) (hg : g ∈ SupportSpace (E := E)) :
    f ⊓ g ∈ SupportSpace (E := E) := by
  have hs := supportSpace_sup ((SupportSpace (E := E)).neg_mem hf)
    ((SupportSpace (E := E)).neg_mem hg)
  have hn := (SupportSpace (E := E)).neg_mem hs
  simpa only [neg_sup, neg_neg] using hn

theorem one_mem_supportSpace : (1 : C(NormalSphere E, ℝ)) ∈ SupportSpace (E := E) :=
  ⟨unitBall, 0, by simp [supportLinear, supportContinuous_unitBall]⟩

private theorem supportSpace_strongly_separates :
    (SupportSpace (E := E) : Set C(NormalSphere E, ℝ)).SeparatesPointsStrongly := by
  intro v x y
  by_cases hxy : x = y
  · subst y
    refine ⟨v x • (1 : C(NormalSphere E, ℝ)),
      (SupportSpace (E := E)).smul_mem (v x) one_mem_supportSpace, ?_, ?_⟩ <;> simp
  · have hvals : x.val ≠ y.val := fun h => hxy (Subtype.ext h)
    obtain ⟨z, hz⟩ : ∃ z : E, x.val z ≠ y.val z := by
      by_contra hn
      push_neg at hn
      exact hvals (ContinuousLinearMap.ext hn)
    let f := supportContinuous (pointBody z)
    have hf : f ∈ SupportSpace (E := E) := ⟨pointBody z, 0, by simp [f, supportLinear]⟩
    have hdiff : f x - f y ≠ 0 := by
      simpa only [f, supportContinuous_point] using sub_ne_zero.mpr hz
    let c := (v y - v x) * (f x - f y)⁻¹
    let g : C(NormalSphere E, ℝ) := c • (f x • 1 - f) + v x • 1
    have hg : g ∈ SupportSpace (E := E) :=
      (SupportSpace (E := E)).add_mem
        ((SupportSpace (E := E)).smul_mem c
          ((SupportSpace (E := E)).sub_mem
            ((SupportSpace (E := E)).smul_mem (f x) one_mem_supportSpace) hf))
        ((SupportSpace (E := E)).smul_mem (v x) one_mem_supportSpace)
    refine ⟨g, hg, ?_, ?_⟩
    · simp [g]
    · simp [g, c, mul_assoc, inv_mul_cancel₀ hdiff]

/-- Differences of genuine support functions are uniformly dense among
continuous functions on the normal sphere. Smoothness is unnecessary here. -/
theorem dense_support_differences :
    Dense (PositiveRepresentation.differenceSpace (supportLinear (E := E)) :
      Set C(NormalSphere E, ℝ)) := by
  rw [dense_iff_closure_eq]
  exact ContinuousMap.sublattice_closure_eq_top _ ⟨0, (SupportSpace (E := E)).zero_mem⟩
    (fun _ hf _ hg => supportSpace_inf hf hg)
    (fun _ hf _ hg => supportSpace_sup hf hg) supportSpace_strongly_separates

section Measures
variable [MeasurableSpace (NormalSphere E)] [BorelSpace (NormalSphere E)]

/-- Integration on a compact space as a bounded linear functional. -/
def continuousIntegral (μ : Measure (NormalSphere E)) [IsFiniteMeasure μ] :
    C(NormalSphere E, ℝ) →L[ℝ] ℝ :=
  ({ toFun := fun f => ∫ x, f x ∂μ
     map_add' := by
       intro f g
       exact integral_add ((BoundedContinuousFunction.mkOfCompact f).integrable μ)
         ((BoundedContinuousFunction.mkOfCompact g).integrable μ)
     map_smul' := by
       intro r f
       exact integral_smul r f } : C(NormalSphere E, ℝ) →ₗ[ℝ] ℝ).mkContinuous
    (μ.real univ) (fun f => (BoundedContinuousFunction.mkOfCompact f).norm_integral_le_mul_norm μ)

/-- A finite Borel measure is determined by its integrals against actual
support functions, rather than by a stipulated uniqueness field. -/
theorem measure_eq_of_support_integrals
    (μ ν : Measure (NormalSphere E)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ A : ConvexBody E,
      (∫ u, supportContinuous A u ∂μ) = ∫ u, supportContinuous A u ∂ν) : μ = ν := by
  have hclosed : IsClosed {f : C(NormalSphere E, ℝ) |
      continuousIntegral μ f = continuousIntegral ν f} :=
    isClosed_eq (continuousIntegral μ).continuous (continuousIntegral ν).continuous
  have hsub : (PositiveRepresentation.differenceSpace (supportLinear (E := E)) :
      Set C(NormalSphere E, ℝ)) ⊆ {f | continuousIntegral μ f = continuousIntegral ν f} := by
    rintro f ⟨A, B, rfl⟩
    change (∫ u, supportContinuous A u - supportContinuous B u ∂μ) =
      ∫ u, supportContinuous A u - supportContinuous B u ∂ν
    calc
      _ = (∫ u, supportContinuous A u ∂μ) - ∫ u, supportContinuous B u ∂μ :=
        integral_sub ((BoundedContinuousFunction.mkOfCompact (supportContinuous A)).integrable μ)
          ((BoundedContinuousFunction.mkOfCompact (supportContinuous B)).integrable μ)
      _ = (∫ u, supportContinuous A u ∂ν) - ∫ u, supportContinuous B u ∂ν :=
        congrArg₂ (· - ·) (h A) (h B)
      _ = _ :=
        (integral_sub ((BoundedContinuousFunction.mkOfCompact (supportContinuous A)).integrable ν)
          ((BoundedContinuousFunction.mkOfCompact (supportContinuous B)).integrable ν)).symm
  have hall : ∀ f : C(NormalSphere E, ℝ),
      continuousIntegral μ f = continuousIntegral ν f := by
    intro f
    exact closure_minimal hsub hclosed (dense_support_differences f)
  have heq : (⟨μ, inferInstance⟩ : FiniteMeasure (NormalSphere E)) = ⟨ν, inferInstance⟩ := by
    apply FiniteMeasure.ext_of_forall_integral_eq
    intro f
    exact hall f.toContinuousMap
  exact congrArg Subtype.val heq

end Measures
end RankThreeProjection
end
end
end DevelopmentSource9

/- Source module: Projection.MixedArea. SHA256: ce4d035293151da9171573779be4c290db96747ef771c7d37b2bf04d1849fe1f -/
section DevelopmentSource10





@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory Module
open scoped NNReal Pointwise

namespace RankThreeProjection
open VolumePolynomials

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

instance normalSphereMeasurableSpace : MeasurableSpace (NormalSphere E) :=
  borel (NormalSphere E)

instance normalSphereBorelSpace : BorelSpace (NormalSphere E) := ⟨rfl⟩

variable [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

/-- The first mixed-volume slot, with the usual area-measure normalization. -/
def mixedFirstLinear {d : ℕ} (K : Fin d → ConvexBody E) : ConvexBody E →ₗ[ℝ≥0] ℝ :=
  (d + 1 : ℝ≥0) •
    (mixedVolumeMultilinear μ (d + 1)).toLinearMap (Fin.cons 0 K) 0

@[simp] theorem mixedFirstLinear_apply {d : ℕ} (K : Fin d → ConvexBody E) (A : ConvexBody E) :
    mixedFirstLinear μ K A = (d + 1 : ℝ) * mixedVolume μ (Fin.cons A K) := by
  have ht : Function.update
      (Fin.cons (0 : ConvexBody E) K : Fin (d + 1) → ConvexBody E) 0 A =
      (Fin.cons A K : Fin (d + 1) → ConvexBody E) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  simp only [mixedFirstLinear, LinearMap.smul_apply, MultilinearMap.toLinearMap_apply,
    mixedVolumeMultilinear_apply, ht]
  rfl

theorem mixedFirstLinear_monotone {d : ℕ} (K : Fin d → ConvexBody E)
    (hdim : finrank ℝ E = d + 1) (A B : ConvexBody E)
    (hAB : supportLinear A ≤ supportLinear B) :
    mixedFirstLinear μ K A ≤ mixedFirstLinear μ K B := by
  rw [mixedFirstLinear_apply, mixedFirstLinear_apply]
  exact mul_le_mul_of_nonneg_left
    (mixedVolume_mono_first_all μ K hdim A B (le_of_supportContinuous_le hAB))
    (by positivity)

/-- Existence of the actual mixed area measure, proved from monotonicity,
support functions, Hahn–Banach, and Riesz representation. -/
theorem exists_mixedAreaMeasure {d : ℕ} (K : Fin d → ConvexBody E)
    (hdim : finrank ℝ E = d + 1) :
    ∃ ν : Measure (NormalSphere E), IsFiniteMeasure ν ∧
      ∀ A : ConvexBody E,
        (∫ u, supportContinuous A u ∂ν) =
          (d + 1 : ℝ) * mixedVolume μ (Fin.cons A K) := by
  obtain ⟨ν, hν, hrep⟩ := PositiveRepresentation.exists_representing_measure
    (supportLinear (E := E)) (mixedFirstLinear μ K)
    (mixedFirstLinear_monotone μ K hdim) unitBall supportContinuous_unitBall
  refine ⟨ν, hν, ?_⟩
  intro A
  exact (hrep A).trans (mixedFirstLinear_apply μ K A)

/-- The unique positive mixed area measure of the background tuple. -/
def mixedAreaMeasure {d : ℕ} (K : Fin d → ConvexBody E)
    (hdim : finrank ℝ E = d + 1) : Measure (NormalSphere E) :=
  (exists_mixedAreaMeasure μ K hdim).choose

instance mixedAreaMeasure_finite {d : ℕ} (K : Fin d → ConvexBody E)
    (hdim : finrank ℝ E = d + 1) : IsFiniteMeasure (mixedAreaMeasure μ K hdim) :=
  (exists_mixedAreaMeasure μ K hdim).choose_spec.1

theorem mixedAreaMeasure_integral {d : ℕ} (K : Fin d → ConvexBody E)
    (hdim : finrank ℝ E = d + 1) (A : ConvexBody E) :
    (∫ u, supportContinuous A u ∂mixedAreaMeasure μ K hdim) =
      (d + 1 : ℝ) * mixedVolume μ (Fin.cons A K) :=
  (exists_mixedAreaMeasure μ K hdim).choose_spec.2 A

theorem mixedAreaMeasure_unique {d : ℕ} (K : Fin d → ConvexBody E)
    (hdim : finrank ℝ E = d + 1) (ν : Measure (NormalSphere E)) [IsFiniteMeasure ν]
    (hν : ∀ A : ConvexBody E, (∫ u, supportContinuous A u ∂ν) =
      (d + 1 : ℝ) * mixedVolume μ (Fin.cons A K)) :
    ν = mixedAreaMeasure μ K hdim := by
  apply measure_eq_of_support_integrals
  intro A
  exact (hν A).trans (mixedAreaMeasure_integral μ K hdim A).symm

theorem mixedVolume_point_first {d : ℕ} (K : Fin d → ConvexBody E) (v : E) :
    mixedVolume μ (Fin.cons (pointBody v) K) = 0 := by
  have ht : (fun i : Fin (d + 1) => translateBody
      ((Fin.cons v (fun _ : Fin d => 0) : Fin (d + 1) → E) i)
      ((Fin.cons (0 : ConvexBody E) K : Fin (d + 1) → ConvexBody E) i)) =
      (Fin.cons (pointBody v) K : Fin (d + 1) → ConvexBody E) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero]
      apply ConvexBody.ext
      ext x
      simp [coe_translateBody, ConvexBody.coe_zero, pointBody, Set.mem_vadd_set,
        vadd_eq_add, eq_comm]
    · simp only [Fin.cons_succ, translateBody_zero]
  have htrans := mixedVolume_translate μ (Fin.cons (0 : ConvexBody E) K)
    (Fin.cons v (fun _ : Fin d => 0))
  rw [ht] at htrans
  have hz := mixedVolume_zero_arg μ (Fin.cons (0 : ConvexBody E) K) 0
  have hu : Function.update
      (Fin.cons (0 : ConvexBody E) K : Fin (d + 1) → ConvexBody E) 0 0 =
      (Fin.cons (0 : ConvexBody E) K : Fin (d + 1) → ConvexBody E) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  rw [hu] at hz
  exact htrans.trans hz

/-- Every linear first moment of the mixed area measure vanishes. -/
theorem mixedAreaMeasure_centered {d : ℕ} (K : Fin d → ConvexBody E)
    (hdim : finrank ℝ E = d + 1) (v : E) :
    (∫ u, u.val v ∂mixedAreaMeasure μ K hdim) = 0 := by
  have h := mixedAreaMeasure_integral μ K hdim (pointBody v)
  simpa only [supportContinuous_point, mixedVolume_point_first, mul_zero] using h

end RankThreeProjection
end
end
end DevelopmentSource10

/- Source module: VolumeVerification.AFPairingEquality. SHA256: 2a3a27db1ea3fb17c5dc0ef63de0555f080c7b7c5bce79b171ede1527d66b61d -/
section DevelopmentSource11




@[expose] public section
set_option autoImplicit false

/-!
# The pairing consequence of equality in Alexandrov–Fenchel

The first result is an elementary one-sided derivative argument for a
quadratic polynomial, proved using an explicit positive test value.  The
second applies it to a symmetric Minkowski-bilinear pairing.  No assertion
about support functions, area measures, or equality rigidity is assumed.
-/
namespace VolumeVerification.AFPairingEquality

theorem linear_coefficient_nonnegative (u v : ℝ)
    (h : ∀ s : ℝ, 0 ≤ s → 0 ≤ u * s + v * s ^ 2) : 0 ≤ u := by
  by_contra hu
  have hu' : u < 0 := lt_of_not_ge hu
  have hd : 0 < |v| + 1 := add_pos_of_nonneg_of_pos (abs_nonneg v) zero_lt_one
  let s : ℝ := -u / (|v| + 1)
  have hs : 0 < s := div_pos (neg_pos.mpr hu') hd
  have he : s * (|v| + 1) = -u := div_mul_cancel₀ _ hd.ne'
  have he' := congrArg (fun x : ℝ => x * s) he
  have hv : v * s ^ 2 ≤ |v| * s ^ 2 :=
    mul_le_mul_of_nonneg_right (le_abs_self v) (sq_nonneg s)
  have hpoly := h s hs.le
  nlinarith [sq_pos_of_pos hs]

/-- A real affine function nonnegative on the whole positive half-line has
nonnegative slope. This is used with an actual AF discriminant. -/
theorem affine_coefficient_nonnegative (c u : ℝ)
    (h : ∀ s : ℝ, 0 ≤ s → 0 ≤ c + u * s) : 0 ≤ u := by
  apply linear_coefficient_nonnegative u c
  intro t ht
  by_cases ht0 : t = 0
  · simp [ht0]
  have hp := mul_nonneg (h t⁻¹ (inv_nonneg.mpr ht)) (sq_nonneg t)
  have he : (c + u * t⁻¹) * t ^ 2 = u * t + c * t ^ 2 := by
    calc
      _ = c * t ^ 2 + u * (t⁻¹ * t) * t := by ring
      _ = _ := by rw [inv_mul_cancel₀ ht0]; ring
  rwa [he] at hp

/-- The scalar step for convex-hull rigidity. If two bodies have equal
pairings against a positive reference, and their difference is null, AF
applied after unequal positive additions of that reference fixes their
remaining pairing. The displayed inequality is exactly that expansion. -/
theorem pairing_le_of_shifted_AF (a b m k : ℝ) (hk : 0 < k)
    (haf : ∀ s : ℝ, 0 ≤ s →
      ((2 * b - a) + 2 * s * m + s ^ 2 * k) *
          (a + 2 * (s + 1) * m + (s + 1) ^ 2 * k) ≤
        (b + (2 * s + 1) * m + s * (s + 1) * k) ^ 2) : b ≤ a := by
  have hslope := affine_coefficient_nonnegative
    ((b - a - m) ^ 2 - a * k - 2 * k * (b - a)) (-2 * k * (b - a))
    (fun s hs => by
      have he :
          ((b - a - m) ^ 2 - a * k - 2 * k * (b - a)) +
              (-2 * k * (b - a)) * s =
            (b + (2 * s + 1) * m + s * (s + 1) * k) ^ 2 -
              (((2 * b - a) + 2 * s * m + s ^ 2 * k) *
                (a + 2 * (s + 1) * m + (s + 1) ^ 2 * k)) := by ring
      rw [he]
      exact sub_nonneg.mpr (haf s hs))
  have hm : k * (b - a) ≤ 0 := by linarith
  exact sub_nonpos.mp (nonpos_of_mul_nonpos_right hm hk)

theorem pairing_le_of_quadratic_inequalities (a b c d : ℝ) (ha : 0 < a)
    (h : ∀ s : ℝ, 0 ≤ s →
      a * (a + 2 * s * b + s ^ 2 * d) ≤ (a + s * c) ^ 2) : b ≤ c := by
  have hc := linear_coefficient_nonnegative (2 * a * (c - b)) (c ^ 2 - a * d)
    (fun s hs => by
      have he : (2 * a * (c - b)) * s + (c ^ 2 - a * d) * s ^ 2 =
          (a + s * c) ^ 2 - a * (a + 2 * s * b + s ^ 2 * d) := by ring
      rw [he]
      exact sub_nonneg.mpr (h s hs))
  have htwo : 0 < 2 * a := mul_pos zero_lt_two ha
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left htwo).mp hc)

/-- Equality at a positive self-pairing forces equality against every test
object.  The assumptions are the usual symmetry, additivity, nonnegative
homogeneity, and Alexandrov–Fenchel inequality of the pairing itself. -/
theorem equality_of_equal_positive_pairings
    {C : Type*} [Add C] [SMul ℝ C]
    (q : C → C → ℝ)
    (hsymm : ∀ A B, q A B = q B A)
    (hadd : ∀ A B T, q (A + B) T = q A T + q B T)
    (hsmul : ∀ (r : ℝ), 0 ≤ r → ∀ A T, q (r • A) T = r * q A T)
    (haf : ∀ A B, q A A * q B B ≤ q A B ^ 2)
    (A B : C) (a : ℝ) (ha : 0 < a)
    (hAA : q A A = a) (hAB : q A B = a) (hBB : q B B = a) :
    ∀ T, q A T = q B T := by
  have hadd_right (X Y Z : C) : q X (Y + Z) = q X Y + q X Z := by
    rw [hsymm X (Y + Z), hadd Y Z X, hsymm Y X, hsymm Z X]
  have hsmul_right (r : ℝ) (hr : 0 ≤ r) (X Y : C) :
      q X (r • Y) = r * q X Y := by
    rw [hsymm X (r • Y), hsmul r hr Y X, hsymm Y X]
  have step (X Y : C) (hXX : q X X = a) (hXY : q X Y = a)
      (hYY : q Y Y = a) (T : C) : q X T ≤ q Y T := by
    apply pairing_le_of_quadratic_inequalities a (q X T) (q Y T) (q T T) ha
    intro s hs
    have hself : q (X + s • T) (X + s • T) =
        a + 2 * s * q X T + s ^ 2 * q T T := by
      rw [hadd, hadd_right, hadd_right, hsmul s hs, hsmul s hs,
        hsmul_right s hs, hsmul_right s hs, hXX, hsymm T X]
      ring
    have hcross : q (X + s • T) Y = a + s * q Y T := by
      rw [hadd, hsmul s hs, hXY, hsymm T Y]
    have h := haf (X + s • T) Y
    rw [hself, hcross, hYY] at h
    simpa only [mul_comm] using h
  intro T
  exact le_antisymm (step A B hAA hAB hBB T)
    (step B A hBB ((hsymm B A).trans hAB) hAA T)

/-- Algebraic amplification from a weak equality to equality for the convex
hull. The only additional input about the hull `D` is its proved quadratic
valuation identity and monotonicity. The geometric application supplies both
from actual convex bodies. -/
theorem hull_pairings_of_weak_equality
    {C : Type*} [Add C] [SMul ℝ C]
    (q : C → C → ℝ)
    (hsymm : ∀ A B, q A B = q B A)
    (hadd : ∀ A B T, q (A + B) T = q A T + q B T)
    (hsmul : ∀ (r : ℝ), 0 ≤ r → ∀ A T, q (r • A) T = r * q A T)
    (haf : ∀ A B, q A A * q B B ≤ q A B ^ 2)
    (A B D H : C) (a : ℝ) (ha : 0 < a)
    (hAA : q A A = a) (hAB : q A B = a) (hBB : q B B = a)
    (hval : q D D + q A B = q D A + q D B)
    (hmono : a ≤ q D A) (hHH : 0 < q H H)
    (hweak : q D H = q A H) : ∀ T, q D T = q A T := by
  have hadd_right (X Y Z : C) : q X (Y + Z) = q X Y + q X Z := by
    rw [hsymm X (Y + Z), hadd Y Z X, hsymm Y X, hsymm Z X]
  have hsmul_right (r : ℝ) (hr : 0 ≤ r) (X Y : C) :
      q X (r • Y) = r * q X Y := by
    rw [hsymm X (r • Y), hsmul r hr Y X, hsymm Y X]
  have hexpand (X Y Z W : C) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
      q (X + s • Z) (Y + t • W) =
        q X Y + t * q X W + s * q Z Y + s * t * q Z W := by
    rw [hadd, hadd_right, hadd_right, hsmul s hs, hsmul s hs,
      hsmul_right t ht, hsmul_right t ht]
    ring
  have hABall := equality_of_equal_positive_pairings q hsymm hadd hsmul haf
    A B a ha hAA hAB hBB
  have hDB : q D B = q D A := by
    rw [hsymm D B, ← hABall D, hsymm A D]
  have hDD : q D D = 2 * q D A - a := by
    rw [hAB, hDB] at hval
    linarith
  have hDAle : q D A ≤ a := by
    apply pairing_le_of_shifted_AF a (q D A) (q A H) (q H H) hHH
    intro s hs
    have hs1 : 0 ≤ s + 1 := by linarith
    have h := haf (D + s • H) (A + (s + 1) • H)
    rw [hexpand D D H H s s hs hs,
      hexpand A A H H (s + 1) (s + 1) hs1 hs1,
      hexpand D A H H s (s + 1) hs hs1] at h
    rw [hsymm H D, hsymm H A, hDD, hAA, hweak] at h
    convert h using 1 <;> ring
  have hDA : q D A = a := le_antisymm hDAle hmono
  have hDD' : q D D = a := by rw [hDD, hDA]; ring
  exact equality_of_equal_positive_pairings q hsymm hadd hsmul haf
    D A a ha hDD' hDA hAA

end VolumeVerification.AFPairingEquality
end
end DevelopmentSource11

/- Source module: VolumeVerification.PositiveHollowKernel. SHA256: a0a835e55dca7a4cb0fc88fe94a90ff3aa420ff77b2d4a88b3f4292f9e754076 -/
section DevelopmentSource12







@[expose] public section
set_option autoImplicit false

/-!
# Sign structure of a positive hollow matrix kernel

Every nonzero kernel vector has at least two positive coordinates and at
least two negative coordinates.  Its positive and negative parts have equal
positive self- and cross-pairings.  No rank condition is needed for these
facts; they are the linear algebra used for the two zonotopes in Proposition
4.2 of the projection-volume paper.
-/
namespace VolumeVerification.PositiveHollowKernel
open scoped BigOperators Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]

theorem entries_nonnegative (P : Matrix ι ι ℝ)
    (hdiag : ∀ i, P i i = 0) (hpos : ∀ i j, i ≠ j → 0 < P i j) :
    ∀ i j, 0 ≤ P i j := by
  intro i j
  by_cases hij : i = j
  · subst j
    rw [hdiag]
  · exact (hpos i j hij).le

theorem exists_positive (P : Matrix ι ι ℝ)
    (hdiag : ∀ i, P i i = 0) (hpos : ∀ i j, i ≠ j → 0 < P i j)
    (w : ι → ℝ) (hw : P *ᵥ w = 0) (hne : w ≠ 0) :
    ∃ i, 0 < w i := by
  classical
  by_contra hex
  have hnonpos : ∀ i, w i ≤ 0 := by
    intro i
    exact le_of_not_gt (fun hi => hex ⟨i, hi⟩)
  obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
    by_contra hj
    push_neg at hj
    exact hne (funext hj)
  have hjneg : w j < 0 := lt_of_le_of_ne (hnonpos j) hj
  obtain ⟨i, hij⟩ := exists_ne j
  have hsum : (∑ k, P i k * w k) < 0 := by
    apply Finset.sum_neg'
    · intro k _
      exact mul_nonpos_of_nonneg_of_nonpos
        (entries_nonnegative P hdiag hpos i k) (hnonpos k)
    · exact ⟨j, Finset.mem_univ j, mul_neg_of_pos_of_neg (hpos i j hij) hjneg⟩
  have hzero : (∑ k, P i k * w k) = 0 := congrFun hw i
  linarith

theorem exists_negative (P : Matrix ι ι ℝ)
    (hdiag : ∀ i, P i i = 0) (hpos : ∀ i j, i ≠ j → 0 < P i j)
    (w : ι → ℝ) (hw : P *ᵥ w = 0) (hne : w ≠ 0) :
    ∃ i, w i < 0 := by
  have hker : P *ᵥ (-w) = 0 := by rw [Matrix.mulVec_neg, hw, neg_zero]
  obtain ⟨i, hi⟩ := exists_positive P hdiag hpos (-w) hker (neg_ne_zero.mpr hne)
  exact ⟨i, neg_pos.mp hi⟩

theorem exists_two_positive (P : Matrix ι ι ℝ)
    (hdiag : ∀ i, P i i = 0) (hpos : ∀ i j, i ≠ j → 0 < P i j)
    (w : ι → ℝ) (hw : P *ᵥ w = 0) (hne : w ≠ 0) :
    ∃ i j, i ≠ j ∧ 0 < w i ∧ 0 < w j := by
  obtain ⟨i, hi⟩ := exists_positive P hdiag hpos w hw hne
  obtain ⟨k, hk⟩ := exists_negative P hdiag hpos w hw hne
  have hik : i ≠ k := by
    intro h
    subst k
    linarith
  by_contra hex
  have hnonpos : ∀ j, j ≠ i → w j ≤ 0 := by
    intro j hji
    exact le_of_not_gt (fun hj => hex ⟨i, j, Ne.symm hji, hi, hj⟩)
  have hsum : (∑ j, P i j * w j) < 0 := by
    apply Finset.sum_neg'
    · intro j _
      by_cases hji : j = i
      · subst j
        rw [hdiag, zero_mul]
      · exact mul_nonpos_of_nonneg_of_nonpos
          (entries_nonnegative P hdiag hpos i j) (hnonpos j hji)
    · exact ⟨k, Finset.mem_univ k, mul_neg_of_pos_of_neg (hpos i k hik) hk⟩
  have hzero : (∑ j, P i j * w j) = 0 := congrFun hw i
  linarith

theorem exists_two_negative (P : Matrix ι ι ℝ)
    (hdiag : ∀ i, P i i = 0) (hpos : ∀ i j, i ≠ j → 0 < P i j)
    (w : ι → ℝ) (hw : P *ᵥ w = 0) (hne : w ≠ 0) :
    ∃ i j, i ≠ j ∧ w i < 0 ∧ w j < 0 := by
  have hker : P *ᵥ (-w) = 0 := by rw [Matrix.mulVec_neg, hw, neg_zero]
  obtain ⟨i, j, hij, hi, hj⟩ :=
    exists_two_positive P hdiag hpos (-w) hker (neg_ne_zero.mpr hne)
  exact ⟨i, j, hij, neg_pos.mp hi, neg_pos.mp hj⟩

def positivePart (w : ι → ℝ) : ι → ℝ := fun i => max (w i) 0

def negativePart (w : ι → ℝ) : ι → ℝ := fun i => max (-w i) 0

theorem positivePart_sub_negativePart (w : ι → ℝ) :
    positivePart w - negativePart w = w := by
  funext i
  change max (w i) 0 - max (-w i) 0 = w i
  rcases le_total 0 (w i) with hi | hi
  · rw [max_eq_left hi, max_eq_right (neg_nonpos.mpr hi), sub_zero]
  · rw [max_eq_right hi, max_eq_left (neg_nonneg.mpr hi)]
    simp

theorem positivePart_mulVec_eq_negativePart (P : Matrix ι ι ℝ)
    (w : ι → ℝ) (hw : P *ᵥ w = 0) :
    P *ᵥ positivePart w = P *ᵥ negativePart w := by
  apply sub_eq_zero.mp
  rw [← Matrix.mulVec_sub, positivePart_sub_negativePart, hw]

theorem positive_self_pairing (P : Matrix ι ι ℝ)
    (hdiag : ∀ i, P i i = 0) (hpos : ∀ i j, i ≠ j → 0 < P i j)
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i)
    (i j : ι) (hij : i ≠ j) (hi : 0 < x i) (hj : 0 < x j) :
    0 < x ⬝ᵥ (P *ᵥ x) := by
  have hP := entries_nonnegative P hdiag hpos
  have hrow (k : ι) : 0 ≤ (P *ᵥ x) k :=
    Finset.sum_nonneg (fun l _ => mul_nonneg (hP k l) (hx l))
  change 0 < ∑ k, x k * (P *ᵥ x) k
  apply Finset.sum_pos'
  · intro k _
    exact mul_nonneg (hx k) (hrow k)
  · refine ⟨i, Finset.mem_univ i, mul_pos hi ?_⟩
    apply Finset.sum_pos'
    · intro k _
      exact mul_nonneg (hP i k) (hx k)
    · exact ⟨j, Finset.mem_univ j, mul_pos (hpos i j hij) hj⟩

/-- The two nonnegative coefficient vectors used to construct the comparison
zonotopes have equal, strictly positive self- and mixed pairings. -/
theorem parts_equal_positive_pairings (P : Matrix ι ι ℝ)
    (hsymm : ∀ i j, P i j = P j i)
    (hdiag : ∀ i, P i i = 0) (hpos : ∀ i j, i ≠ j → 0 < P i j)
    (w : ι → ℝ) (hw : P *ᵥ w = 0) (hne : w ≠ 0) :
    ∃ a : ℝ, 0 < a ∧
      positivePart w ⬝ᵥ (P *ᵥ positivePart w) = a ∧
      positivePart w ⬝ᵥ (P *ᵥ negativePart w) = a ∧
      negativePart w ⬝ᵥ (P *ᵥ negativePart w) = a := by
  have hsymmP : Pᵀ = P := by
    ext i j
    exact hsymm j i
  have hsymm_pair (x y : ι → ℝ) : x ⬝ᵥ (P *ᵥ y) = y ⬝ᵥ (P *ᵥ x) := by
    simpa only [hsymmP] using Matrix.dotProduct_transpose_mulVec P x y
  have he := positivePart_mulVec_eq_negativePart P w hw
  obtain ⟨i, j, hij, hi, hj⟩ := exists_two_positive P hdiag hpos w hw hne
  have ha : 0 < positivePart w ⬝ᵥ (P *ᵥ positivePart w) := by
    apply positive_self_pairing P hdiag hpos _ (fun k => le_max_right _ _) i j hij
    · exact lt_of_lt_of_le hi (le_max_left _ _)
    · exact lt_of_lt_of_le hj (le_max_left _ _)
  refine ⟨positivePart w ⬝ᵥ (P *ᵥ positivePart w), ha, rfl, ?_, ?_⟩
  · rw [he]
  · calc
      negativePart w ⬝ᵥ (P *ᵥ negativePart w) =
          negativePart w ⬝ᵥ (P *ᵥ positivePart w) := by rw [he]
      _ = positivePart w ⬝ᵥ (P *ᵥ negativePart w) := hsymm_pair _ _
      _ = positivePart w ⬝ᵥ (P *ᵥ positivePart w) := by rw [he]

end VolumeVerification.PositiveHollowKernel
end
end DevelopmentSource12

/- Source module: VolumePolynomials.ProjectionPairingEquality. SHA256: 2e29cf6d78ee2efeb3a1723e98d7cba9af8b156b7af704be6fd100d826376cd9 -/
section DevelopmentSource13




@[expose] public section
set_option autoImplicit false

/-!
# Equality of all actual mixed-volume pairings

This is the algebraic half of Lemma 4.1 of the projection-volume paper.
The mixed volume is the coefficient of the actual Haar-volume polynomial
defined by the recovered VolumePolynomials project.  The conclusion does
not assert the separate Shenfeld–van Handel support-function rigidity.
-/
namespace VolumePolynomials
open MeasureTheory Module
open scoped Pointwise BigOperators Matrix

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

theorem mixedVolume_equal_pairings_of_AF_equality {n : ℕ}
    (hdim : finrank ℝ E = n + 2) (K : Fin n → ConvexBody E)
    (A B : ConvexBody E) (a : ℝ) (ha : 0 < a)
    (hAA : mixedVolume μ (Fin.cons A (Fin.cons A K)) = a)
    (hAB : mixedVolume μ (Fin.cons A (Fin.cons B K)) = a)
    (hBB : mixedVolume μ (Fin.cons B (Fin.cons B K)) = a) :
    ∀ T : ConvexBody E,
      mixedVolume μ (Fin.cons A (Fin.cons T K)) =
        mixedVolume μ (Fin.cons B (Fin.cons T K)) := by
  let q : ConvexBody E → ConvexBody E → ℝ :=
    fun X Y => mixedVolume μ (Fin.cons X (Fin.cons Y K))
  apply VolumeVerification.AFPairingEquality.equality_of_equal_positive_pairings
    q (fun X Y => PolyhedralSupport.mixedVolume_cons_cons_swap μ X Y K)
    (fun X Y T => PolyhedralSupport.mixedVolume_cons_add μ X Y (Fin.cons T K))
    (fun r hr X T => PolyhedralSupport.mixedVolume_cons_smul μ X (Fin.cons T K) hr)
    (fun X Y => mixedVolume_alexandrovFenchel μ hdim K X Y)
    A B a ha hAA hAB hBB

theorem mixedVolume_cons_zero {n : ℕ} (K : Fin n → ConvexBody E) :
    mixedVolume μ (Fin.cons (0 : ConvexBody E) K) = 0 := by
  simpa only [Fin.update_cons_zero] using
    mixedVolume_zero_arg μ (Fin.cons (0 : ConvexBody E) K) 0

theorem mixedVolume_cons_sum {ι : Type*} [DecidableEq ι] {n : ℕ}
    (s : Finset ι) (A : ι → ConvexBody E) (K : Fin n → ConvexBody E) :
    mixedVolume μ (Fin.cons (∑ i ∈ s, A i) K) =
      ∑ i ∈ s, mixedVolume μ (Fin.cons (A i) K) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, mixedVolume_cons_zero]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, PolyhedralSupport.mixedVolume_cons_add, ih,
        Finset.sum_insert hi]

theorem mixedVolume_weighted_sum_pairing {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (K : Fin n → ConvexBody E) (S : ι → ConvexBody E)
    (x y : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) :
    mixedVolume μ (Fin.cons (∑ i, x i • S i) (Fin.cons (∑ j, y j • S j) K)) =
      ∑ i, ∑ j, x i * y j * mixedVolume μ (Fin.cons (S i) (Fin.cons (S j) K)) := by
  rw [mixedVolume_cons_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [PolyhedralSupport.mixedVolume_cons_smul μ _ _ (hx i),
    PolyhedralSupport.mixedVolume_cons_cons_swap, mixedVolume_cons_sum,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [PolyhedralSupport.mixedVolume_cons_smul μ _ _ (hy j),
    PolyhedralSupport.mixedVolume_cons_cons_swap]
  ring

theorem scaled_mixedVolume_weighted_sum_pairing
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (K : Fin n → ConvexBody E) (S : ι → ConvexBody E)
    (P : Matrix ι ι ℝ) (c : ℝ)
    (hP : ∀ i j, P i j =
      c * mixedVolume μ (Fin.cons (S i) (Fin.cons (S j) K)))
    (x y : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) :
    c * mixedVolume μ
      (Fin.cons (∑ i, x i • S i) (Fin.cons (∑ j, y j • S j) K)) =
      x ⬝ᵥ (P *ᵥ y) := by
  rw [mixedVolume_weighted_sum_pairing μ K S x y hx hy]
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hP]
  ring

/-- The actual Minkowski sums with the positive and negative kernel
coefficients satisfy precisely the positive equality hypotheses of AF.
This includes lower-dimensional comparison bodies and dependent marked
segments; the only normalization requirement is `0 < c`. -/
theorem mixedVolume_kernel_zonotopes_equal_positive
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]
    {n : ℕ} (K : Fin n → ConvexBody E) (S : ι → ConvexBody E)
    (P : Matrix ι ι ℝ) (c : ℝ) (hc : 0 < c)
    (hP : ∀ i j, P i j =
      c * mixedVolume μ (Fin.cons (S i) (Fin.cons (S j) K)))
    (hsymm : ∀ i j, P i j = P j i)
    (hdiag : ∀ i, P i i = 0) (hpos : ∀ i j, i ≠ j → 0 < P i j)
    (w : ι → ℝ) (hw : P *ᵥ w = 0) (hne : w ≠ 0) :
    let A := ∑ i, VolumeVerification.PositiveHollowKernel.positivePart w i • S i
    let B := ∑ i, VolumeVerification.PositiveHollowKernel.negativePart w i • S i
    ∃ a : ℝ, 0 < a ∧
      mixedVolume μ (Fin.cons A (Fin.cons A K)) = a ∧
      mixedVolume μ (Fin.cons A (Fin.cons B K)) = a ∧
      mixedVolume μ (Fin.cons B (Fin.cons B K)) = a := by
  dsimp only
  let x := VolumeVerification.PositiveHollowKernel.positivePart w
  let y := VolumeVerification.PositiveHollowKernel.negativePart w
  have hx : ∀ i, 0 ≤ x i := fun i => le_max_right _ _
  have hy : ∀ i, 0 ≤ y i := fun i => le_max_right _ _
  obtain ⟨a, ha, hxx, hxy, hyy⟩ :=
    VolumeVerification.PositiveHollowKernel.parts_equal_positive_pairings
      P hsymm hdiag hpos w hw hne
  have h₁ := scaled_mixedVolume_weighted_sum_pairing μ K S P c hP x x hx hx
  have h₂ := scaled_mixedVolume_weighted_sum_pairing μ K S P c hP x y hx hy
  have h₃ := scaled_mixedVolume_weighted_sum_pairing μ K S P c hP y y hy hy
  rw [show x ⬝ᵥ (P *ᵥ x) = a from hxx] at h₁
  rw [show x ⬝ᵥ (P *ᵥ y) = a from hxy] at h₂
  rw [show y ⬝ᵥ (P *ᵥ y) = a from hyy] at h₃
  refine ⟨a / c, div_pos ha hc, ?_, ?_, ?_⟩
  · apply (eq_div_iff hc.ne').mpr
    simpa only [mul_comm] using h₁
  · apply (eq_div_iff hc.ne').mpr
    simpa only [mul_comm] using h₂
  · apply (eq_div_iff hc.ne').mpr
    simpa only [mul_comm] using h₃

end VolumePolynomials
end
end DevelopmentSource13

/- Source module: Projection.AreaEquality. SHA256: 9c09108b5c3507fc42430e73edd1412cf670a41b6176aec7ba4264d723121239 -/
section DevelopmentSource14







@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory Module
open scoped BigOperators Pointwise Matrix

namespace RankThreeProjection
open VolumePolynomials

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

/-- The measure-equality half of Lemma 4.1, for the actual mixed area measures.
This uses the proved AF inequality and the proved density of support differences;
it makes no assertion about the separate support-function rigidity theorem. -/
theorem mixedAreaMeasure_eq_of_positive_AF_equality {d : ℕ}
    (K : Fin d → ConvexBody E) (hdim : finrank ℝ E = d + 2)
    (A B : ConvexBody E) (a : ℝ) (ha : 0 < a)
    (hAA : mixedVolume μ (Fin.cons A (Fin.cons A K)) = a)
    (hAB : mixedVolume μ (Fin.cons A (Fin.cons B K)) = a)
    (hBB : mixedVolume μ (Fin.cons B (Fin.cons B K)) = a) :
    mixedAreaMeasure μ (Fin.cons A K) hdim =
      mixedAreaMeasure μ (Fin.cons B K) hdim := by
  have heq := mixedVolume_equal_pairings_of_AF_equality μ hdim K A B a ha hAA hAB hBB
  apply measure_eq_of_support_integrals
  intro T
  rw [mixedAreaMeasure_integral, mixedAreaMeasure_integral,
    PolyhedralSupport.mixedVolume_cons_cons_swap μ T A K,
    PolyhedralSupport.mixedVolume_cons_cons_swap μ T B K, heq T]

/-- Minkowski linearity of the actual area measure in a marked body. -/
theorem mixedAreaMeasure_weighted_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {d : ℕ} (K : Fin d → ConvexBody E) (hdim : finrank ℝ E = d + 2)
    (S : ι → ConvexBody E) (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) :
    mixedAreaMeasure μ (Fin.cons (∑ i, x i • S i) K) hdim =
      ∑ i, ENNReal.ofReal (x i) • mixedAreaMeasure μ (Fin.cons (S i) K) hdim := by
  letI : ∀ i, IsFiniteMeasure
      (ENNReal.ofReal (x i) • mixedAreaMeasure μ (Fin.cons (S i) K) hdim) :=
    fun i => Measure.smul_finite _ ENNReal.ofReal_ne_top
  apply measure_eq_of_support_integrals
  intro A
  rw [mixedAreaMeasure_integral,
    PolyhedralSupport.mixedVolume_cons_cons_swap μ A _ K,
    mixedVolume_cons_sum, Finset.mul_sum,
    integral_finsetSum_measure (f := fun u : NormalSphere E => supportContinuous A u) (fun i _ =>
      (BoundedContinuousFunction.mkOfCompact (supportContinuous A)).integrable _)]
  apply Finset.sum_congr rfl
  intro i _
  rw [PolyhedralSupport.mixedVolume_cons_smul μ _ _ (hx i),
    integral_smul_measure, ENNReal.toReal_ofReal (hx i), smul_eq_mul,
    mixedAreaMeasure_integral,
    PolyhedralSupport.mixedVolume_cons_cons_swap μ (S i) A K]
  ring

private theorem real_weighted_sum {X : Type*} [MeasurableSpace X]
    {ι : Type*} [Fintype ι] (ν : ι → Measure X) [∀ i, IsFiniteMeasure (ν i)]
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (s : Set X) :
    (∑ i, ENNReal.ofReal (x i) • ν i).real s = ∑ i, x i * (ν i).real s := by
  letI : ∀ i, IsFiniteMeasure (ENNReal.ofReal (x i) • ν i) :=
    fun i => Measure.smul_finite _ ENNReal.ofReal_ne_top
  rw [Measure.real, Measure.finsetSum_apply,
    ENNReal.toReal_sum (fun i _ => measure_ne_top _ s)]
  apply Finset.sum_congr rfl
  intro i _
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (hx i)]
  rfl

/-- Every kernel vector of an actual positive hollow mixed-volume matrix gives
an identity of signed area measures, including on arbitrary measurable sets.
The positive and negative bodies are genuine Minkowski sums. -/
theorem mixedAreaMeasure_kernel_relation
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]
    {d : ℕ} (K : Fin d → ConvexBody E) (hdim : finrank ℝ E = d + 2)
    (S : ι → ConvexBody E) (P : Matrix ι ι ℝ) (c : ℝ) (hc : 0 < c)
    (hP : ∀ i j, P i j =
      c * mixedVolume μ (Fin.cons (S i) (Fin.cons (S j) K)))
    (hsymm : ∀ i j, P i j = P j i)
    (hdiag : ∀ i, P i i = 0) (hpos : ∀ i j, i ≠ j → 0 < P i j)
    (w : ι → ℝ) (hw : P *ᵥ w = 0) (s : Set (NormalSphere E)) :
    ∑ i, w i * (mixedAreaMeasure μ (Fin.cons (S i) K) hdim).real s = 0 := by
  by_cases hne : w = 0
  · subst w
    simp
  let x := VolumeVerification.PositiveHollowKernel.positivePart w
  let y := VolumeVerification.PositiveHollowKernel.negativePart w
  have hx : ∀ i, 0 ≤ x i := fun i => le_max_right _ _
  have hy : ∀ i, 0 ≤ y i := fun i => le_max_right _ _
  obtain ⟨a, ha, hAA, hAB, hBB⟩ :=
    mixedVolume_kernel_zonotopes_equal_positive μ K S P c hc hP hsymm hdiag hpos w hw hne
  have heq := mixedAreaMeasure_eq_of_positive_AF_equality μ K hdim
    (∑ i, x i • S i) (∑ i, y i • S i) a ha hAA hAB hBB
  rw [mixedAreaMeasure_weighted_sum μ K hdim S x hx,
    mixedAreaMeasure_weighted_sum μ K hdim S y hy] at heq
  have hr := congrArg (fun ν : Measure (NormalSphere E) => ν.real s) heq
  rw [real_weighted_sum _ x hx, real_weighted_sum _ y hy] at hr
  have hparts : ∀ i, w i = x i - y i := by
    intro i
    exact (congrFun
      (VolumeVerification.PositiveHollowKernel.positivePart_sub_negativePart w) i).symm
  simp_rw [hparts, sub_mul]
  rw [Finset.sum_sub_distrib, hr, sub_self]

end RankThreeProjection
end
end
end DevelopmentSource14

/- Source module: Projection.Rigidity.VolumePolynomialJets. SHA256: dd332f3f52f21f0b550d63129612942adc32148d2a812b09213f96d8037c34dc -/
section DevelopmentSource15







/-!
# Real polynomial extensions of actual Minkowski volume

Negative coefficients below belong only to a finite-dimensional multilinear
extension. Actual convex bodies are evaluated only at nonnegative weights,
where the extension is proved equal to the genuine mixed-volume functional.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Module Polynomial
open scoped BigOperators Pointwise NNReal
namespace RankThreeProjection.Rigidity
open VolumePolynomials

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

/-- Finite coordinate extension of the actual mixed volume. -/
def weightedMixedForm {m : ℕ} (B : Fin m → ConvexBody E) (n : ℕ) :
    MultilinearMap ℝ (fun _ : Fin n => Fin m → ℝ) ℝ :=
  ∑ r : Fin n → Fin m,
    mixedVolume μ (fun i => B (r i)) •
      ((MultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compLinearMap
        (fun i => LinearMap.proj (r i)))

theorem weightedMixedForm_apply {m n : ℕ} (B : Fin m → ConvexBody E)
    (w : Fin n → Fin m → ℝ) :
    weightedMixedForm μ B n w =
      ∑ r : Fin n → Fin m,
        (∏ i, w i (r i)) * mixedVolume μ (fun i => B (r i)) := by
  simp [weightedMixedForm, MultilinearMap.mkPiAlgebra_apply, mul_comm]

/-- The real extension agrees with genuine bodies whenever all their
Minkowski coefficients are nonnegative. -/
theorem weightedMixedForm_nonnegative {m n : ℕ} (B : Fin m → ConvexBody E)
    (w : Fin n → Fin m → ℝ) (hw : ∀ i j, 0 ≤ w i j) :
    weightedMixedForm μ B n w =
      mixedVolume μ (fun i => ∑ j, w i j • B j) := by
  rw [weightedMixedForm_apply]
  symm
  calc
    _ = ∑ r : Fin n → Fin m,
        mixedVolume μ (fun i => w i (r i) • B (r i)) := by
      let c : Fin n → Fin m → ℝ≥0 := fun i j => NNReal.mk (w i j) (hw i j)
      exact (mixedVolumeMultilinear μ n).map_sum (fun i j => c i j • B j)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      exact mixedVolume_independent_smul μ (fun i => B (r i))
        (fun i => w i (r i)) (fun i => hw i (r i))

theorem weightedMixedForm_single {m n : ℕ} (B : Fin m → ConvexBody E)
    (r : Fin n → Fin m) :
    weightedMixedForm μ B n (fun i => Pi.single (r i) 1) =
      mixedVolume μ (fun i => B (r i)) := by
  rw [weightedMixedForm_apply]
  classical
  rw [Finset.sum_eq_single r]
  · simp
  · intro s _hs hsr
    have hex : ∃ i, s i ≠ r i := by
      by_contra h
      push_neg at h
      exact hsr (funext h)
    obtain ⟨i, hi⟩ := hex
    have hz : (∏ j, (Pi.single (r j) 1 : Fin m → ℝ) (s j)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [Pi.single_apply, hi, Ne.symm hi]
    rw [hz, zero_mul]
  · simp

theorem weightedMixedForm_symmetric {m n : ℕ} (B : Fin m → ConvexBody E) :
    MultilinearDiagonal.PermutationSymmetric (weightedMixedForm μ B n) := by
  intro w e
  have he : (weightedMixedForm μ B n).domDomCongr e = weightedMixedForm μ B n := by
    apply Module.Basis.ext_multilinear (fun _ => Pi.basisFun ℝ (Fin m))
    intro r
    simp only [MultilinearMap.domDomCongr_apply, Pi.basisFun_apply]
    change weightedMixedForm μ B n (fun i => Pi.single (r (e i)) 1) =
      weightedMixedForm μ B n (fun i => Pi.single (r i) 1)
    rw [weightedMixedForm_single, weightedMixedForm_single]
    exact mixedVolume_reindex μ (fun i => B (r i)) e
  exact congrArg (fun F : MultilinearMap ℝ (fun _ : Fin n => Fin m → ℝ) ℝ => F w) he

/-- An ordinary polynomial, with no artificial negative dilation of a body. -/
def weightedLinePolynomial {m : ℕ} (B : Fin m → ConvexBody E)
    (n : ℕ) (p x : Fin m → ℝ) : ℝ[X] :=
  ∑ r : Fin n → Fin m,
    C (mixedVolume μ (fun i => B (r i))) *
      ∏ i, (C (p (r i)) + C (x (r i)) * X)

theorem weightedLinePolynomial_eval {m n : ℕ} (B : Fin m → ConvexBody E)
    (p x : Fin m → ℝ) (t : ℝ) :
    (weightedLinePolynomial μ B n p x).eval t =
      weightedMixedForm μ B n (fun _ => p + t • x) := by
  simp only [weightedLinePolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod,
    Polynomial.eval_add, Polynomial.eval_X, weightedMixedForm_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro r _
  rw [mul_comm]
  apply congrArg (fun z : ℝ => z * mixedVolume μ (fun i => B (r i)))
  apply Finset.prod_congr rfl
  intro i _
  ring

theorem weightedLinePolynomial_derivative {m d : ℕ}
    (B : Fin m → ConvexBody E) (p x : Fin m → ℝ) (t : ℝ) :
    (weightedLinePolynomial μ B (d + 1) p x).derivative.eval t =
      (d + 1 : ℝ) * weightedMixedForm μ B (d + 1)
        (Fin.cons x (fun _ : Fin d => p + t • x)) := by
  have hcurve := MultilinearDiagonal.hasDerivAt_diagonal
    (weightedMixedForm μ B (d + 1)) (weightedMixedForm_symmetric μ B) p x t
  have he : (fun s => (weightedLinePolynomial μ B (d + 1) p x).eval s) =
      (fun s : ℝ => weightedMixedForm μ B (d + 1) (fun _ => p + s • x)) :=
    funext (weightedLinePolynomial_eval μ B p x)
  rw [← he] at hcurve
  simpa only [Nat.cast_add, Nat.cast_one] using
    ((weightedLinePolynomial μ B (d + 1) p x).hasDerivAt t).unique hcurve

theorem weightedLinePolynomial_second_derivative {m d : ℕ}
    (B : Fin m → ConvexBody E) (p x : Fin m → ℝ) (t : ℝ) :
    (weightedLinePolynomial μ B (d + 2) p x).derivative.derivative.eval t =
      (d + 2 : ℝ) * (d + 1 : ℝ) * weightedMixedForm μ B (d + 2)
        (Fin.cons x (Fin.cons x (fun _ : Fin d => p + t • x))) := by
  have hcurve := MultilinearDiagonal.hasDerivAt_first_diagonal_derivative
    (weightedMixedForm μ B (d + 2)) (weightedMixedForm_symmetric μ B) p x t
  push_cast at hcurve
  have he : (fun s => (weightedLinePolynomial μ B (d + 2) p x).derivative.eval s) =
      (fun s : ℝ => (d + 2 : ℝ) * weightedMixedForm μ B (d + 2)
        (Fin.cons x (fun _ : Fin (d + 1) => p + s • x))) := by
    funext s
    have h := weightedLinePolynomial_derivative (d := d + 1) μ B p x s
    convert h using 1 <;> push_cast <;> ring
  rw [← he] at hcurve
  have hu := ((weightedLinePolynomial μ B (d + 2) p x).derivative.hasDerivAt t).unique hcurve
  convert hu using 1 <;> push_cast <;> ring

/-- Polynomial along the actual Minkowski ray from K in direction A. -/
def minkowskiRayPolynomial (K A : ConvexBody E) (n : ℕ) : ℝ[X] :=
  weightedLinePolynomial μ ![K,A] n (Pi.single 0 1) (Pi.single 1 1)

theorem minkowskiRayPolynomial_eval {n : ℕ} (hdim : finrank ℝ E = n)
    (K A : ConvexBody E) (t : ℝ) (ht : 0 ≤ t) :
    (minkowskiRayPolynomial μ K A n).eval t =
      μ.real ((K + t • A : ConvexBody E) : Set E) := by
  rw [minkowskiRayPolynomial, weightedLinePolynomial_eval,
    weightedMixedForm_nonnegative μ ![K,A] _ (by
      intro i j
      fin_cases j <;> simp [ht])]
  have he : (fun _ : Fin n =>
      ∑ j : Fin 2, ((Pi.single 0 1 + t • Pi.single 1 1 : Fin 2 → ℝ) j) •
        (![K,A] : Fin 2 → ConvexBody E) j) = (fun _ => K + t • A) := by
    funext i
    simp [Fin.sum_univ_succ]
  rw [he]
  exact mixedVolume_diagonal μ hdim (K + t • A)

theorem minkowskiRayPolynomial_zero {n : ℕ}
    (K A : ConvexBody E) :
    (minkowskiRayPolynomial μ K A n).eval 0 = mixedVolume μ (fun _ : Fin n => K) := by
  rw [minkowskiRayPolynomial, weightedLinePolynomial_eval]
  simp only [zero_smul, add_zero]
  exact weightedMixedForm_single μ ![K,A] (fun _ : Fin n => (0 : Fin 2))

theorem minkowskiRayPolynomial_first_zero {d : ℕ}
    (K A : ConvexBody E) :
    (minkowskiRayPolynomial μ K A (d + 1)).derivative.eval 0 =
      (d + 1 : ℝ) * mixedVolume μ (Fin.cons A (fun _ : Fin d => K)) := by
  rw [minkowskiRayPolynomial, weightedLinePolynomial_derivative]
  simp only [zero_smul, add_zero]
  congr 1
  have he : (Fin.cons (Pi.single (1 : Fin 2) (1 : ℝ))
      (fun _ : Fin d => Pi.single (0 : Fin 2) (1 : ℝ)) :
        Fin (d + 1) → Fin 2 → ℝ) =
      (fun i : Fin (d + 1) => (Pi.single
        ((Fin.cons (1 : Fin 2) (fun _ : Fin d => 0) : Fin (d + 1) → Fin 2) i)
        (1 : ℝ) : Fin 2 → ℝ)) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  rw [he, weightedMixedForm_single]
  congr 1
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem minkowskiRayPolynomial_second_zero {d : ℕ}
    (K A : ConvexBody E) :
    (minkowskiRayPolynomial μ K A (d + 2)).derivative.derivative.eval 0 =
      (d + 2 : ℝ) * (d + 1 : ℝ) *
        mixedVolume μ (Fin.cons A (Fin.cons A (fun _ : Fin d => K))) := by
  rw [minkowskiRayPolynomial, weightedLinePolynomial_second_derivative]
  simp only [zero_smul, add_zero]
  congr 1
  have he : (Fin.cons (Pi.single (1 : Fin 2) (1 : ℝ))
      (Fin.cons (Pi.single (1 : Fin 2) (1 : ℝ))
        (fun _ : Fin d => Pi.single (0 : Fin 2) (1 : ℝ))) :
        Fin (d + 2) → Fin 2 → ℝ) =
      (fun i : Fin (d + 2) => (Pi.single ((Fin.cons (1 : Fin 2)
        (Fin.cons 1 (fun _ : Fin d => 0)) : Fin (d + 2) → Fin 2) i) (1 : ℝ) :
          Fin 2 → ℝ)) := by
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun _ => rfl) j) i
  rw [he, weightedMixedForm_single]
  congr 1
  funext i
  exact Fin.cases rfl (fun j => Fin.cases rfl (fun _ => rfl) j) i

end RankThreeProjection.Rigidity

end
end
end DevelopmentSource15

/- Source module: Projection.Rigidity.PolynomialContact. SHA256: 98edf61f3585886c8c90a3abd00575aa6e647cec727756cdc8301b63f72670f5 -/
section DevelopmentSource16












/-!
# Cubic contact and the normalized midpoint volume deficit

All statements are about actual real polynomials and the usual real square
root. Equality of value and first two derivatives gives the exact factor
X³, then a vanishing deficit after division by t².
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Polynomial Filter
open scoped Topology

namespace RankThreeProjection.Rigidity

theorem X_cube_dvd_sub_of_two_derivatives (P Q : ℝ[X])
    (h0 : P.eval 0 = Q.eval 0)
    (h1 : P.derivative.eval 0 = Q.derivative.eval 0)
    (h2 : P.derivative.derivative.eval 0 = Q.derivative.derivative.eval 0) :
    (X : ℝ[X]) ^ 3 ∣ P - Q := by
  have hc0 : P.coeff 0 = Q.coeff 0 := by
    simpa only [← coeff_zero_eq_eval_zero] using h0
  have hc1 : P.coeff 1 = Q.coeff 1 := by
    simpa only [← coeff_zero_eq_eval_zero, coeff_derivative, Nat.cast_zero,
      zero_add, Nat.cast_one, mul_one] using h1
  have hc2 : P.coeff 2 = Q.coeff 2 := by
    have h := h2
    norm_num only [← coeff_zero_eq_eval_zero, coeff_derivative] at h
    linarith
  apply X_pow_dvd_iff.mpr
  intro i hi
  have hc : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hc with rfl | rfl | rfl <;> simp only [coeff_sub, hc0, hc1, hc2, sub_self]

theorem X_cube_dvd_midpoint_product (P A C : ℝ[X])
    (hA : (X : ℝ[X]) ^ 3 ∣ P - A)
    (hC : (X : ℝ[X]) ^ 3 ∣ P - C) :
    (X : ℝ[X]) ^ 3 ∣ P ^ 2 - A * C := by
  have he : P ^ 2 - A * C = (P - A) * P + A * (P - C) := by ring
  rw [he]
  exact dvd_add (dvd_mul_of_dvd_left hA P) (dvd_mul_of_dvd_right hC A)

theorem tendsto_eval_div_sq_of_X_cube_dvd (P : ℝ[X])
    (hP : (X : ℝ[X]) ^ 3 ∣ P) :
    Tendsto (fun t : ℝ => P.eval t / t ^ 2) (𝓝 0) (𝓝 0) := by
  obtain ⟨R, hR⟩ := hP
  have he : (fun t : ℝ => P.eval t / t ^ 2) = (fun t : ℝ => t * R.eval t) := by
    funext t
    rw [hR, eval_mul, eval_pow, eval_X]
    by_cases ht : t = 0
    · simp [ht]
    · field_simp [ht] <;> ring
  rw [he]
  have hid : Tendsto (fun t : ℝ => t) (𝓝 0) (𝓝 0) := tendsto_id
  simpa only [zero_mul] using hid.mul (R.continuous.tendsto (0 : ℝ))

/-- This limit needs only the exact cubic divisibility and a positive common
volume at zero. It is valid along the full neighborhood filter. -/
theorem midpoint_sqrt_deficit_little_o_sq (P A C : ℝ[X])
    (h0A : P.eval 0 = A.eval 0) (h0C : P.eval 0 = C.eval 0)
    (hpos : 0 < P.eval 0)
    (hdiv : (X : ℝ[X]) ^ 3 ∣ P ^ 2 - A * C) :
    Tendsto (fun t : ℝ =>
      (P.eval t - Real.sqrt (A.eval t * C.eval t)) / t ^ 2) (𝓝 0) (𝓝 0) := by
  let D := P ^ 2 - A * C
  have hD : Tendsto (fun t : ℝ => D.eval t / t ^ 2) (𝓝 0) (𝓝 0) :=
    tendsto_eval_div_sq_of_X_cube_dvd D hdiv
  let denom : ℝ → ℝ := fun t => P.eval t + Real.sqrt (A.eval t * C.eval t)
  have hden : Continuous denom :=
    P.continuous.add (Real.continuous_sqrt.comp (A.continuous.mul C.continuous))
  have hs0 : Real.sqrt (A.eval 0 * C.eval 0) = P.eval 0 := by
    rw [← h0A, ← h0C, Real.sqrt_mul_self hpos.le]
  have hd0 : 0 < denom 0 := by
    dsimp only [denom]
    rw [hs0]
    exact add_pos hpos hpos
  have hprod0 : 0 < A.eval 0 * C.eval 0 := by
    rw [← h0A, ← h0C]
    exact mul_pos hpos hpos
  have hprod : ∀ᶠ t : ℝ in 𝓝 0, 0 < A.eval t * C.eval t :=
    (isOpen_lt continuous_const (A.continuous.mul C.continuous)).mem_nhds hprod0
  have hdenpos : ∀ᶠ t : ℝ in 𝓝 0, 0 < denom t :=
    (isOpen_lt continuous_const hden).mem_nhds hd0
  have he : (fun t : ℝ => (D.eval t / t ^ 2) / denom t) =ᶠ[𝓝 0]
      (fun t : ℝ => (P.eval t - Real.sqrt (A.eval t * C.eval t)) / t ^ 2) := by
    filter_upwards [hprod, hdenpos] with t ht hd
    have hs := Real.sq_sqrt ht.le
    have hfactor : P.eval t ^ 2 - A.eval t * C.eval t =
        (P.eval t - Real.sqrt (A.eval t * C.eval t)) * denom t := by
      dsimp only [denom]
      nlinarith [hs]
    change ((P ^ 2 - A * C).eval t / t ^ 2) / denom t = _
    rw [eval_sub, eval_pow, eval_mul, hfactor]
    by_cases ht0 : t = 0
    · simp [ht0]
    · field_simp [ht0, hd.ne'] <;> ring
  have hquot : Tendsto (fun t : ℝ => (D.eval t / t ^ 2) / denom t)
      (𝓝 0) (𝓝 0) := by
    simpa only [div_eq_mul_inv, zero_mul] using
      hD.mul ((hden.tendsto 0).inv₀ hd0.ne')
  exact Filter.Tendsto.congr' he hquot

end RankThreeProjection.Rigidity

end
end
end DevelopmentSource16

/- Source module: Projection.Rigidity.VolumeDeficit. SHA256: 5253b66b07a223cfd009bef2e7ecd76e772394c3a67071377cd28edb92004817 -/
section DevelopmentSource17





/-!
# Actual volume deficit under mixed-volume equality

The theorem at the end proves the vanishing normalized midpoint deficit for
the actual bodies K+tA and K+tC. All coefficients come from their actual
Haar-volume polynomials. There is no polynomiality or asymptotic hypothesis.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Module Polynomial Filter
open scoped BigOperators Pointwise Topology
namespace RankThreeProjection.Rigidity
open VolumePolynomials

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

def minkowskiMidpoint (A C : ConvexBody E) : ConvexBody E := (1 / 2 : ℝ) • (A + C)

theorem minkowskiRay_midpoint (K A C : ConvexBody E) (t : ℝ) (ht : 0 ≤ t) :
    K + t • minkowskiMidpoint A C =
      (1 / 2 : ℝ) • ((K + t • A) + (K + t • C)) := by
  have hK : (1 / 2 : ℝ) • K + (1 / 2 : ℝ) • K = K := by
    rw [← body_add_smul K (by norm_num) (by norm_num)]
    norm_num
  have hmul : t * (1 / 2 : ℝ) = (1 / 2 : ℝ) * t := by ring
  simp only [minkowskiMidpoint, smul_add, smul_smul, hmul]
  conv_lhs => rw [← hK]
  exact add_add_add_comm _ _ _ _

theorem mixedVolume_midpoint_first {d : ℕ} (H : Fin d → ConvexBody E)
    (A C : ConvexBody E) :
    mixedVolume μ (Fin.cons (minkowskiMidpoint A C) H) =
      (mixedVolume μ (Fin.cons A H) + mixedVolume μ (Fin.cons C H)) / 2 := by
  rw [minkowskiMidpoint,
    PolyhedralSupport.mixedVolume_cons_smul μ (A + C) H (by norm_num),
    PolyhedralSupport.mixedVolume_cons_add]
  ring

theorem mixedVolume_midpoint_self {d : ℕ} (H : Fin d → ConvexBody E)
    (A C : ConvexBody E) (a : ℝ)
    (hAA : mixedVolume μ (Fin.cons A (Fin.cons A H)) = a)
    (hAC : mixedVolume μ (Fin.cons A (Fin.cons C H)) = a)
    (hCC : mixedVolume μ (Fin.cons C (Fin.cons C H)) = a) :
    mixedVolume μ (Fin.cons (minkowskiMidpoint A C)
      (Fin.cons (minkowskiMidpoint A C) H)) = a := by
  rw [mixedVolume_midpoint_first]
  rw [PolyhedralSupport.mixedVolume_cons_cons_swap μ A (minkowskiMidpoint A C),
    PolyhedralSupport.mixedVolume_cons_cons_swap μ C (minkowskiMidpoint A C)]
  rw [mixedVolume_midpoint_first, mixedVolume_midpoint_first]
  rw [PolyhedralSupport.mixedVolume_cons_cons_swap μ C A, hAA, hAC, hCC]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- The one-sided first derivative of the actual Haar volume, obtained from
the same actual Minkowski polynomial used for the second-order deficit. -/
theorem hasDerivWithinAt_minkowskiRayVolume {d : ℕ}
    (K A : ConvexBody E) (hdim : finrank ℝ E = d + 1) :
    HasDerivWithinAt
      (fun t : ℝ => μ.real ((K + t • A : ConvexBody E) : Set E))
      ((d + 1 : ℝ) * mixedVolume μ (Fin.cons A (fun _ : Fin d => K)))
      (Ici 0) 0 := by
  have hp := HasDerivAt.hasDerivWithinAt (s := Ici (0 : ℝ))
    ((minkowskiRayPolynomial μ K A (d + 1)).hasDerivAt 0)
  rw [minkowskiRayPolynomial_first_zero] at hp
  apply hp.congr
  · intro t ht
    exact (minkowskiRayPolynomial_eval μ hdim K A t ht).symm
  · exact (minkowskiRayPolynomial_eval μ hdim K A 0 le_rfl).symm

set_option backward.isDefEq.respectTransparency false in
/-- Equality in the positive mixed-volume pairing forces equality of the
first volume derivatives. This records the mass cancellation needed when
passing from conditional expectations to unnormalised ridge integrals. -/
theorem actual_ray_volume_difference_derivative_zero {d : ℕ}
    (K : ConvexBody E) (hdim : finrank ℝ E = d + 2)
    (A C : ConvexBody E) (a : ℝ) (ha : 0 < a)
    (hAA : mixedVolume μ (Fin.cons A (Fin.cons A (fun _ : Fin d => K))) = a)
    (hAC : mixedVolume μ (Fin.cons A (Fin.cons C (fun _ : Fin d => K))) = a)
    (hCC : mixedVolume μ (Fin.cons C (Fin.cons C (fun _ : Fin d => K))) = a) :
    HasDerivWithinAt
      (fun t : ℝ => μ.real ((K + t • A : ConvexBody E) : Set E) -
        μ.real ((K + t • C : ConvexBody E) : Set E)) 0 (Ici 0) 0 := by
  have hfirst : mixedVolume μ (Fin.cons A (fun _ : Fin (d + 1) => K)) =
      mixedVolume μ (Fin.cons C (fun _ : Fin (d + 1) => K)) := by
    simpa only [MultilinearDiagonal.cons_const] using
      mixedVolume_equal_pairings_of_AF_equality μ hdim (fun _ : Fin d => K)
        A C a ha hAA hAC hCC K
  have h := (hasDerivWithinAt_minkowskiRayVolume μ K A hdim).fun_sub
    (hasDerivWithinAt_minkowskiRayVolume μ K C hdim)
  simpa only [hfirst, sub_self] using h

theorem ray_polynomials_cubic_contact_of_AF_equality {d : ℕ}
    (K : ConvexBody E) (hdim : finrank ℝ E = d + 2)
    (A C : ConvexBody E) (a : ℝ) (ha : 0 < a)
    (hAA : mixedVolume μ (Fin.cons A (Fin.cons A (fun _ : Fin d => K))) = a)
    (hAC : mixedVolume μ (Fin.cons A (Fin.cons C (fun _ : Fin d => K))) = a)
    (hCC : mixedVolume μ (Fin.cons C (Fin.cons C (fun _ : Fin d => K))) = a) :
    (X : ℝ[X]) ^ 3 ∣
        minkowskiRayPolynomial μ K (minkowskiMidpoint A C) (d + 2) -
          minkowskiRayPolynomial μ K A (d + 2) ∧
      (X : ℝ[X]) ^ 3 ∣
        minkowskiRayPolynomial μ K (minkowskiMidpoint A C) (d + 2) -
          minkowskiRayPolynomial μ K C (d + 2) := by
  have hfirst : mixedVolume μ (Fin.cons A (fun _ : Fin (d + 1) => K)) =
      mixedVolume μ (Fin.cons C (fun _ : Fin (d + 1) => K)) := by
    simpa only [MultilinearDiagonal.cons_const] using
      mixedVolume_equal_pairings_of_AF_equality μ hdim (fun _ : Fin d => K)
        A C a ha hAA hAC hCC K
  have hmfirst : mixedVolume μ
      (Fin.cons (minkowskiMidpoint A C) (fun _ : Fin (d + 1) => K)) =
        mixedVolume μ (Fin.cons A (fun _ : Fin (d + 1) => K)) := by
    rw [mixedVolume_midpoint_first, ← hfirst]
    ring
  have hmsecond := mixedVolume_midpoint_self μ (fun _ : Fin d => K) A C a hAA hAC hCC
  constructor
  · apply X_cube_dvd_sub_of_two_derivatives
    · rw [minkowskiRayPolynomial_zero, minkowskiRayPolynomial_zero]
    · rw [minkowskiRayPolynomial_first_zero, minkowskiRayPolynomial_first_zero, hmfirst]
    · rw [minkowskiRayPolynomial_second_zero, minkowskiRayPolynomial_second_zero,
        hmsecond, hAA]
  · apply X_cube_dvd_sub_of_two_derivatives
    · rw [minkowskiRayPolynomial_zero, minkowskiRayPolynomial_zero]
    · rw [minkowskiRayPolynomial_first_zero, minkowskiRayPolynomial_first_zero,
        hmfirst, hfirst]
    · rw [minkowskiRayPolynomial_second_zero, minkowskiRayPolynomial_second_zero,
        hmsecond, hCC]

/-- The quantitative-transport input obtained from actual AF equality:
the midpoint Brunn--Minkowski volume deficit is little-o of t² as t↓0.
Lower-dimensional comparison bodies A and C are allowed. -/
theorem actual_midpoint_deficit_little_o_sq {d : ℕ}
    (K : ConvexBody E) (hdim : finrank ℝ E = d + 2)
    (hK : 0 < μ.real (K : Set E))
    (A C : ConvexBody E) (a : ℝ) (ha : 0 < a)
    (hAA : mixedVolume μ (Fin.cons A (Fin.cons A (fun _ : Fin d => K))) = a)
    (hAC : mixedVolume μ (Fin.cons A (Fin.cons C (fun _ : Fin d => K))) = a)
    (hCC : mixedVolume μ (Fin.cons C (Fin.cons C (fun _ : Fin d => K))) = a) :
    Tendsto (fun t : ℝ =>
      (μ.real ((K + t • minkowskiMidpoint A C : ConvexBody E) : Set E) -
        Real.sqrt
          (μ.real ((K + t • A : ConvexBody E) : Set E) *
            μ.real ((K + t • C : ConvexBody E) : Set E))) / t ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  let P := minkowskiRayPolynomial μ K (minkowskiMidpoint A C) (d + 2)
  let PA := minkowskiRayPolynomial μ K A (d + 2)
  let PC := minkowskiRayPolynomial μ K C (d + 2)
  have h0A : P.eval 0 = PA.eval 0 := by
    rw [minkowskiRayPolynomial_zero, minkowskiRayPolynomial_zero]
  have h0C : P.eval 0 = PC.eval 0 := by
    rw [minkowskiRayPolynomial_zero, minkowskiRayPolynomial_zero]
  have hpos : 0 < P.eval 0 := by
    rw [minkowskiRayPolynomial_zero, mixedVolume_diagonal μ hdim]
    exact hK
  obtain ⟨hA,hC⟩ := ray_polynomials_cubic_contact_of_AF_equality μ K hdim A C a ha hAA hAC hCC
  have hdiv : (X : ℝ[X]) ^ 3 ∣ P ^ 2 - PA * PC :=
    X_cube_dvd_midpoint_product P PA PC hA hC
  have hlim := (midpoint_sqrt_deficit_little_o_sq P PA PC h0A h0C hpos hdiv).mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  apply Filter.Tendsto.congr' _ hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  rw [minkowskiRayPolynomial_eval μ hdim K (minkowskiMidpoint A C) t ht.le,
    minkowskiRayPolynomial_eval μ hdim K A t ht.le,
    minkowskiRayPolynomial_eval μ hdim K C t ht.le]

end RankThreeProjection.Rigidity

end
end
end DevelopmentSource17

/- Source module: Projection.Rigidity.QuantileRayEnergy. SHA256: c3623d1c20520e34e76e5b040aa838da3bd18a9ba03123a77da7bcf32257eebd -/
section DevelopmentSource18






@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory ProbabilityTheory Filter Module
open scoped Pointwise RealInnerProductSpace Topology

namespace RankThreeProjection.QuantileStability
open VolumePolynomials

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem le_minkowski_ray_of_zero_mem (K A : ConvexBody E) (hA : (0 : E) ∈ A) (t : ℝ) :
    K ≤ K + t • A := by
  intro x hx
  refine ⟨x, hx, 0, ⟨0, hA, by simp⟩, by simp⟩

theorem minkowski_ray_volume_ne_zero (K A : ConvexBody E)
    (hK : volume (K : Set E) ≠ 0) (hA : (0 : E) ∈ A) (t : ℝ) :
    volume ((K + t • A : ConvexBody E) : Set E) ≠ 0 :=
  ne_of_gt ((pos_iff_ne_zero.mpr hK).trans_le
    (measure_mono (le_minkowski_ray_of_zero_mem K A hA t)))

theorem exists_common_minkowski_ray_radius (K A C : ConvexBody E) :
    ∃ R : ℝ, 0 < R ∧ ∀ t ∈ Icc (0 : ℝ) 1,
      (∀ x ∈ ((K + t • A : ConvexBody E) : Set E), ‖x‖ < R) ∧
      (∀ x ∈ ((K + t • C : ConvexBody E) : Set E), ‖x‖ < R) := by
  obtain ⟨R₀, hR₀, hK⟩ := K.isCompact.isBounded.exists_pos_norm_le
  obtain ⟨R₁, hR₁, hA⟩ := A.isCompact.isBounded.exists_pos_norm_le
  obtain ⟨R₂, hR₂, hC⟩ := C.isCompact.isBounded.exists_pos_norm_le
  refine ⟨R₀ + R₁ + R₂ + 1, by linarith, ?_⟩
  intro t ht
  have bound (B : ConvexBody E) (R : ℝ) (hB : ∀ x ∈ (B : Set E), ‖x‖ ≤ R)
      (hR : R₀ + R < R₀ + R₁ + R₂ + 1) :
      ∀ x ∈ ((K + t • B : ConvexBody E) : Set E), ‖x‖ < R₀ + R₁ + R₂ + 1 := by
    rintro x ⟨k, hk, z, ⟨b, hb, rfl⟩, rfl⟩
    have hs : ‖t • b‖ ≤ ‖b‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact mul_le_of_le_one_left (norm_nonneg b) ht.2
    exact ((norm_add_le k (t • b)).trans
      (add_le_add (hK k hk) (hs.trans (hB b hb)))).trans_lt hR
  exact ⟨bound A R₁ hA (by linarith), bound C R₂ hC (by linarith)⟩

theorem continuous_minkowski_ray_volume (K A : ConvexBody E) :
    Continuous (fun t : ℝ => volume.real ((K + t • A : ConvexBody E) : Set E)) :=
  (continuous_convexBody_realMeasure volume).comp
    (continuous_const.add (continuous_id.smul continuous_const))

/-- Positive AF equality for the actual repeated background implies that the
squared quantile-slope difference is `o(t²)` on every compact probability
interval. This theorem contains all geometric inputs to that conclusion. -/
theorem actual_quantile_ray_energy_little_o_sq {d : ℕ}
    (K A C : ConvexBody E) (hdim : finrank ℝ E = d + 2)
    (hK : 0 < volume.real (K : Set E)) (hA : (0 : E) ∈ A) (hC : (0 : E) ∈ C)
    (z : ℝ) (hz : 0 < z)
    (hAA : mixedVolume volume (Fin.cons A (Fin.cons A (fun _ : Fin d => K))) = z)
    (hAC : mixedVolume volume (Fin.cons A (Fin.cons C (fun _ : Fin d => K))) = z)
    (hCC : mixedVolume volume (Fin.cons C (Fin.cons C (fun _ : Fin d => K))) = z)
    {e : E} (he : ‖e‖ = 1) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    Tendsto (fun t : ℝ =>
      (∫ τ in Icc a b,
        (heightQuantileSlope ((K + t • C : ConvexBody E) : Set E) e τ -
          heightQuantileSlope ((K + t • A : ConvexBody E) : Set E) e τ) ^ 2) / t ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  have hK0 : volume (K : Set E) ≠ 0 := by
    intro h
    have : volume.real (K : Set E) = 0 := by simp [Measure.real, h]
    exact hK.ne' this
  have hd : 2 ≤ finrank ℝ E := by omega
  obtain ⟨R, hR, hbound⟩ := exists_common_minkowski_ray_radius K A C
  let M : ℝ := 2 * R / min a (1 - b)
  have hM : 0 < M := div_pos (mul_pos zero_lt_two hR) (lt_min ha (sub_pos.mpr hb))
  let c : ℝ → ℝ := fun t => Real.sqrt
    (volume.real ((K + t • A : ConvexBody E) : Set E) *
      volume.real ((K + t • C : ConvexBody E) : Set E))
  let k : ℝ → ℝ := fun t => c t / (8 * M ^ 2)
  let D : ℝ → ℝ := fun t =>
    volume.real ((K + t • Rigidity.minkowskiMidpoint A C : ConvexBody E) : Set E) - c t
  let F : ℝ → ℝ := fun t => ∫ τ in Icc a b,
    (heightQuantileSlope ((K + t • C : ConvexBody E) : Set E) e τ -
      heightQuantileSlope ((K + t • A : ConvexBody E) : Set E) e τ) ^ 2
  have hc : Tendsto c (𝓝[>] 0) (𝓝 (volume.real (K : Set E))) := by
    have h := ((continuous_minkowski_ray_volume K A).mul
      (continuous_minkowski_ray_volume K C)).sqrt.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
    simpa only [c, Pi.mul_def, body_zero_smul, add_zero,
      Real.sqrt_mul_self hK.le] using h
  have hk := hc.div_const (8 * M ^ 2)
  have hk0 : 0 < volume.real (K : Set E) / (8 * M ^ 2) :=
    div_pos hK (mul_pos (by linarith) (sq_pos_of_pos hM))
  have hkpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < k t := hk.eventually (lt_mem_nhds hk0)
  have hD : Tendsto (fun t : ℝ => D t / t ^ 2) (𝓝[>] 0) (𝓝 0) :=
    Rigidity.actual_midpoint_deficit_little_o_sq volume K hdim hK A C z hz hAA hAC hCC
  have hupper : Tendsto (fun t : ℝ => (D t / t ^ 2) / k t) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Pi.div_def, k, zero_div] using hD.div hk hk0.ne'
  have hineq : ∀ᶠ t in 𝓝[>] (0 : ℝ), F t / t ^ 2 ≤ (D t / t ^ 2) / k t := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 from zero_lt_one), hkpos]
      with t ht hkt
    have hAt := minkowski_ray_volume_ne_zero K A hK0 hA t
    have hCt := minkowski_ray_volume_ne_zero K C hK0 hC t
    obtain ⟨hRA, hRC⟩ := hbound t ⟨ht.1.le, ht.2.le⟩
    have hE := convexBody_midpoint_quantile_energy (K + t • A) (K + t • C)
      he hAt hCt M a b hM ha hab hb
      (fun τ hτ => heightQuantileSlope_le_of_radius (K + t • A) he hd hAt R hRA ha hb hτ)
      (fun τ hτ => heightQuantileSlope_le_of_radius (K + t • C) he hd hCt R hRC ha hb hτ)
    rw [← smul_add, ← Rigidity.minkowskiRay_midpoint K A C t ht.1.le] at hE
    have hE' : F t * k t ≤ D t := by
      dsimp only [F, k, D, c]
      simpa only [sub_sq_comm, mul_comm] using hE
    have h := div_le_div_of_nonneg_right ((le_div_iff₀ hkt).mpr hE') (sq_nonneg t)
    convert h using 1 <;> ring
  exact squeeze_zero' (Eventually.of_forall (fun t =>
    div_nonneg (integral_nonneg (fun _ => sq_nonneg _)) (sq_nonneg t))) hineq hupper

end RankThreeProjection.QuantileStability
end
end
end DevelopmentSource18

/- Source module: Projection.Rigidity.DilationSandwich. SHA256: 946c13fa1225120a33edd0eb2b5a53a61b7d40cbe0014a74ccedf286f190cd88 -/
section DevelopmentSource19







/-!
# Dilation control of actual Minkowski rays

A body containing the origin in its interior absorbs every compact comparison
body. If the comparison also contains zero, its nonnegative Minkowski ray is
sandwiched between the original body and a dilation with factor `1 + C * t`.
The estimate includes all nonnegative parameters, and permits comparison
bodies of arbitrary affine dimension.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped Pointwise

namespace RankThreeProjection.Rigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_pos_dilation_containing (K A : ConvexBody E)
    (hK : (0 : E) ∈ interior (K : Set E)) :
    ∃ C : ℝ, 0 < C ∧ A ≤ C • K := by
  obtain ⟨r, hr, hrK⟩ := Metric.mem_nhds_iff.mp
    (mem_interior_iff_mem_nhds.mp hK)
  obtain ⟨R, hR, hRA⟩ := A.isBounded.exists_pos_norm_le
  let C : ℝ := 2 * R / r
  have hC : 0 < C := div_pos (mul_pos (by norm_num) hR) hr
  refine ⟨C, hC, ?_⟩
  intro a ha
  change a ∈ C • (K : Set E)
  refine ⟨C⁻¹ • a, hrK ?_, ?_⟩
  · rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hC)]
    calc
      C⁻¹ * ‖a‖ ≤ C⁻¹ * R :=
        mul_le_mul_of_nonneg_left (hRA a ha) (inv_nonneg.mpr hC.le)
      _ = r / 2 := by
        dsimp [C]
        field_simp [ne_of_gt hR, ne_of_gt hr] <;> ring
      _ < r := half_lt_self hr
  · change C • (C⁻¹ • a) = a
    rw [smul_smul, mul_inv_cancel₀ hC.ne', one_smul]

theorem minkowski_ray_dilation_sandwich (K A : ConvexBody E)
    (hK : (0 : E) ∈ interior (K : Set E)) (hA : (0 : E) ∈ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      K ≤ K + t • A ∧ K + t • A ≤ (1 + C * t) • K := by
  obtain ⟨C, hC, hAC⟩ := exists_pos_dilation_containing K A hK
  refine ⟨C, hC, fun t ht => ⟨?_, ?_⟩⟩
  · intro x hx
    change x ∈ (K : Set E) + t • (A : Set E)
    exact ⟨x, hx, 0, ⟨0, hA, smul_zero _⟩, add_zero x⟩
  · have hsub : K + t • A ≤ K + t • (C • K) := by
      rintro x ⟨k, hk, y, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨k, hk, t • a, ⟨a, hAC ha, rfl⟩, rfl⟩
    have heq : K + t • (C • K) = (1 + C * t) • K := by
      rw [smul_smul]
      apply SetLike.coe_injective
      change (K : Set E) + (t * C) • (K : Set E) =
        (1 + C * t) • (K : Set E)
      calc
        (K : Set E) + (t * C) • (K : Set E) =
            (1 : ℝ) • (K : Set E) + (t * C) • (K : Set E) := by rw [one_smul]
        _ = (1 + t * C) • (K : Set E) :=
          (K.convex.add_smul zero_le_one (mul_nonneg ht hC.le)).symm
        _ = _ := by rw [mul_comm t C]
    exact heq ▸ hsub

end RankThreeProjection.Rigidity
end
end
end DevelopmentSource19

/- Source module: TauCeti.Probability.Quantile.Map. SHA256: fd29fe15b3c9520380f83866afc1f9259c7646552083a425cdaf138d08a930fd -/
section DevelopmentSource20
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/







/-!
# Quantiles of pushforwards along monotone maps

If `X` has law `μ` and `g : ℝ → ℝ` is continuous and nondecreasing, the quantile function of
`g X` is `g` composed with the quantile function of `X`: at every level `t` strictly between `0`
and `1`,

`(μ.map g).quantile t = g (μ.quantile t)`,

and the same holds for the upper quantile. Strict monotonicity is not needed: a flat piece of `g`
merges values without changing which point is the `t`-quantile.

A nonincreasing map reverses the order of levels and exchanges the two quantiles. Negation is the
basic case, `μ.neg.quantile t = -μ.upperQuantile (1 - t)`, and composing with it gives
`(μ.map g).quantile t = g (μ.upperQuantile (1 - t))` for continuous nonincreasing `g`. The upper
quantile cannot be replaced by the lower one when the cumulative distribution function of `μ` has
a plateau at level `1 - t`.

Maps such as the logarithm or the reciprocal are monotone and continuous only on part of the line.
The general statements therefore only ask for the hypotheses on an interval `s` carrying all the
mass of `μ`. Every quantile at a level strictly between `0` and `1` lies in such an interval
(`Set.OrdConnected.quantile_mem`), so the hypotheses on `s` apply at the quantile.

## Main statements

* `Set.OrdConnected.quantile_mem`, `Set.OrdConnected.upperQuantile_mem` — interior quantiles lie
  in every interval of full mass;
* `MeasureTheory.Measure.quantile_map_of_monotoneOn`,
  `MeasureTheory.Measure.upperQuantile_map_of_monotoneOn` — the quantiles of a pushforward along a
  map that is nondecreasing and continuous on an interval of full mass, with the global forms
  `MeasureTheory.Measure.quantile_map_of_monotone` and
  `MeasureTheory.Measure.upperQuantile_map_of_monotone`;
* `MeasureTheory.Measure.quantile_neg`, `MeasureTheory.Measure.upperQuantile_neg` — the quantiles
  of the reflected law;
* `MeasureTheory.Measure.quantile_map_of_antitoneOn`,
  `MeasureTheory.Measure.upperQuantile_map_of_antitoneOn` — the quantiles of a pushforward along a
  nonincreasing continuous map, with the global forms
  `MeasureTheory.Measure.quantile_map_of_antitone` and
  `MeasureTheory.Measure.upperQuantile_map_of_antitone`;
* `MeasureTheory.Measure.quantile_map_exp`, `MeasureTheory.Measure.quantile_map_log`,
  `MeasureTheory.Measure.quantile_map_rpow`, `MeasureTheory.Measure.quantile_map_sqrt`,
  `MeasureTheory.Measure.quantile_map_inv` and their upper-quantile counterparts — the elementary
  maps, with the logarithm, real powers and the reciprocal taken on the half-line carrying a
  positive or nonnegative law.

## References

* P. Embrechts and M. Hofert, *A note on generalized inverses*, Mathematical Methods of
  Operations Research 77 (2013), 423--432.
-/

public section

open Filter MeasureTheory ProbabilityTheory Set Topology

variable {μ : Measure ℝ} {s : Set ℝ} {t : ℝ}

namespace MeasureTheory.Measure

variable {g : ℝ → ℝ}

/-! ### Nondecreasing maps -/

/-- **Quantiles of a nondecreasing image.** If `g` is nondecreasing and continuous on an interval
carrying all the mass of `μ`, then at every level strictly between `0` and `1` the quantile of the
law of `g X` is `g` applied to the quantile of the law of `X`. -/
theorem quantile_map_of_monotoneOn [IsProbabilityMeasure μ] (hs : s.OrdConnected)
    (hμs : ∀ᵐ x ∂μ, x ∈ s) (hg : MonotoneOn g s) (hgc : ContinuousOn g s) (h0 : 0 < t)
    (h1 : t < 1) : (μ.map g).quantile t = g (μ.quantile t) := by
  have hgm : AEMeasurable g μ :=
    restrict_eq_self_of_ae_mem hμs ▸ aemeasurable_restrict_of_monotoneOn hs.measurableSet hg
  have hq := hs.quantile_mem hμs h0 h1
  refine le_antisymm ((quantile_le_iff _ h0 h1).2 ?_) (le_of_not_gt fun hlt ↦ ?_)
  · -- Every point of `s` below the quantile is sent below its image.
    rw [cdf_eq_real, map_measureReal_apply_of_aemeasurable hgm measurableSet_Iic]
    refine (le_cdf_quantile μ h1).trans ?_
    rw [cdf_eq_real]
    exact ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono_ae (hμs.mono fun x hx hxq ↦ hg hx hq hxq))
  · -- Left continuity keeps `g` above the smaller quantile on some `s ∩ Ioc l q`, so the mass
    -- sent below it is at most `cdf μ l`, which is smaller than `t`.
    obtain ⟨l, hlq, hl⟩ := exists_Ioc_subset_of_mem_nhds
      (eventually_nhdsWithin_iff.1 ((hgc _ hq).eventually (lt_mem_nhds hlt)))
      ⟨μ.quantile t - 1, by linarith⟩
    refine ((lt_quantile_iff μ h0 h1).1 hlq).not_ge ((le_cdf_quantile (μ.map g) h1).trans ?_)
    rw [cdf_eq_real, map_measureReal_apply_of_aemeasurable hgm measurableSet_Iic, cdf_eq_real]
    refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae (hμs.mono fun x hx hxy ↦ ?_))
    simp only [mem_preimage, mem_Iic] at hxy ⊢
    by_contra! hxl
    rcases le_or_gt x (μ.quantile t) with hxq | hxq
    · exact (hl ⟨hxl, hxq⟩ hx).not_ge hxy
    · exact hlt.not_ge ((hg hq hx hxq.le).trans hxy)

/-- **Upper quantiles of a nondecreasing image.** If `g` is nondecreasing and continuous on an
interval carrying all the mass of `μ`, then at every level strictly between `0` and `1` the upper
quantile of the law of `g X` is `g` applied to the upper quantile of the law of `X`. -/
theorem upperQuantile_map_of_monotoneOn [IsProbabilityMeasure μ] (hs : s.OrdConnected)
    (hμs : ∀ᵐ x ∂μ, x ∈ s) (hg : MonotoneOn g s) (hgc : ContinuousOn g s) (h0 : 0 < t)
    (h1 : t < 1) : (μ.map g).upperQuantile t = g (μ.upperQuantile t) := by
  have hgm : AEMeasurable g μ :=
    restrict_eq_self_of_ae_mem hμs ▸ aemeasurable_restrict_of_monotoneOn hs.measurableSet hg
  have hp := hs.upperQuantile_mem hμs h0 h1
  refine le_antisymm (le_of_forall_gt_imp_ge_of_dense fun y hy ↦ ?_)
    ((le_upperQuantile_iff _ h0 h1).2 ?_)
  · -- Right continuity keeps `g` below `y` on some `s ∩ Ico p r`, so every point of `s` below `r`
    -- is sent to at most `y`, and that mass exceeds `t`.
    obtain ⟨r, hpr, hr⟩ := exists_Ico_subset_of_mem_nhds
      (eventually_nhdsWithin_iff.1 ((hgc _ hp).eventually (gt_mem_nhds hy)))
      ⟨μ.upperQuantile t + 1, by linarith⟩
    refine upperQuantile_le_of_lt_cdf _ h0 (((upperQuantile_lt_iff μ h0 h1).1 hpr).trans_le ?_)
    rw [cdf_eq_real, map_measureReal_apply_of_aemeasurable hgm measurableSet_Iic]
    refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae (hμs.mono fun x hx hxr ↦ ?_))
    rcases le_or_gt (μ.upperQuantile t) x with hpx | hxp
    · exact (hr ⟨hpx, hxr⟩ hx).le
    · exact (hg hx hp hxp.le).trans hy.le
  · -- A point of `s` sent strictly below the image of the upper quantile lies strictly below it.
    refine le_trans ?_ (measureReal_Iio_upperQuantile_le μ h0 h1)
    rw [map_measureReal_apply_of_aemeasurable hgm measurableSet_Iio]
    exact ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono_ae (hμs.mono fun x hx hxp ↦ lt_of_not_ge fun hpx ↦
        (hg hp hx hpx).not_gt hxp))

/-- **Quantiles of a nondecreasing image.** For a nondecreasing continuous `g`, the quantile of
the law of `g X` at a level strictly between `0` and `1` is `g` applied to the quantile of the law
of `X`. -/
theorem quantile_map_of_monotone [IsProbabilityMeasure μ] (hg : Monotone g) (hgc : Continuous g)
    (h0 : 0 < t) (h1 : t < 1) : (μ.map g).quantile t = g (μ.quantile t) :=
  quantile_map_of_monotoneOn ordConnected_univ (ae_of_all _ mem_univ) (hg.monotoneOn _)
    hgc.continuousOn h0 h1

/-- **Upper quantiles of a nondecreasing image.** For a nondecreasing continuous `g`, the upper
quantile of the law of `g X` at a level strictly between `0` and `1` is `g` applied to the upper
quantile of the law of `X`. -/
theorem upperQuantile_map_of_monotone [IsProbabilityMeasure μ] (hg : Monotone g)
    (hgc : Continuous g) (h0 : 0 < t) (h1 : t < 1) :
    (μ.map g).upperQuantile t = g (μ.upperQuantile t) :=
  upperQuantile_map_of_monotoneOn ordConnected_univ (ae_of_all _ mem_univ) (hg.monotoneOn _)
    hgc.continuousOn h0 h1

/-! ### Reflection and nonincreasing maps -/

/-- **Quantiles of the reflected law.** The quantile of the law of `-X` at a level strictly between
`0` and `1` is minus the upper quantile of the law of `X` at the complementary level. -/
@[simp] theorem quantile_neg [IsProbabilityMeasure μ] (h0 : 0 < t) (h1 : t < 1) :
    μ.neg.quantile t = -μ.upperQuantile (1 - t) := by
  refine eq_of_forall_ge_iff fun y ↦ ?_
  have hpre : (Neg.neg ⁻¹' Iic y : Set ℝ) = (Iio (-y))ᶜ := by
    ext x
    simp
  rw [quantile_le_iff _ h0 h1, cdf_eq_real, neg_def,
    map_measureReal_apply measurable_neg measurableSet_Iic, hpre,
    measureReal_compl measurableSet_Iio, probReal_univ, neg_le,
    le_upperQuantile_iff μ (by linarith) (by linarith)]
  constructor <;> intro h <;> linarith

/-- **Upper quantiles of the reflected law.** The upper quantile of the law of `-X` at a level
strictly between `0` and `1` is minus the quantile of the law of `X` at the complementary level. -/
@[simp] theorem upperQuantile_neg [IsProbabilityMeasure μ] (h0 : 0 < t) (h1 : t < 1) :
    μ.neg.upperQuantile t = -μ.quantile (1 - t) := by
  refine eq_of_forall_le_iff fun y ↦ ?_
  have hpre : (Neg.neg ⁻¹' Iio y : Set ℝ) = (Iic (-y))ᶜ := by
    ext x
    simp
  rw [le_upperQuantile_iff _ h0 h1, neg_def,
    map_measureReal_apply measurable_neg measurableSet_Iio, hpre,
    measureReal_compl measurableSet_Iic, probReal_univ, le_neg,
    quantile_le_iff μ (by linarith) (by linarith), cdf_eq_real]
  constructor <;> intro h <;> linarith

/-- Pushing forward along a nonincreasing map `g` is pushing the reflected law forward along the
map `x ↦ g (-x)`, which is nondecreasing and continuous on the reflected interval, and that
interval carries all the mass of the reflected law. -/
private theorem map_eq_map_neg_comp (hs : s.OrdConnected)
    (hμs : ∀ᵐ x ∂μ, x ∈ s) (hg : AntitoneOn g s) (hgc : ContinuousOn g s) :
    μ.map g = μ.neg.map (g ∘ Neg.neg) ∧ (Neg.neg ⁻¹' s).OrdConnected ∧
      (∀ᵐ x ∂μ.neg, x ∈ Neg.neg ⁻¹' s) ∧
      MonotoneOn (g ∘ Neg.neg) (Neg.neg ⁻¹' s) ∧ ContinuousOn (g ∘ Neg.neg) (Neg.neg ⁻¹' s) := by
  have hae : ∀ᵐ x ∂μ.neg, x ∈ Neg.neg ⁻¹' s := by
    exact μ.ae_neg_mem_preimage hs.measurableSet hμs
  have hmono : MonotoneOn (g ∘ Neg.neg) (Neg.neg ⁻¹' s) :=
    fun x hx y hy hxy ↦ hg hy hx (neg_le_neg hxy)
  refine ⟨?_, hs.preimage_anti fun _ _ ↦ neg_le_neg, hae, hmono,
    hgc.comp continuousOn_neg fun _ hx ↦ hx⟩
  have hgm : AEMeasurable (g ∘ Neg.neg) μ.neg := restrict_eq_self_of_ae_mem hae ▸
    aemeasurable_restrict_of_monotoneOn (measurable_neg hs.measurableSet) hmono
  exact (μ.map_neg_comp hgm).symm

/-- **Quantiles of a nonincreasing image.** If `g` is nonincreasing and continuous on an interval
carrying all the mass of `μ`, then at every level strictly between `0` and `1` the quantile of the
law of `g X` is `g` applied to the upper quantile of the law of `X` at the complementary level. -/
theorem quantile_map_of_antitoneOn [IsProbabilityMeasure μ] (hs : s.OrdConnected)
    (hμs : ∀ᵐ x ∂μ, x ∈ s) (hg : AntitoneOn g s) (hgc : ContinuousOn g s) (h0 : 0 < t)
    (h1 : t < 1) : (μ.map g).quantile t = g (μ.upperQuantile (1 - t)) := by
  obtain ⟨hmap, hs', hμs', hg', hgc'⟩ := map_eq_map_neg_comp hs hμs hg hgc
  rw [hmap, quantile_map_of_monotoneOn hs' hμs' hg' hgc' h0 h1, Function.comp_apply,
    quantile_neg h0 h1, neg_neg]

/-- **Upper quantiles of a nonincreasing image.** If `g` is nonincreasing and continuous on an
interval carrying all the mass of `μ`, then at every level strictly between `0` and `1` the upper
quantile of the law of `g X` is `g` applied to the quantile of the law of `X` at the complementary
level. -/
theorem upperQuantile_map_of_antitoneOn [IsProbabilityMeasure μ] (hs : s.OrdConnected)
    (hμs : ∀ᵐ x ∂μ, x ∈ s) (hg : AntitoneOn g s) (hgc : ContinuousOn g s) (h0 : 0 < t)
    (h1 : t < 1) : (μ.map g).upperQuantile t = g (μ.quantile (1 - t)) := by
  obtain ⟨hmap, hs', hμs', hg', hgc'⟩ := map_eq_map_neg_comp hs hμs hg hgc
  rw [hmap, upperQuantile_map_of_monotoneOn hs' hμs' hg' hgc' h0 h1, Function.comp_apply,
    upperQuantile_neg h0 h1, neg_neg]

/-- **Quantiles of a nonincreasing image.** For a nonincreasing continuous `g`, the quantile of
the law of `g X` at a level strictly between `0` and `1` is `g` applied to the upper quantile of
the law of `X` at the complementary level. -/
theorem quantile_map_of_antitone [IsProbabilityMeasure μ] (hg : Antitone g) (hgc : Continuous g)
    (h0 : 0 < t) (h1 : t < 1) : (μ.map g).quantile t = g (μ.upperQuantile (1 - t)) :=
  quantile_map_of_antitoneOn ordConnected_univ (ae_of_all _ mem_univ) (hg.antitoneOn _)
    hgc.continuousOn h0 h1

/-- **Upper quantiles of a nonincreasing image.** For a nonincreasing continuous `g`, the upper
quantile of the law of `g X` at a level strictly between `0` and `1` is `g` applied to the
quantile of the law of `X` at the complementary level. -/
theorem upperQuantile_map_of_antitone [IsProbabilityMeasure μ] (hg : Antitone g)
    (hgc : Continuous g) (h0 : 0 < t) (h1 : t < 1) :
    (μ.map g).upperQuantile t = g (μ.quantile (1 - t)) :=
  upperQuantile_map_of_antitoneOn ordConnected_univ (ae_of_all _ mem_univ) (hg.antitoneOn _)
    hgc.continuousOn h0 h1

/-! ### Elementary maps -/

/-- The quantile of the law of `exp X` is the exponential of the quantile of the law of `X`. -/
@[simp] theorem quantile_map_exp [IsProbabilityMeasure μ] (h0 : 0 < t) (h1 : t < 1) :
    (μ.map Real.exp).quantile t = Real.exp (μ.quantile t) :=
  quantile_map_of_monotone Real.exp_monotone Real.continuous_exp h0 h1

/-- The upper quantile of the law of `exp X` is the exponential of the upper quantile of the law
of `X`. -/
@[simp] theorem upperQuantile_map_exp [IsProbabilityMeasure μ] (h0 : 0 < t) (h1 : t < 1) :
    (μ.map Real.exp).upperQuantile t = Real.exp (μ.upperQuantile t) :=
  upperQuantile_map_of_monotone Real.exp_monotone Real.continuous_exp h0 h1

/-- For a law carried by the positive half-line, the quantile of the law of `log X` is the
logarithm of the quantile of the law of `X`. -/
@[simp] theorem quantile_map_log [IsProbabilityMeasure μ] (hμ : ∀ᵐ x ∂μ, 0 < x) (h0 : 0 < t)
    (h1 : t < 1) : (μ.map Real.log).quantile t = Real.log (μ.quantile t) :=
  quantile_map_of_monotoneOn ordConnected_Ioi hμ Real.strictMonoOn_log.monotoneOn
    (Real.continuousOn_log.mono fun _ hx ↦ (ne_of_gt hx)) h0 h1

/-- For a law carried by the positive half-line, the upper quantile of the law of `log X` is the
logarithm of the upper quantile of the law of `X`. -/
@[simp] theorem upperQuantile_map_log [IsProbabilityMeasure μ] (hμ : ∀ᵐ x ∂μ, 0 < x) (h0 : 0 < t)
    (h1 : t < 1) : (μ.map Real.log).upperQuantile t = Real.log (μ.upperQuantile t) :=
  upperQuantile_map_of_monotoneOn ordConnected_Ioi hμ Real.strictMonoOn_log.monotoneOn
    (Real.continuousOn_log.mono fun _ hx ↦ (ne_of_gt hx)) h0 h1

/-- For a law carried by the nonnegative half-line and a nonnegative exponent `r`, the quantile of
the law of `X ^ r` is the `r`-th power of the quantile of the law of `X`. -/
@[simp] theorem quantile_map_rpow [IsProbabilityMeasure μ] (hμ : ∀ᵐ x ∂μ, 0 ≤ x) {r : ℝ}
    (hr : 0 ≤ r)
    (h0 : 0 < t) (h1 : t < 1) : (μ.map (· ^ r)).quantile t = μ.quantile t ^ r :=
  quantile_map_of_monotoneOn ordConnected_Ici hμ (Real.monotoneOn_rpow_Ici_of_exponent_nonneg hr)
    (Real.continuous_rpow_const hr).continuousOn h0 h1

/-- For a law carried by the nonnegative half-line and a nonnegative exponent `r`, the upper
quantile of the law of `X ^ r` is the `r`-th power of the upper quantile of the law of `X`. -/
@[simp] theorem upperQuantile_map_rpow [IsProbabilityMeasure μ] (hμ : ∀ᵐ x ∂μ, 0 ≤ x) {r : ℝ}
    (hr : 0 ≤ r) (h0 : 0 < t) (h1 : t < 1) :
    (μ.map (· ^ r)).upperQuantile t = μ.upperQuantile t ^ r :=
  upperQuantile_map_of_monotoneOn ordConnected_Ici hμ
    (Real.monotoneOn_rpow_Ici_of_exponent_nonneg hr) (Real.continuous_rpow_const hr).continuousOn
    h0 h1

/-- The quantile of the law of `√X` is the square root of the quantile of the law of `X`. Since
`Real.sqrt` is nondecreasing and continuous on the whole line, no support hypothesis is needed. -/
@[simp] theorem quantile_map_sqrt [IsProbabilityMeasure μ] (h0 : 0 < t) (h1 : t < 1) :
    (μ.map Real.sqrt).quantile t = √(μ.quantile t) :=
  quantile_map_of_monotone (fun _ _ ↦ Real.sqrt_le_sqrt) Real.continuous_sqrt h0 h1

/-- The upper quantile of the law of `√X` is the square root of the upper quantile of the law
of `X`. -/
@[simp] theorem upperQuantile_map_sqrt [IsProbabilityMeasure μ] (h0 : 0 < t) (h1 : t < 1) :
    (μ.map Real.sqrt).upperQuantile t = √(μ.upperQuantile t) :=
  upperQuantile_map_of_monotone (fun _ _ ↦ Real.sqrt_le_sqrt) Real.continuous_sqrt h0 h1

/-- For a law carried by the positive half-line, the quantile of the law of `X⁻¹` is the
reciprocal of the upper quantile of the law of `X` at the complementary level. -/
@[simp] theorem quantile_map_inv [IsProbabilityMeasure μ] (hμ : ∀ᵐ x ∂μ, 0 < x) (h0 : 0 < t)
    (h1 : t < 1) : (μ.map (·⁻¹)).quantile t = (μ.upperQuantile (1 - t))⁻¹ :=
  quantile_map_of_antitoneOn ordConnected_Ioi hμ (fun _ hx _ _ hxy ↦ inv_anti₀ hx hxy)
    (continuousOn_inv₀.mono fun _ hx ↦ (ne_of_gt hx)) h0 h1

/-- For a law carried by the positive half-line, the upper quantile of the law of `X⁻¹` is the
reciprocal of the quantile of the law of `X` at the complementary level. -/
@[simp] theorem upperQuantile_map_inv [IsProbabilityMeasure μ] (hμ : ∀ᵐ x ∂μ, 0 < x) (h0 : 0 < t)
    (h1 : t < 1) : (μ.map (·⁻¹)).upperQuantile t = (μ.quantile (1 - t))⁻¹ :=
  upperQuantile_map_of_antitoneOn ordConnected_Ioi hμ (fun _ hx _ _ hxy ↦ inv_anti₀ hx hxy)
    (continuousOn_inv₀.mono fun _ hx ↦ (ne_of_gt hx)) h0 h1

end MeasureTheory.Measure
end
end DevelopmentSource20

/- Source module: Projection.QuantileDilation. SHA256: cff442d7dfb97001b52e5057a236c88e3270a4acfa179ecbdd89e360880b0a48 -/
section DevelopmentSource21







@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory ProbabilityTheory TauCeti Filter
open scoped Pointwise RealInnerProductSpace Topology

namespace RankThreeProjection.QuantileStability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def heightCDF (K : Set E) (e : E) (s : ℝ) : ℝ :=
  cdf ((volume[|K]).map fun x => ⟪e, x⟫) s

private theorem volumeReal_smul (S : Set E) {scale : ℝ} (hscale : 0 ≤ scale) :
    volume.real (scale • S) = scale ^ Module.finrank ℝ E * volume.real S := by
  simp only [Measure.real]
  rw [Measure.addHaar_smul_of_nonneg volume hscale, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hscale _)]

private theorem volumeReal_height_smul (K : ConvexBody E) (e : E)
    {scale : ℝ} (hscale : 0 < scale) (s : ℝ) :
    volume.real {x ∈ ((scale • K : ConvexBody E) : Set E) | ⟪e, x⟫ ≤ scale * s} =
      scale ^ Module.finrank ℝ E * volume.real {x ∈ (K : Set E) | ⟪e, x⟫ ≤ s} := by
  have hset : {x ∈ ((scale • K : ConvexBody E) : Set E) | ⟪e, x⟫ ≤ scale * s} =
      scale • {x ∈ (K : Set E) | ⟪e, x⟫ ≤ s} := by
    ext x
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hys⟩
      refine ⟨y, ⟨hy, ?_⟩, rfl⟩
      exact (mul_le_mul_iff_of_pos_left hscale).mp
        (by simpa only [real_inner_smul_right] using hys)
    · rintro ⟨y, ⟨hy, hys⟩, rfl⟩
      exact ⟨⟨y, hy, rfl⟩, by
        simpa only [real_inner_smul_right] using mul_le_mul_of_nonneg_left hys hscale.le⟩
  rw [hset, volumeReal_smul _ hscale.le]

/-- CDF comparisons obtained directly from the nested actual bodies
`K ⊆ L ⊆ scale • K`. The factor `scale^dim` accounts for normalization of volume. -/
theorem heightCDF_dilation_bounds (K L : ConvexBody E) (e : E)
    (hK : volume (K : Set E) ≠ 0) {scale : ℝ} (hscale : 0 < scale)
    (hKL : K ≤ L) (hLK : L ≤ scale • K) (s : ℝ) :
    heightCDF (K : Set E) e s / scale ^ Module.finrank ℝ E ≤ heightCDF (L : Set E) e s ∧
      heightCDF (L : Set E) e (scale * s) ≤
        scale ^ Module.finrank ℝ E * heightCDF (K : Set E) e s := by
  have hL : volume (L : Set E) ≠ 0 :=
    ne_of_gt ((pos_iff_ne_zero.mpr hK).trans_le (measure_mono hKL))
  have hV : 0 < volume.real (K : Set E) :=
    ENNReal.toReal_pos hK K.isCompact.measure_lt_top.ne
  have hW : 0 < volume.real (L : Set E) :=
    ENNReal.toReal_pos hL L.isCompact.measure_lt_top.ne
  have hpow : 0 < scale ^ Module.finrank ℝ E := pow_pos hscale _
  have hVW : volume.real (K : Set E) ≤ volume.real (L : Set E) :=
    measureReal_mono hKL L.isCompact.measure_lt_top.ne
  have hWV : volume.real (L : Set E) ≤
      volume.real (K : Set E) * scale ^ Module.finrank ℝ E := by
    have h := measureReal_mono (μ := volume) hLK (scale • K).isCompact.measure_lt_top.ne
    rw [ConvexBody.coe_smul, volumeReal_smul _ hscale.le] at h
    simpa only [mul_comm] using h
  have hsmall : volume.real {x ∈ (K : Set E) | ⟪e, x⟫ ≤ s} ≤
      volume.real {x ∈ (L : Set E) | ⟪e, x⟫ ≤ s} :=
    measureReal_mono (μ := volume) (fun x hx => ⟨hKL hx.1, hx.2⟩)
      (measure_lt_top_of_subset (μ := volume)
        (fun x (hx : x ∈ {x ∈ (L : Set E) | ⟪e, x⟫ ≤ s}) => hx.1)
        L.isCompact.measure_lt_top.ne).ne
  have hlarge : volume.real {x ∈ (L : Set E) | ⟪e, x⟫ ≤ scale * s} ≤
      scale ^ Module.finrank ℝ E * volume.real {x ∈ (K : Set E) | ⟪e, x⟫ ≤ s} := by
    have h := measureReal_mono (μ := volume)
      (fun x (hx : x ∈ {x ∈ (L : Set E) | ⟪e, x⟫ ≤ scale * s}) =>
      (show x ∈ {x ∈ ((scale • K : ConvexBody E) : Set E) | ⟪e, x⟫ ≤ scale * s} from
        ⟨hLK hx.1, hx.2⟩))
      (measure_lt_top_of_subset (μ := volume)
        (fun x (hx : x ∈ {x ∈ ((scale • K : ConvexBody E) : Set E) |
          ⟪e, x⟫ ≤ scale * s}) => hx.1)
        (scale • K).isCompact.measure_lt_top.ne).ne
    rw [volumeReal_height_smul K e hscale s] at h
    exact h
  simp only [heightCDF, cdf_map_inner_cond hK K.isCompact.measure_lt_top.ne,
    cdf_map_inner_cond hL L.isCompact.measure_lt_top.ne]
  constructor
  · rw [div_div]
    apply (div_le_div_iff₀ (mul_pos hV hpow) hW).mpr
    exact (mul_le_mul_of_nonneg_left hWV measureReal_nonneg).trans
      (mul_le_mul_of_nonneg_right hsmall (mul_nonneg hV.le hpow.le))
  · rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hW hV).mpr
    exact (mul_le_mul_of_nonneg_left hVW measureReal_nonneg).trans
      (mul_le_mul_of_nonneg_right hlarge hW.le)

theorem abs_heightQuantile_lt_of_radius (K : ConvexBody E) {e : E} (he : ‖e‖ = 1)
    (hK : volume (K : Set E) ≠ 0) (R : ℝ)
    (hR : ∀ x ∈ (K : Set E), ‖x‖ < R) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    |heightQuantile (K : Set E) e t| < R := by
  obtain ⟨x, hx, heq⟩ := K.convex.quantile_map_inner_cond_mem_image_interior he hK
    K.isCompact.measure_lt_top.ne ht
  unfold heightQuantile
  rw [← heq]
  exact (abs_real_inner_le_norm e x).trans_lt
    (by simpa only [he, one_mul] using hR x (interior_subset hx))

/-- Reflection exchanges the two probability tails exactly. -/
theorem heightQuantile_neg (K : ConvexBody E) {e : E} (he : ‖e‖ = 1)
    (hK : volume (K : Set E) ≠ 0) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    heightQuantile (K : Set E) (-e) t = -heightQuantile (K : Set E) e (1 - t) := by
  let ν := (volume[|(K : Set E)]).map fun x => ⟪e, x⟫
  haveI := cond_isProbabilityMeasure_of_finite hK K.isCompact.measure_lt_top.ne
  have hmap : (volume[|(K : Set E)]).map (fun x => ⟪-e, x⟫) = ν.neg := by
    dsimp only [ν]
    have hmeas : Measurable (fun x : E => ⟪e, x⟫) :=
      (continuous_const.inner continuous_id).measurable
    rw [Measure.neg_def, Measure.map_map measurable_neg hmeas]
    congr 1
    funext x
    simp only [Function.comp_apply, inner_neg_left]
  change ((volume[|(K : Set E)]).map (fun x => ⟪-e, x⟫)).quantile t = -ν.quantile (1 - t)
  rw [hmap, Measure.quantile_neg ht.1 ht.2]
  congr 1
  apply Measure.upperQuantile_eq_of_cdf_eq ν
    (K.convex.strictMonoOn_cdf_map_inner_cond he hK K.isCompact.measure_lt_top.ne)
  · exact Measure.cdf_quantile ν
      (continuous_cdf_map_inner_cond he hK K.isCompact.measure_lt_top.ne)
      (by linarith [ht.2]) (by linarith [ht.1])
  · exact ⟨by linarith [ht.2], by linarith [ht.1]⟩

private theorem heightQuantile_dilation_bound_left (K L : ConvexBody E)
    {e : E} (he : ‖e‖ = 1) (hdim : 2 ≤ Module.finrank ℝ E)
    (hK : volume (K : Set E) ≠ 0) (R : ℝ)
    (hR : ∀ x ∈ (K : Set E), ‖x‖ < R)
    {scale : ℝ} (hscale1 : 1 ≤ scale) (hpow : scale ^ Module.finrank ℝ E ≤ 3 / 2)
    (hKL : K ≤ L) (hLK : L ≤ scale • K)
    {t : ℝ} (ht : 0 < t) (ht2 : t ≤ 1 / 2) :
    |heightQuantile (L : Set E) e t - heightQuantile (K : Set E) e t| ≤
      R * (scale - 1) + 4 * R * (scale ^ Module.finrank ℝ E - 1) := by
  let Λ := scale ^ Module.finrank ℝ E
  let q := heightQuantile (K : Set E) e
  let v := heightQuantileSlope (K : Set E) e
  have hscale : 0 < scale := zero_lt_one.trans_le hscale1
  have hΛ1 : 1 ≤ Λ := one_le_pow₀ hscale1
  have hΛ : 0 < Λ := pow_pos hscale _
  have hΛ2 : Λ ≤ 3 / 2 := hpow
  have hL : volume (L : Set E) ≠ 0 :=
    ne_of_gt ((pos_iff_ne_zero.mpr hK).trans_le (measure_mono hKL))
  have htI : t ∈ Ioo (0 : ℝ) 1 := ⟨ht, by linarith⟩
  have hlowI : t / Λ ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos ht hΛ, (div_lt_iff₀ hΛ).mpr (by linarith)⟩
  have hhighI : Λ * t ∈ Ioo (0 : ℝ) 1 := ⟨mul_pos hΛ ht, by nlinarith⟩
  have hbaseCDF (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) :
      heightCDF (K : Set E) e (q u) = u :=
    Measure.cdf_quantile _ (continuous_cdf_map_inner_cond he hK K.isCompact.measure_lt_top.ne)
      hu.1 hu.2
  have hlow : scale * q (t / Λ) ≤ heightQuantile (L : Set E) e t := by
    have h := (heightCDF_dilation_bounds K L e hK hscale hKL hLK (q (t / Λ))).2
    rw [hbaseCDF _ hlowI] at h
    have heq : Λ * (t / Λ) = t := mul_div_cancel₀ _ hΛ.ne'
    change heightCDF (L : Set E) e (scale * q (t / Λ)) ≤ Λ * (t / Λ) at h
    rw [heq] at h
    by_contra hn
    have hlt := (Measure.quantile_lt_iff
      ((volume[|(L : Set E)]).map fun x => ⟪e, x⟫)
      (continuous_cdf_map_inner_cond he hL L.isCompact.measure_lt_top.ne)
      (L.convex.strictMonoOn_cdf_map_inner_cond he hL L.isCompact.measure_lt_top.ne)
      htI.1 htI.2).mp (lt_of_not_ge hn)
    exact (not_lt_of_ge h) hlt
  have hhigh : heightQuantile (L : Set E) e t ≤ q (Λ * t) := by
    apply (Measure.quantile_le_iff _ htI.1 htI.2).mpr
    have h := (heightCDF_dilation_bounds K L e hK hscale hKL hLK (q (Λ * t))).1
    rw [hbaseCDF _ hhighI] at h
    have heq : (Λ * t) / Λ = t := mul_div_cancel_left₀ _ hΛ.ne'
    change (Λ * t) / Λ ≤ _ at h
    rwa [heq] at h
  obtain ⟨x, hx⟩ := K.nonempty
  have hRpos : 0 < R := (norm_nonneg x).trans_lt (hR x hx)
  have hderiv (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) : HasDerivAt q (v u) u :=
    hasDerivAt_heightQuantile K he hK hu
  have hv (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) : 0 ≤ v u :=
    div_nonneg measureReal_nonneg measureReal_nonneg
  have hweighted (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) : min u (1 - u) * v u ≤ 2 * R :=
    weighted_heightQuantileSlope_le K he hdim hK R hR hu
  have hlh : t / Λ ≤ Λ * t :=
    (show t / Λ ≤ t from (div_le_iff₀ hΛ).mpr (by nlinarith)).trans (by nlinarith)
  have hinc₀ := quantile_multiplicative_increment q v (2 * R) (by linarith)
    hderiv hv hweighted ht ht2 hΛ1 hΛ2 (left_mem_Icc.mpr hlh)
  have hinc₁ := quantile_multiplicative_increment q v (2 * R) (by linarith)
    hderiv hv hweighted ht ht2 hΛ1 hΛ2 (right_mem_Icc.mpr hlh)
  have hqR := abs_heightQuantile_lt_of_radius K he hK R hR hlowI
  have hscaled := mul_le_mul_of_nonneg_left (abs_lt.mp hqR).1.le (sub_nonneg.mpr hscale1)
  rw [abs_le] at hinc₀ hinc₁ ⊢
  constructor
  · nlinarith [hinc₀.1]
  · nlinarith [hinc₁.2, mul_nonneg hRpos.le (sub_nonneg.mpr hscale1)]

/-- Uniform quantile control, including both extreme probability tails.
The displacement bound tends linearly to zero as the dilation tends to one. -/
theorem heightQuantile_dilation_bound (K L : ConvexBody E)
    {e : E} (he : ‖e‖ = 1) (hdim : 2 ≤ Module.finrank ℝ E)
    (hK : volume (K : Set E) ≠ 0) (R : ℝ)
    (hR : ∀ x ∈ (K : Set E), ‖x‖ < R)
    {scale : ℝ} (hscale1 : 1 ≤ scale) (hpow : scale ^ Module.finrank ℝ E ≤ 3 / 2)
    (hKL : K ≤ L) (hLK : L ≤ scale • K)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    |heightQuantile (L : Set E) e t - heightQuantile (K : Set E) e t| ≤
      R * (scale - 1) + 4 * R * (scale ^ Module.finrank ℝ E - 1) := by
  by_cases ht2 : t ≤ 1 / 2
  · exact heightQuantile_dilation_bound_left K L he hdim hK R hR hscale1 hpow hKL hLK ht.1 ht2
  · have hL : volume (L : Set E) ≠ 0 :=
      ne_of_gt ((pos_iff_ne_zero.mpr hK).trans_le (measure_mono hKL))
    have hneg : ‖-e‖ = 1 := by simpa only [norm_neg] using he
    have ht' : 1 - t ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have h := heightQuantile_dilation_bound_left K L hneg hdim hK R hR
      hscale1 hpow hKL hLK ht'.1 (by linarith)
    rw [heightQuantile_neg L he hL ht', heightQuantile_neg K he hK ht'] at h
    simpa only [sub_sub_cancel, neg_sub_neg, abs_sub_comm] using h

end RankThreeProjection.QuantileStability
end
end
end DevelopmentSource21

/- Source module: Projection.Rigidity.QuantileRayBound. SHA256: 975b0ae73d72a95cba3cbe111319facbbacd1e3488485c8a0fd555a5680fca3e -/
section DevelopmentSource22






/-!
# A uniform first-order bound for Minkowski-ray quantiles

The same bound works for every unit direction and every probability in (0,1).
Thus domination survives at both probability tails when taking first
variations of expectations. All bodies and quantiles are the actual ones.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped Pointwise RealInnerProductSpace Topology

namespace RankThreeProjection.QuantileStability

theorem tendsto_dilation_power_quotient (C : ℝ) (n : ℕ) :
    Tendsto (fun t : ℝ => ((1 + C * t) ^ n - 1) / t)
      (𝓝[>] 0) (𝓝 ((n : ℝ) * C)) := by
  have hd : HasDerivAt (fun t : ℝ => (1 + C * t) ^ n) ((n : ℝ) * C) 0 := by
    simpa only [id_eq, mul_one, mul_zero, add_zero, one_pow, one_mul] using
      ((((hasDerivAt_id (0 : ℝ)).const_mul C).const_add 1).fun_pow n)
  simpa only [zero_add, mul_zero, add_zero, one_pow, smul_eq_mul,
    div_eq_mul_inv, mul_comm] using hd.tendsto_slope_zero_right

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Uniform domination of the actual first quantile difference quotients.
The comparison body is allowed to have empty interior. -/
theorem uniform_minkowski_quantile_quotient_bound
    (K A : ConvexBody E) (hdim : 2 ≤ Module.finrank ℝ E)
    (hK : (0 : E) ∈ interior (K : Set E)) (hA : (0 : E) ∈ A) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ t : ℝ in 𝓝[>] 0,
      ∀ e : E, ‖e‖ = 1 → ∀ τ ∈ Ioo (0 : ℝ) 1,
        |(heightQuantile ((K + t • A : ConvexBody E) : Set E) e τ -
          heightQuantile (K : Set E) e τ) / t| ≤ B := by
  obtain ⟨C, hC, hsandwich⟩ :=
    RankThreeProjection.Rigidity.minkowski_ray_dilation_sandwich K A hK hA
  obtain ⟨R₀, hR₀, hbound⟩ := K.isBounded.exists_pos_norm_le
  let R : ℝ := R₀ + 1
  have hR : 0 < R := by dsimp [R]; linarith
  have hradius : ∀ x ∈ (K : Set E), ‖x‖ < R := by
    intro x hx
    exact (hbound x hx).trans_lt (by dsimp [R]; linarith)
  let n := Module.finrank ℝ E
  let D : ℝ := (n : ℝ) * C + 1
  let B : ℝ := R * C + 4 * R * D
  have hD : 0 < D := by dsimp [D]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hratio : ∀ᶠ t : ℝ in 𝓝[>] 0,
      ((1 + C * t) ^ n - 1) / t ≤ D := by
    apply ((tendsto_dilation_power_quotient C n).eventually
      (Iio_mem_nhds (show (n : ℝ) * C < D by dsimp [D]; linarith))).mono
    exact fun _ h => h.le
  have hcontinuous : Continuous (fun t : ℝ => (1 + C * t) ^ n) :=
    (continuous_const.add (continuous_const.mul continuous_id)).pow n
  have hpowlim : Tendsto (fun t : ℝ => (1 + C * t) ^ n)
      (𝓝[>] 0) (𝓝 (1 : ℝ)) := by
    simpa only [mul_zero, add_zero, one_pow] using
      hcontinuous.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have hpowsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, (1 + C * t) ^ n ≤ 3 / 2 :=
    (hpowlim.eventually (Iio_mem_nhds (by norm_num : (1 : ℝ) < 3 / 2))).mono
      (fun _ h => h.le)
  have hvolume : volume (K : Set E) ≠ 0 :=
    (Measure.measure_pos_of_nonempty_interior volume ⟨0, hK⟩).ne'
  refine ⟨B, hB, ?_⟩
  filter_upwards [self_mem_nhdsWithin, hratio, hpowsmall] with t ht hquot hp
  change 0 < t at ht
  intro e he τ hτ
  obtain ⟨hleft, hright⟩ := hsandwich t ht.le
  have hlambda : 1 ≤ 1 + C * t := le_add_of_nonneg_right (mul_nonneg hC.le ht.le)
  have hq := heightQuantile_dilation_bound K (K + t • A) he hdim
    hvolume R hradius hlambda hp hleft hright hτ
  rw [abs_div, abs_of_pos ht]
  apply (div_le_iff₀ ht).mpr
  have hpower : (1 + C * t) ^ n - 1 ≤ D * t := (div_le_iff₀ ht).mp hquot
  calc
    _ ≤ R * ((1 + C * t) - 1) + 4 * R * ((1 + C * t) ^ n - 1) := hq
    _ ≤ R * ((1 + C * t) - 1) + 4 * R * (D * t) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hpower (by positivity))
    _ = B * t := by dsimp [B]; ring

end RankThreeProjection.QuantileStability
end
end
end DevelopmentSource22

/- Source module: Projection.Rigidity.QuantileCenteredLimit. SHA256: 2469f0b2ead0d0dac0a0ec392160604656b3d1e5e34367287afe8cdc3bdd1372 -/
section DevelopmentSource23





@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory ProbabilityTheory Filter Module
open scoped Pointwise RealInnerProductSpace Topology

namespace RankThreeProjection.QuantileStability
open VolumePolynomials

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The actual centered quantile limit. All geometric energy and tail bounds
are proved from the actual bodies and AF equality. The remaining scalar
parameter `c` is the derivative of the actual directional centroid; the
separate centroid-variation theorem supplies one vector for these parameters
simultaneously in every direction. -/
theorem actual_centered_quantile_L1_limit {d : ℕ}
    (K A C : ConvexBody E) (hdim : finrank ℝ E = d + 2)
    (hK : (0 : E) ∈ interior (K : Set E)) (hA : (0 : E) ∈ A) (hC : (0 : E) ∈ C)
    (z : ℝ) (hz : 0 < z)
    (hAA : mixedVolume volume (Fin.cons A (Fin.cons A (fun _ : Fin d => K))) = z)
    (hAC : mixedVolume volume (Fin.cons A (Fin.cons C (fun _ : Fin d => K))) = z)
    (hCC : mixedVolume volume (Fin.cons C (Fin.cons C (fun _ : Fin d => K))) = z)
    {e : E} (he : ‖e‖ = 1) (c : ℝ)
    (hmean : HasDerivWithinAt (fun t : ℝ =>
      (∫ x, ⟪e, x⟫ ∂volume[|((K + t • C : ConvexBody E) : Set E)]) -
        ∫ x, ⟪e, x⟫ ∂volume[|((K + t • A : ConvexBody E) : Set E)])
      c (Ici 0) 0) :
    Tendsto (fun t : ℝ => ∫ τ in Ioo (0 : ℝ) 1,
      |(heightQuantile ((K + t • C : ConvexBody E) : Set E) e τ -
          heightQuantile ((K + t • A : ConvexBody E) : Set E) e τ) / t - c|)
      (𝓝[>] 0) (𝓝 0) := by
  let U := Ioo (0 : ℝ) 1
  let μ : Measure ℝ := volume.restrict U
  letI : IsProbabilityMeasure μ := ⟨by simp [μ, U, Real.volume_Ioo]⟩
  have hd : 2 ≤ finrank ℝ E := by omega
  have hK0 : volume (K : Set E) ≠ 0 :=
    (Measure.measure_pos_of_nonempty_interior volume ⟨0, hK⟩).ne'
  have hKV : 0 < volume.real (K : Set E) :=
    ENNReal.toReal_pos hK0 K.isCompact.measure_lt_top.ne
  have hAt (t : ℝ) := minkowski_ray_volume_ne_zero K A hK0 hA t
  have hCt (t : ℝ) := minkowski_ray_volume_ne_zero K C hK0 hC t
  let f : ℝ → ℝ → ℝ := fun t τ =>
    heightQuantile ((K + t • C : ConvexBody E) : Set E) e τ -
      heightQuantile ((K + t • A : ConvexBody E) : Set E) e τ
  let v : ℝ → ℝ → ℝ := fun t τ =>
    heightQuantileSlope ((K + t • C : ConvexBody E) : Set E) e τ -
      heightQuantileSlope ((K + t • A : ConvexBody E) : Set E) e τ
  let F : ℝ → ℝ → ℝ := fun t τ => f t τ / t
  have hfderiv (t τ : ℝ) (hτ : τ ∈ U) : HasDerivAt (f t) (v t τ) τ :=
    (hasDerivAt_heightQuantile (K + t • C) he (hCt t) hτ).sub
      (hasDerivAt_heightQuantile (K + t • A) he (hAt t) hτ)
  have hvcont (t : ℝ) : ContinuousOn (v t) U :=
    (continuousOn_heightQuantileSlope (K + t • C) he (hCt t)).sub
      (continuousOn_heightQuantileSlope (K + t • A) he (hAt t))
  have hFcont (t : ℝ) : ContinuousOn (F t) U :=
    ((continuousOn_heightQuantile (K + t • C) he (hCt t)).sub
      (continuousOn_heightQuantile (K + t • A) he (hAt t))).div_const t
  have hosc_interval {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
      Tendsto (fun t : ℝ => (f t b - f t a) / t) (𝓝[>] 0) (𝓝 0) := by
    have hsub : Icc a b ⊆ U := fun τ hτ => ⟨ha.trans_le hτ.1, hτ.2.trans_lt hb⟩
    exact tendsto_scaled_oscillation_of_energy f v hab
      (Eventually.of_forall (fun t τ hτ => hfderiv t τ (hsub hτ)))
      (Eventually.of_forall (fun t => (hvcont t).mono hsub))
      (actual_quantile_ray_energy_little_o_sq K A C hdim hKV hA hC z hz
        hAA hAC hCC he ha hab hb)
  have hhalf : (1 / 2 : ℝ) ∈ U := ⟨by linarith, by linarith⟩
  have hosc_point (τ : ℝ) (hτ : τ ∈ U) :
      Tendsto (fun t : ℝ => F t τ - F t (1 / 2)) (𝓝[>] 0) (𝓝 0) := by
    rcases le_total (1 / 2 : ℝ) τ with h | h
    · have hlim := hosc_interval hhalf.1 h hτ.2
      apply Filter.Tendsto.congr' _ hlim
      exact Eventually.of_forall (fun t => by dsimp [F]; ring)
    · have hlim := (hosc_interval hτ.1 h hhalf.2).neg
      simp only [neg_zero] at hlim
      apply Filter.Tendsto.congr' _ hlim
      exact Eventually.of_forall (fun t => by dsimp [F]; ring)
  obtain ⟨B₁, hB₁, hboundA⟩ := uniform_minkowski_quantile_quotient_bound K A hd hK hA
  obtain ⟨B₂, hB₂, hboundC⟩ := uniform_minkowski_quantile_quotient_bound K C hd hK hC
  have hbound : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ τ ∈ U, ‖F t τ‖ ≤ B₁ + B₂ := by
    filter_upwards [hboundA, hboundC] with t hta htc
    intro τ hτ
    have ha := hta e he τ hτ
    have hc := htc e he τ hτ
    have heq : F t τ =
        (heightQuantile ((K + t • C : ConvexBody E) : Set E) e τ -
          heightQuantile (K : Set E) e τ) / t -
        (heightQuantile ((K + t • A : ConvexBody E) : Set E) e τ -
          heightQuantile (K : Set E) e τ) / t := by
      dsimp [F, f]
      ring
    rw [heq, Real.norm_eq_abs]
    exact (abs_sub _ _).trans (by linarith)
  have hmeanlim : Tendsto (fun t => ∫ τ, F t τ ∂μ) (𝓝[>] (0 : ℝ)) (𝓝 c) := by
    have hzero :
        ((∫ x, ⟪e, x⟫ ∂volume[|((K + (0 : ℝ) • C : ConvexBody E) : Set E)]) -
          ∫ x, ⟪e, x⟫ ∂volume[|((K + (0 : ℝ) • A : ConvexBody E) : Set E)]) = 0 := by
      simp only [body_zero_smul, add_zero, sub_self]
    have hlim := (hasDerivWithinAt_Ici_zero_iff_div hzero).mp hmean
    apply Filter.Tendsto.congr' _ hlim
    apply Eventually.of_forall
    intro t
    change _ = ∫ τ in U,
      (heightQuantile ((K + t • C : ConvexBody E) : Set E) e τ -
        heightQuantile ((K + t • A : ConvexBody E) : Set E) e τ) / t
    rw [integral_div, integral_sub
      (integrableOn_heightQuantile (K + t • C) e (hCt t))
      (integrableOn_heightQuantile (K + t • A) e (hAt t)),
      integral_heightQuantile (K + t • C) e (hCt t),
      integral_heightQuantile (K + t • A) e (hAt t)]
  have hflat := mean_determines_flat_limit μ F (1 / 2) (B₁ + B₂) c
    (Eventually.of_forall (fun t =>
      ((hFcont t).aemeasurable measurableSet_Ioo).aestronglyMeasurable))
    (hbound.mono (fun t ht => by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with τ hτ
      exact ht τ hτ))
    (hbound.mono (fun t ht => ht (1 / 2) hhalf))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with τ hτ
      exact hosc_point τ hτ)
    hmeanlim
  simpa only [μ, U, F, f, Real.norm_eq_abs] using hflat.2.2

end RankThreeProjection.QuantileStability
end
end
end DevelopmentSource23

/- Source module: Projection.Rigidity.WulffVariation. SHA256: 2131a0f23ffcc4d53d8b73b4ae8a432354cfcbffd0822f7b205e415c3cc8bff0 -/
section DevelopmentSource24






















/-!
# Actual Wulff first variation: a source-preserving dependency extraction

The declaration bodies below are copied from the OpenAI mathematics repository
at commit `4eaee87548250b2682affda7d05d947c05554bae`. Only the support-function,
spherical-measure, gauge, and first-variation declarations needed here are
included; the unrelated Petty projection inequality is not imported.

The extraction script and the exact source-range/hash manifest are retained in
`work/extract_wulff_variation.py` and `work/wulff-extraction-manifest.json`.
Import adaptation and the modern Lean module header are local changes.
-/

@[expose] public section
set_option autoImplicit false

namespace OAI.PettyProjection
noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Pointwise
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

def IsConvexBody {n : ℕ} (K : Set (Space n)) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty

def unitBall (n : ℕ) : Set (Space n) := Metric.closedBall 0 1

def kappa (n : ℕ) : ℝ := volume.real (unitBall n)


end
end OAI.PettyProjection

namespace OAI.PettyProjection.Spherical
noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Pointwise
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev Sphere (n : ℕ) := sphere (0 : Space n) 1

def surface (n : ℕ) : Measure (Sphere n) :=
  (volume : Measure (Space n)).toSphere

def sigma (n : ℕ) : Measure (Sphere n) :=
  (surface n univ)⁻¹ • surface n

instance surface_finite (n : ℕ) : IsFiniteMeasure (surface n) := by
  unfold surface
  infer_instance

lemma surface_ne_zero (n : ℕ) [NeZero n] : surface n ≠ 0 := by
  exact Measure.toSphere_ne_zero _

instance sigma_probability (n : ℕ) [NeZero n] : IsProbabilityMeasure (sigma n) := by
  constructor
  rw [sigma, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel
    (Measure.measure_univ_ne_zero.mpr (surface_ne_zero n)) (measure_ne_top _ _)

instance surface_open_pos (n : ℕ) : (surface n).IsOpenPosMeasure := by
  unfold surface
  infer_instance

instance sigma_open_pos (n : ℕ) : (sigma n).IsOpenPosMeasure := by
  exact Measure.isOpenPosMeasure_smul _ (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))

/-- Spherical means in the probability normalization. -/
def mean {n : ℕ} (f : Sphere n → ℝ) : ℝ := ∫ u, f u ∂sigma n

lemma mean_const (n : ℕ) [NeZero n] (c : ℝ) : mean (fun _ : Sphere n => c) = c := by
  simp [mean]

instance sphere_compact (n : ℕ) : CompactSpace (Sphere n) :=
  isCompact_iff_compactSpace.mp (isCompact_sphere (0 : Space n) 1)

lemma norm_coe {n : ℕ} (u : Sphere n) : ‖(u : Space n)‖ = 1 := by
  simpa only [mem_sphere, dist_zero_right] using u.property


end
end OAI.PettyProjection.Spherical

namespace OAI.PettyProjection
noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Pointwise
/-- The actual support function of a compact body, not a surrogate gauge. -/
def support {n : ℕ} (K : Set (Space n)) (u : Space n) : ℝ :=
  sSup ((fun x => ⟪u,x⟫) '' K)

lemma support_attained {n : ℕ} {K : Set (Space n)} (hK : IsCompact K) (hKn : K.Nonempty)
    (u : Space n) : ∃ x ∈ K, support K u = ⟪u,x⟫ :=
  hK.exists_sSup_image_eq hKn (by fun_prop)

lemma inner_le_support {n : ℕ} {K : Set (Space n)} (hK : IsCompact K)
    {x : Space n} (hx : x ∈ K) (u : Space n) : ⟪u,x⟫ ≤ support K u := by
  exact le_csSup (hK.bddAbove_image (by fun_prop)) (mem_image_of_mem _ hx)

lemma support_le_iff {n : ℕ} {K : Set (Space n)} (hK : IsCompact K) (hKn : K.Nonempty)
    {u : Space n} {a : ℝ} : support K u ≤ a ↔ ∀ x ∈ K, ⟪u,x⟫ ≤ a := by
  constructor
  · intro h x hx; exact (inner_le_support hK hx u).trans h
  · intro h
    obtain ⟨x,hx,he⟩ := support_attained hK hKn u
    rw [he]; exact h x hx

lemma support_continuous {n : ℕ} {K : Set (Space n)} (hK : IsCompact K) :
    Continuous (support K) :=
  hK.continuous_sSup (by fun_prop)

lemma support_lipschitz {n : ℕ} {K : Set (Space n)} (hK : IsCompact K) (hKn : K.Nonempty)
    {R : ℝ≥0} (hR : ∀ x ∈ K, ‖x‖ ≤ R) : LipschitzWith R (support K) := by
  apply LipschitzWith.of_le_add_mul
  intro u v
  obtain ⟨x,hx,he⟩ := support_attained hK hKn u
  rw [he]
  have hi := inner_le_support hK hx v
  have hbound : ⟪u-v,x⟫ ≤ R*dist u v := by
    calc
      _ ≤ ‖u-v‖*‖x‖ := real_inner_le_norm _ _
      _ ≤ ‖u-v‖*R := mul_le_mul_of_nonneg_left (hR x hx) (norm_nonneg _)
      _ = _ := by rw [dist_eq_norm]; ring
  rw [inner_sub_left] at hbound
  linarith

lemma support_smul {n : ℕ} {K : Set (Space n)} (hK : IsCompact K) (hKn : K.Nonempty)
    {r : ℝ} (hr : 0 ≤ r) (u : Space n) : support K (r • u) = r*support K u := by
  apply le_antisymm
  · apply (support_le_iff hK hKn).mpr
    intro x hx
    rw [real_inner_smul_left]
    exact mul_le_mul_of_nonneg_left (inner_le_support hK hx u) hr
  · obtain ⟨x,hx,he⟩ := support_attained hK hKn u
    rw [he]
    simpa only [real_inner_smul_left] using inner_le_support hK hx (r • u)

lemma support_add_le {n : ℕ} {K : Set (Space n)} (hK : IsCompact K) (hKn : K.Nonempty)
    (u v : Space n) : support K (u+v) ≤ support K u+support K v := by
  apply (support_le_iff hK hKn).mpr
  intro x hx
  rw [inner_add_left]
  exact add_le_add (inner_le_support hK hx u) (inner_le_support hK hx v)

lemma support_nonneg {n : ℕ} {K : Set (Space n)} (hK : IsCompact K) (h0 : 0 ∈ K)
    (u : Space n) : 0 ≤ support K u := by
  simpa only [inner_zero_right] using inner_le_support hK h0 u

lemma support_minkowski {n : ℕ} {K L : Set (Space n)}
    (hK : IsCompact K) (hKn : K.Nonempty) (hL : IsCompact L) (hLn : L.Nonempty)
    (u : Space n) : support (K+L) u = support K u+support L u := by
  apply le_antisymm
  · apply (support_le_iff (hK.add hL) (hKn.add hLn)).mpr
    rintro _ ⟨x,hx,y,hy,rfl⟩
    rw [inner_add_right]
    exact add_le_add (inner_le_support hK hx u) (inner_le_support hL hy u)
  · obtain ⟨x,hx,hxe⟩ := support_attained hK hKn u
    obtain ⟨y,hy,hye⟩ := support_attained hL hLn u
    rw [hxe,hye,← inner_add_right]
    exact inner_le_support (hK.add hL) (add_mem_add hx hy) u

lemma support_linear_image {n : ℕ} {K : Set (Space n)} (hK : IsCompact K) (hKn : K.Nonempty)
    (T : Space n →L[ℝ] Space n) (u : Space n) :
    support (T '' K) u = support K (T.adjoint u) := by
  apply le_antisymm
  · apply (support_le_iff (hK.image T.continuous) (hKn.image T)).mpr
    rintro _ ⟨x,hx,rfl⟩
    rw [← ContinuousLinearMap.adjoint_inner_left]
    exact inner_le_support hK hx _
  · obtain ⟨x,hx,he⟩ := support_attained hK hKn (T.adjoint u)
    rw [he,ContinuousLinearMap.adjoint_inner_left]
    exact inner_le_support (hK.image T.continuous) (mem_image_of_mem T hx) u

lemma mem_iff_inner_le_support {n : ℕ} {K : Set (Space n)}
    (hK : IsCompact K) (hc : Convex ℝ K) (hKn : K.Nonempty) {x : Space n} :
    x ∈ K ↔ ∀ u : Space n, ⟪u,x⟫ ≤ support K u := by
  constructor
  · intro hx u; exact inner_le_support hK hx u
  · intro hx
    by_contra hn
    obtain ⟨f,a,hfa,hax⟩ := geometric_hahn_banach_closed_point hc hK.isClosed hn
    let u := (InnerProductSpace.toDual ℝ (Space n)).symm f
    have hu (y : Space n) : ⟪u,y⟫ = f y := by
      change (InnerProductSpace.toDual ℝ (Space n)) u y = f y
      rw [LinearIsometryEquiv.apply_symm_apply]
    obtain ⟨y,hy,he⟩ := support_attained hK hKn u
    have h := hx u
    rw [he,hu,hu] at h
    exact (not_lt_of_ge h) ((hfa y hy).trans hax)

lemma support_eq_iff {n : ℕ} {K L : Set (Space n)}
    (hK : IsCompact K) (hcK : Convex ℝ K) (hKn : K.Nonempty)
    (hL : IsCompact L) (hcL : Convex ℝ L) (hLn : L.Nonempty) :
    support K = support L ↔ K = L := by
  constructor
  · intro h
    ext x
    rw [mem_iff_inner_le_support hK hcK hKn,mem_iff_inner_le_support hL hcL hLn,h]
  · rintro rfl; rfl


end
end OAI.PettyProjection

namespace OAI.PettyProjection.Spherical
noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Pointwise
lemma sphere_ae_of_radial {n : ℕ} {P : Space n → Prop}
    (hP : ∀ᵐ x ∂(volume : Measure (Space n)), P x)
    (hr : ∀ (u : Sphere n) (r : ℝ), 0 < r → P (r • (u : Space n)) → P u) :
    ∀ᵐ (u : Sphere n) ∂sigma n, P (u : Space n) := by
  let ν := Measure.volumeIoiPow (Module.finrank ℝ (Space n) - 1)
  have hν : ν ≠ 0 := by
    intro h
    have he := Measure.volumeIoiPow_apply_Iio (Module.finrank ℝ (Space n) - 1)
      (⟨1, mem_Ioi.mpr one_pos⟩ : Ioi (0 : ℝ))
    change ν _ = _ at he
    rw [h] at he
    have hp : 0 < (1 : ℝ) ^ (Module.finrank ℝ (Space n) - 1 + 1) /
        ((Module.finrank ℝ (Space n) - 1 : ℕ) + 1) := by positivity
    exact (ne_of_gt (ENNReal.ofReal_pos.mpr hp)) he.symm
  let : NeZero ν := ⟨hν⟩
  have hs : ∀ᵐ (x : ({0}ᶜ : Set (Space n))) ∂(volume : Measure (Space n)).comap
      (Subtype.val : ({0}ᶜ : Set (Space n)) → Space n), P (x : Space n) :=
    (ae_restrict_iff_subtype (measurableSet_singleton (0 : Space n)).compl).mp
      (ae_restrict_of_ae hP)
  have hm := (volume : Measure (Space n)).measurePreserving_homeomorphUnitSphereProd
  have hi := hm.symm (homeomorphUnitSphereProd (Space n)).toMeasurableEquiv
  have hh := hi.quasiMeasurePreserving.ae hs
  have hh' : ∀ᵐ z ∂(surface n).prod ν, P (z.2.1 • (z.1 : Space n)) := by
    change ∀ᵐ z ∂(surface n).prod ν, P (((homeomorphUnitSphereProd (Space n)).symm z : ({0}ᶜ : Set (Space n))) : Space n) at hh
    simpa only [homeomorphUnitSphereProd_symm_apply_coe] using hh
  apply Measure.ae_smul_measure (μ := surface n) _ ((surface n univ)⁻¹)
  filter_upwards [Measure.ae_ae_of_ae_prod hh'] with u hu
  obtain ⟨r, hr'⟩ := hu.exists
  exact hr u r r.property hr'


end
end OAI.PettyProjection.Spherical

namespace OAI.PettyProjection
noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Pointwise
open Spherical (Sphere norm_coe)

/-- Intersection of the actual supporting constraints, with no evenness or
convexity condition on the constraint function. -/
def wulff {n : ℕ} (s : Sphere n → ℝ) : Set (Space n) :=
  {x | ∀ u : Sphere n, ⟪(u : Space n),x⟫ ≤ s u}

lemma wulff_closed {n : ℕ} (s : Sphere n → ℝ) : IsClosed (wulff s) := by
  unfold wulff
  rw [ofPred_forall]
  exact isClosed_iInter (fun _ => isClosed_le (by fun_prop) continuous_const)

lemma wulff_convex {n : ℕ} (s : Sphere n → ℝ) : Convex ℝ (wulff s) := by
  intro x hx y hy a b ha hb hab u
  rw [inner_add_right,real_inner_smul_right,real_inner_smul_right]
  calc
    _ ≤ a*s u+b*s u := add_le_add (mul_le_mul_of_nonneg_left (hx u) ha)
      (mul_le_mul_of_nonneg_left (hy u) hb)
    _ = s u := by rw [← add_mul,hab,one_mul]

lemma closedBall_subset_wulff {n : ℕ} {s : Sphere n → ℝ} {r : ℝ}
    (hr : ∀ u, r ≤ s u) : closedBall (0 : Space n) r ⊆ wulff s := by
  intro x hx u
  calc
    _ ≤ ‖(u : Space n)‖*‖x‖ := real_inner_le_norm _ _
    _ = ‖x‖ := by rw [norm_coe,one_mul]
    _ ≤ r := by simpa only [mem_closedBall,dist_zero_right] using hx
    _ ≤ s u := hr u

lemma wulff_subset_closedBall {n : ℕ} {s : Sphere n → ℝ} {R : ℝ}
    (hR : 0 ≤ R) (hs : ∀ u, s u ≤ R) : wulff s ⊆ closedBall (0 : Space n) R := by
  intro x hx
  rw [mem_closedBall,dist_zero_right]
  by_cases h : x = 0
  · simpa [h] using hR
  · let u : Sphere n := ⟨‖x‖⁻¹ • x, by
      rw [mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)]⟩
    have hu : ⟪(u : Space n),x⟫ = ‖x‖ := by
      dsimp only [u]
      rw [real_inner_smul_left,real_inner_self_eq_norm_sq]
      field_simp
    exact hu ▸ (hx u).trans (hs u)

lemma positive_constraint_bounds {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ))
    (hs : ∀ u, 0 < s u) : ∃ m M : ℝ, 0 < m ∧ 0 < M ∧ ∀ u, m ≤ s u ∧ s u ≤ M := by
  have hne : (univ : Set (Sphere n)).Nonempty := by
    obtain ⟨u,hu⟩ := (NormedSpace.sphere_nonempty (x := (0 : Space n))).mpr (by norm_num : (0:ℝ) ≤ 1)
    exact ⟨⟨u,hu⟩,mem_univ _⟩
  obtain ⟨u,_,hu⟩ := isCompact_univ.exists_isMinOn hne s.continuous.continuousOn
  obtain ⟨v,_,hv⟩ := isCompact_univ.exists_isMaxOn hne s.continuous.continuousOn
  exact ⟨s u,s v,hs u,hs v,fun w => ⟨hu (mem_univ w),hv (mem_univ w)⟩⟩

lemma wulff_nhds {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u) :
    wulff s ∈ 𝓝 (0 : Space n) := by
  obtain ⟨m,M,hm,_,hb⟩ := positive_constraint_bounds s hs
  exact Metric.mem_nhds_iff.mpr ⟨m,hm,ball_subset_closedBall.trans
    (closedBall_subset_wulff (fun u => (hb u).1))⟩

lemma wulff_compact {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u) :
    IsCompact (wulff s) := by
  obtain ⟨m,M,_,hM,hb⟩ := positive_constraint_bounds s hs
  exact (isCompact_closedBall (0 : Space n) M).of_isClosed_subset (wulff_closed _)
    (wulff_subset_closedBall hM.le (fun u => (hb u).2))

lemma wulff_body {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u) :
    IsConvexBody (wulff s) :=
  ⟨wulff_compact s hs,wulff_convex s,⟨0,mem_interior_iff_mem_nhds.mpr (wulff_nhds s hs)⟩⟩

lemma wulff_support {n : ℕ} [NeZero n] {K : Set (Space n)}
    (hK : IsCompact K) (hc : Convex ℝ K) (hKn : K.Nonempty) :
    wulff (fun u : Sphere n => support K u) = K := by
  ext x
  rw [mem_iff_inner_le_support hK hc hKn]
  constructor
  · intro h u
    by_cases hu : u = 0
    · subst u
      obtain ⟨y,hy,he⟩ := support_attained hK hKn 0
      simpa only [inner_zero_left] using he.ge
    · let v : Sphere n := ⟨‖u‖⁻¹ • u, by
        rw [mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr hu)]⟩
      have he : u = ‖u‖ • (v : Space n) := by dsimp [v]; rw [smul_inv_smul₀ (norm_ne_zero_iff.mpr hu)]
      rw [he,real_inner_smul_left,support_smul hK hKn (norm_nonneg _)]
      exact mul_le_mul_of_nonneg_left (h v) (norm_nonneg _)
  · intro h u; exact h u

/-- Compact coefficient set of the maximum formula. -/
def wulffCoefficients {n : ℕ} (s : Sphere n → ℝ) : Set (Space n) :=
  range (fun u : Sphere n => (s u)⁻¹ • (u : Space n))

def wulffMax {n : ℕ} (s : Sphere n → ℝ) (x : Space n) : ℝ :=
  support (wulffCoefficients s) x

lemma wulffCoefficients_compact {n : ℕ} (s : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u) :
    IsCompact (wulffCoefficients s) :=
  isCompact_range ((s.continuous.inv₀ (fun u => (hs u).ne')).smul continuous_subtype_val)

lemma wulffCoefficients_nonempty {n : ℕ} [NeZero n] (s : Sphere n → ℝ) :
    (wulffCoefficients s).Nonempty := by
  obtain ⟨u,hu⟩ := (NormedSpace.sphere_nonempty (x := (0 : Space n))).mpr (by norm_num : (0:ℝ) ≤ 1)
  exact ⟨_,⟨⟨u,hu⟩,rfl⟩⟩

lemma wulffMax_attained {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u)
    (x : Space n) : ∃ u : Sphere n, wulffMax s x = ⟪x,(u : Space n)⟫ / s u := by
  obtain ⟨y,⟨u,rfl⟩,he⟩ := support_attained (wulffCoefficients_compact s hs)
    (wulffCoefficients_nonempty s) x
  exact ⟨u,by simpa only [wulffMax,real_inner_smul_right,div_eq_inv_mul] using he⟩

lemma le_wulffMax {n : ℕ} (s : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u)
    (x : Space n) (u : Sphere n) : ⟪x,(u : Space n)⟫ / s u ≤ wulffMax s x := by
  simpa only [wulffMax,real_inner_smul_right,div_eq_inv_mul] using
    inner_le_support (wulffCoefficients_compact s hs) (mem_range_self u) x

lemma wulffMax_pos {n : ℕ} (s : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u)
    {x : Space n} (hx : x ≠ 0) : 0 < wulffMax s x := by
  let u : Sphere n := ⟨‖x‖⁻¹ • x, by
    rw [mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩
  have he : ⟪x,(u : Space n)⟫ = ‖x‖ := by
    dsimp only [u]
    rw [real_inner_smul_right,real_inner_self_eq_norm_sq]
    field_simp
  apply lt_of_lt_of_le _ (le_wulffMax s hs x u)
  rw [he]
  exact div_pos (norm_pos_iff.mpr hx) (hs u)

lemma wulffMax_zero {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u) :
    wulffMax s (0 : Space n) = 0 := by
  obtain ⟨u,he⟩ := wulffMax_attained s hs 0
  simpa only [inner_zero_left,zero_div] using he

lemma mem_smul_wulff {n : ℕ} {s : Sphere n → ℝ} {a : ℝ} (ha : 0 < a) {x : Space n} :
    x ∈ a • wulff s ↔ ∀ u : Sphere n, ⟪x,(u : Space n)⟫ ≤ a*s u := by
  rw [mem_smul_set_iff_inv_smul_mem₀ ha.ne']
  change (∀ u : Sphere n, ⟪(u : Space n),a⁻¹ • x⟫ ≤ s u) ↔ _
  simp_rw [real_inner_smul_right,real_inner_comm (y := x),← div_eq_inv_mul,div_le_iff₀ ha]
  simp only [mul_comm]

lemma gauge_wulff_eq_max {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u)
    (x : Space n) : gauge (wulff s) x = wulffMax s x := by
  by_cases hx : x = 0
  · subst x; rw [gauge_zero,wulffMax_zero s hs]
  have hp := wulffMax_pos s hs hx
  have hmem : x ∈ wulffMax s x • wulff s := by
    apply (mem_smul_wulff hp).mpr
    intro u
    have h := (div_le_iff₀ (hs u)).mp (le_wulffMax s hs x u)
    simpa only [mul_comm] using h
  apply le_antisymm (gauge_le_of_mem hp.le hmem)
  rw [gauge_def]
  refine le_csInf (s := {r : ℝ | r ∈ Ioi 0 ∧ x ∈ r • wulff s})
    ⟨wulffMax s x,hp,hmem⟩ ?_
  rintro a ⟨ha,hax⟩
  obtain ⟨u,he⟩ := wulffMax_attained s hs x
  rw [he]
  exact (div_le_iff₀ (hs u)).mpr ((mem_smul_wulff ha).mp hax u)

lemma gauge_ae_differentiable_sphere {n : ℕ} {K : Set (Space n)}
    (hc : Convex ℝ K) (h0 : K ∈ 𝓝 (0 : Space n)) :
    ∀ᵐ (u : Sphere n) ∂Spherical.sigma n, DifferentiableAt ℝ (gauge K) (u : Space n) := by
  obtain ⟨C,hC⟩ := hc.lipschitz_gauge h0
  apply Spherical.sphere_ae_of_radial hC.ae_differentiableAt
  intro u r hr hd
  have hh : DifferentiableAt ℝ (fun x : Space n => r⁻¹ * gauge K (r • x)) (u : Space n) :=
    (hd.comp (u : Space n) (differentiableAt_id.const_smul r)).const_mul r⁻¹
  have he : (fun x : Space n => r⁻¹ * gauge K (r • x)) = gauge K := by
    funext x
    rw [gauge_smul_of_nonneg (α := ℝ) hr.le,smul_eq_mul,← mul_assoc,
      inv_mul_cancel₀ hr.ne',one_mul]
  rwa [he] at hh


end
end OAI.PettyProjection

namespace OAI

universe uU

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Gradient
namespace PettyProjection
open Spherical (Sphere norm_coe)

lemma support_gradient_of_active {n : ℕ} {C : Set (Space n)}
    (hC : IsCompact C) {x y : Space n} (hy : y ∈ C)
    (hxy : support C x = ⟪x,y⟫)
    (hd : DifferentiableAt ℝ (support C) x) : ∇ (support C) x = y := by
  let l : Space n →L[ℝ] ℝ := InnerProductSpace.toDual ℝ (Space n) y
  have he (z : Space n) : l z = ⟪z,y⟫ := by
    change ⟪y,z⟫ = ⟪z,y⟫
    exact real_inner_comm z y
  have hl : IsLocalMin (fun z => support C z-l z) x := by
    apply Eventually.of_forall
    intro z
    dsimp only
    rw [he,he,hxy,sub_self]
    exact sub_nonneg.mpr (inner_le_support hC hy z)
  have hz := hl.hasFDerivAt_eq_zero (hd.hasFDerivAt.sub l.hasFDerivAt)
  have hd' : fderiv ℝ (support C) x = l := sub_eq_zero.mp hz
  apply ext_inner_right ℝ
  intro z
  rw [inner_gradient_left,hd',he]
  exact real_inner_comm _ _

lemma wulff_gradient_of_active {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ))
    (hs : ∀ u, 0 < s u) {x : Space n} {u : Sphere n}
    (hu : wulffMax s x = ⟪x,(u : Space n)⟫ / s u)
    (hd : DifferentiableAt ℝ (gauge (wulff s)) x) :
    ∇ (gauge (wulff s)) x = (s u)⁻¹ • (u : Space n) := by
  have he : gauge (wulff s) = support (wulffCoefficients s) :=
    funext (gauge_wulff_eq_max s hs)
  rw [he] at hd ⊢
  apply support_gradient_of_active (wulffCoefficients_compact s hs) (mem_range_self u) _ hd
  simpa only [real_inner_smul_right,div_eq_inv_mul,wulffMax] using hu

lemma wulff_active_unique {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ))
    (hs : ∀ u, 0 < s u) {x : Space n} (hd : DifferentiableAt ℝ (gauge (wulff s)) x)
    {u v : Sphere n} (hu : wulffMax s x = ⟪x,(u : Space n)⟫/s u)
    (hv : wulffMax s x = ⟪x,(v : Space n)⟫/s v) : u = v := by
  have he := (wulff_gradient_of_active s hs hu hd).symm.trans (wulff_gradient_of_active s hs hv hd)
  have hn := congrArg norm he
  simp only [norm_smul,norm_coe,mul_one,Real.norm_eq_abs,abs_inv,abs_of_pos (hs u),
    abs_of_pos (hs v)] at hn
  have hsuv : s u = s v := inv_injective hn
  apply Subtype.ext
  rw [hsuv] at he
  exact (smul_right_injective _ (inv_ne_zero (hs v).ne')) he

end PettyProjection
end

noncomputable section
open Set Filter Topology
namespace PettyProjection

/-- Convergence of maximizers at a unique maximum, with a compact parameter
space and joint continuity only at the limiting parameter. -/
lemma selected_max_tendsto {U : Type uU} [TopologicalSpace U] [CompactSpace U]
    {f : ℝ → U → ℝ} {a : ℝ → U} {u₀ : U}
    (hc : ∀ u : U, ContinuousAt (fun p : ℝ × U => f p.1 p.2) (0,u))
    (hm : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ u, f t u ≤ f t (a t))
    (hu : ∀ u, (∀ v, f 0 v ≤ f 0 u) → u = u₀) :
    Tendsto a (𝓝 0) (𝓝 u₀) := by
  apply tendsto_nhds_of_unique_mapClusterPt
  intro u hu'
  obtain ⟨l,hl,hat⟩ := mapClusterPt_iff_ultrafilter.mp hu'
  apply hu
  intro v
  have ht : Tendsto (fun t : ℝ => t) (l : Filter ℝ) (𝓝 0) := hl
  have hv : Tendsto (fun t => f t v) (l : Filter ℝ) (𝓝 (f 0 v)) :=
    (hc v).tendsto.comp (ht.prodMk_nhds tendsto_const_nhds)
  have hav : Tendsto (fun t => f t (a t)) (l : Filter ℝ) (𝓝 (f 0 u)) :=
    (hc u).tendsto.comp (ht.prodMk_nhds hat)
  exact le_of_tendsto_of_tendsto hv hav (hl (hm.mono (fun t h => h v)))

lemma quotient_bounds {a b z t : ℝ} (ht : t ≠ 0) (hl : t*a ≤ z) (hh : z ≤ t*b) :
    min a b ≤ z/t ∧ z/t ≤ max a b := by
  have he : z/t*t = z := div_mul_cancel₀ z ht
  rcases lt_or_gt_of_ne ht with ht | ht
  · have hb : b ≤ z/t := by nlinarith
    have ha : z/t ≤ a := by nlinarith
    exact ⟨(min_le_right a b).trans hb,ha.trans (le_max_left a b)⟩
  · have ha : a ≤ z/t := by nlinarith
    have hb : z/t ≤ b := by nlinarith
    exact ⟨(min_le_left a b).trans ha,hb.trans (le_max_right a b)⟩

/-- Envelope differentiation from an exact continuous difference quotient.
The statement does not require a smooth boundary or a smooth maximizer. -/
lemma hasDerivAt_selected_max {U : Type uU} [TopologicalSpace U] [CompactSpace U]
    {f d : ℝ → U → ℝ} {q : ℝ → ℝ} {a : ℝ → U} {u₀ : U}
    (hc : ∀ u : U, ContinuousAt (fun p : ℝ × U => f p.1 p.2) (0,u))
    (hd : ContinuousAt (fun p : ℝ × U => d p.1 p.2) (0,u₀))
    (hq : ∀ᶠ t in 𝓝 (0 : ℝ), q t = f t (a t) ∧ ∀ u, f t u ≤ q t)
    (hq₀ : q 0 = f 0 u₀) (hm₀ : ∀ u, f 0 u ≤ q 0)
    (hu : ∀ u, (∀ v, f 0 v ≤ f 0 u) → u = u₀)
    (he : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ u, f t u-f 0 u = t*d t u) :
    HasDerivAt q (d 0 u₀) 0 := by
  have ha : Tendsto a (𝓝 0) (𝓝 u₀) := selected_max_tendsto hc
    (hq.mono (fun t h u => h.1 ▸ h.2 u)) hu
  have hd₀ : Tendsto (fun t => d t u₀) (𝓝 0) (𝓝 (d 0 u₀)) :=
    hd.tendsto.comp (tendsto_id.prodMk_nhds tendsto_const_nhds)
  have hda : Tendsto (fun t => d t (a t)) (𝓝 0) (𝓝 (d 0 u₀)) :=
    hd.tendsto.comp (tendsto_id.prodMk_nhds ha)
  have hlo : Tendsto (fun t => min (d t u₀) (d t (a t))) (𝓝 0) (𝓝 (d 0 u₀)) := by
    simpa only [min_self] using hd₀.min hda
  have hhi : Tendsto (fun t => max (d t u₀) (d t (a t))) (𝓝 0) (𝓝 (d 0 u₀)) := by
    simpa only [max_self] using hd₀.max hda
  rw [hasDerivAt_iff_tendsto_slope_zero]
  simp only [zero_add,smul_eq_mul,← div_eq_inv_mul]
  have hb : ∀ᶠ t in 𝓝[≠] (0 : ℝ), min (d t u₀) (d t (a t)) ≤ (q t-q 0)/t ∧
      (q t-q 0)/t ≤ max (d t u₀) (d t (a t)) := by
    filter_upwards [hq.filter_mono nhdsWithin_le_nhds,he.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t ht he ht0
    have htn : t ≠ 0 := ht0
    have hl : t*d t u₀ ≤ q t-q 0 := by
      rw [← he u₀,hq₀]
      exact sub_le_sub_right (ht.2 u₀) _
    have hh : q t-q 0 ≤ t*d t (a t) := by
      rw [← he (a t),ht.1]
      exact sub_le_sub_left (hm₀ (a t)) _
    exact quotient_bounds htn hl hh
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (hlo.mono_left nhdsWithin_le_nhds) (hhi.mono_left nhdsWithin_le_nhds)
    (hb.mono (fun _ h => h.1)) (hb.mono (fun _ h => h.2))

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Gradient
namespace PettyProjection
open Spherical (Sphere norm_coe)

lemma positive_constraints_eventually {n : ℕ} [NeZero n]
    (s φ : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u) :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), ∀ u, m ≤ (s+t • φ) u ∧ (s+t • φ) u ≤ M) := by
  obtain ⟨a,b,ha,hb,hab⟩ := positive_constraint_bounds s hs
  refine ⟨a/2,b+a/2,by positivity,by positivity,?_⟩
  have ht : ∀ᶠ t in 𝓝 (0 : ℝ), |t| *(‖φ‖+1) < a/2 := by
    have h : Tendsto (fun t : ℝ => |t| *(‖φ‖+1)) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_abs.tendsto (0:ℝ)).mul_const (‖φ‖+1)
    exact h.eventually (eventually_lt_nhds (by positivity))
  filter_upwards [ht] with t ht u
  have hφ : |φ u| ≤ ‖φ‖ := φ.norm_coe_le_norm u
  have hbound : |t*φ u| ≤ |t| *(‖φ‖+1) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hφ.trans (by linarith)) (abs_nonneg _)
  have hlo := neg_abs_le (t*φ u)
  have hhi := le_abs_self (t*φ u)
  have hh := hab u
  change a/2 ≤ s u+t*φ u ∧ s u+t*φ u ≤ b+a/2
  constructor <;> linarith

lemma positive_constraints_nhds {n : ℕ} [NeZero n]
    (s φ : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∀ u, 0 < (s+t • φ) u := by
  obtain ⟨m,M,hm,_,he⟩ := positive_constraints_eventually s φ hs
  exact he.mono (fun _ h u => hm.trans_le (h u).1)

lemma wulff_derivative_active {n : ℕ} [NeZero n]
    (s φ : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u) {x : Space n}
    (hd : DifferentiableAt ℝ (gauge (wulff s)) x) {u₀ : Sphere n}
    (hu₀ : wulffMax s x = ⟪x,(u₀ : Space n)⟫/s u₀) :
    HasDerivAt (fun t : ℝ => gauge (wulff ⇑(s+t • φ)) x)
      (-(gauge (wulff s) x)*φ u₀/s u₀) 0 := by
  classical
  let f : ℝ → Sphere n → ℝ := fun t u => ⟪x,(u : Space n)⟫/(s u+t*φ u)
  let d : ℝ → Sphere n → ℝ := fun t u => -(⟪x,(u : Space n)⟫*φ u)/(s u*(s u+t*φ u))
  let a : ℝ → Sphere n := fun t => if hp : ∀ u, 0 < (s+t • φ) u then
    (wulffMax_attained (s+t • φ) hp x).choose else u₀
  have hpos := positive_constraints_nhds s φ hs
  have hq : ∀ᶠ t in 𝓝 (0 : ℝ), gauge (wulff ⇑(s+t • φ)) x = f t (a t) ∧
      ∀ u, f t u ≤ gauge (wulff ⇑(s+t • φ)) x := by
    filter_upwards [hpos] with t ht
    rw [gauge_wulff_eq_max (s+t • φ) ht]
    constructor
    · dsimp only [a]
      rw [dite_eq_left ht]
      exact (wulffMax_attained (s+t • φ) ht x).choose_spec
    · intro u; exact le_wulffMax (s+t • φ) ht x u
  have hq0 : gauge (wulff (s+(0:ℝ) • φ)) x = f 0 u₀ := by
    simpa only [zero_smul,add_zero,f,zero_mul] using (gauge_wulff_eq_max s hs x).trans hu₀
  have hm0 : ∀ u, f 0 u ≤ gauge (wulff (s+(0:ℝ) • φ)) x := by
    intro u
    simpa only [zero_smul,add_zero,f,zero_mul,gauge_wulff_eq_max s hs x] using le_wulffMax s hs x u
  have hc (u : Sphere n) : ContinuousAt (fun p : ℝ × Sphere n => f p.1 p.2) (0,u) := by
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · simpa using (hs u).ne'
  have hdc : ContinuousAt (fun p : ℝ × Sphere n => d p.1 p.2) (0,u₀) := by
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · simpa using mul_ne_zero (hs u₀).ne' (hs u₀).ne'
  have hu : ∀ u, (∀ v, f 0 v ≤ f 0 u) → u = u₀ := by
    intro u h
    apply wulff_active_unique s hs hd _ hu₀
    apply le_antisymm
    · simpa only [f,zero_mul,add_zero,← hu₀] using h u₀
    · exact le_wulffMax s hs x u
  have he : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ u, f t u-f 0 u = t*d t u := by
    filter_upwards [hpos] with t ht u
    have hst : s u+t*φ u ≠ 0 := (ht u).ne'
    dsimp only [f,d]
    simp only [zero_mul,add_zero]
    field_simp [hst,(hs u).ne']
    ring
  have h := hasDerivAt_selected_max hc hdc hq hq0 hm0 hu he
  have he0 : d 0 u₀ = -(gauge (wulff s) x)*φ u₀/s u₀ := by
    rw [gauge_wulff_eq_max s hs x,hu₀]
    dsimp [d]
    ring
  rwa [he0] at h

/-- Wulff variation against an actual continuous positively homogeneous test.
No symmetry or boundary smoothness is assumed. -/
theorem wulff_derivative {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ))
    (hs : ∀ u, 0 < s u) (φ : Space n → ℝ) (hφ : Continuous φ)
    (hh : ∀ (a : ℝ), 0 < a → ∀ x, φ (a • x) = a*φ x)
    {x : Space n} (hd : DifferentiableAt ℝ (gauge (wulff s)) x) :
    HasDerivAt (fun t : ℝ => gauge (wulff (s+t • (⟨fun u : Sphere n => φ u,
      hφ.comp continuous_subtype_val⟩ : C(Sphere n,ℝ)))) x)
      (-(gauge (wulff s) x)*φ (∇ (gauge (wulff s)) x)) 0 := by
  obtain ⟨u,hu⟩ := wulffMax_attained s hs x
  have he := wulff_gradient_of_active s hs hu hd
  have h := wulff_derivative_active s ⟨fun u : Sphere n => φ u,hφ.comp continuous_subtype_val⟩ hs hd hu
  rw [he,hh _ (inv_pos.mpr (hs u))]
  convert h using 1
  dsimp
  ring

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace
namespace PettyProjection
open Spherical (Sphere norm_coe surface sigma mean)

lemma kappa_pos (n : ℕ) : 0 < kappa n := by
  unfold kappa unitBall
  exact ENNReal.toReal_pos (measure_closedBall_pos volume 0 (by norm_num)).ne'
    (measure_closedBall_lt_top.ne)

lemma surface_real_univ (n : ℕ) [NeZero n] : (surface n).real univ = n*kappa n := by
  rw [surface,Measure.toSphere_real_apply_univ]
  simp only [finrank_euclideanSpace_fin]
  congr 1
  exact congrArg ENNReal.toReal (Measure.addHaar_closedBall_eq_addHaar_ball volume (0 : Space n) (1:ℝ)).symm

/-- Polar integration of an arbitrary convex neighborhood of zero; the body
need not be symmetric or have a smooth boundary. -/
lemma gauge_volume_lintegral {n : ℕ} [NeZero n] {K : Set (Space n)}
    (hc : Convex ℝ K) (h0 : K ∈ 𝓝 (0 : Space n))
    (hp : ∀ u : Sphere n, 0 < gauge K (u : Space n)) :
    volume K = ∫⁻ u : Sphere n, ENNReal.ofReal ((gauge K (u : Space n))⁻¹ ^ n / n)
      ∂surface n := by
  let ν := Measure.volumeIoiPow (Module.finrank ℝ (Space n)-1)
  let A : Set ({0}ᶜ : Set (Space n)) := Subtype.val ⁻¹' interior K
  let S : Set (Sphere n × Ioi (0:ℝ)) :=
    {z | z.2.1 < (gauge K (z.1 : Space n))⁻¹}
  have hA : MeasurableSet A := isOpen_interior.measurableSet.preimage measurable_subtype_coe
  have hS : MeasurableSet S := by
    apply isOpen_lt (by fun_prop) ?_ |>.measurableSet
    exact ((continuous_gauge hc h0).comp (continuous_subtype_val.comp continuous_fst)).inv₀
      (fun z => (hp z.1).ne')
  have he : (homeomorphUnitSphereProd (Space n)).symm ⁻¹' A = S := by
    ext z
    change (↑((homeomorphUnitSphereProd (Space n)).symm z) : Space n) ∈ interior K ↔ _
    rw [homeomorphUnitSphereProd_symm_apply_coe,← gauge_lt_one_iff_mem_interior hc h0,
      gauge_smul_of_nonneg (α := ℝ) z.2.property.le]
    change (z.2 : ℝ)*gauge K (z.1 : Space n) < 1 ↔ (z.2 : ℝ) < (gauge K (z.1 : Space n))⁻¹
    rw [inv_eq_one_div,lt_div_iff₀ (hp z.1)]
  have hm := ((volume : Measure (Space n)).measurePreserving_homeomorphUnitSphereProd).symm
    (homeomorphUnitSphereProd (Space n)).toMeasurableEquiv
  have hm' := hm.measure_preimage hA.nullMeasurableSet
  change (surface n).prod ν ((homeomorphUnitSphereProd (Space n)).symm ⁻¹' A) = _ at hm'
  rw [he, ((MeasurableEmbedding.subtype_coe (measurableSet_singleton (0 : Space n)).compl)).comap_apply] at hm'
  have hi : Subtype.val '' A = interior K \ {0} := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩; exact ⟨hy,y.property⟩
    · intro hx; exact ⟨⟨x,hx.2⟩,hx.1,rfl⟩
  rw [hi,measure_sdiff_null (measure_singleton _),
    measure_interior_of_null_frontier (hc.addHaar_frontier volume)] at hm'
  rw [← hm',Measure.prod_apply hS]
  apply lintegral_congr
  intro u
  have hu : Prod.mk u ⁻¹' S = Iio (⟨(gauge K (u : Space n))⁻¹,inv_pos.mpr (hp u)⟩ : Ioi (0:ℝ)) := rfl
  rw [hu,Measure.volumeIoiPow_apply_Iio]
  have hn : n-1+1 = n := Nat.sub_add_cancel (NeZero.one_le : 1 ≤ n)
  have hnR := congrArg (fun j : ℕ => (j : ℝ)) hn
  simp only [Nat.cast_add,Nat.cast_one] at hnR
  simp only [finrank_euclideanSpace_fin,hn,hnR]

lemma gauge_volume {n : ℕ} [NeZero n] {K : Set (Space n)}
    (hc : Convex ℝ K) (h0 : K ∈ 𝓝 (0 : Space n))
    (hp : ∀ u : Sphere n, 0 < gauge K (u : Space n)) :
    volume.real K = kappa n * mean (fun u : Sphere n => (gauge K (u : Space n))⁻¹ ^ n) := by
  have hcont : Continuous (fun u : Sphere n => (gauge K (u : Space n))⁻¹ ^ n) :=
    (((continuous_gauge hc h0).comp continuous_subtype_val).inv₀ (fun u => (hp u).ne')).pow n
  have hnn : ∀ u : Sphere n, 0 ≤ (gauge K (u : Space n))⁻¹ ^ n := fun u => pow_nonneg (inv_nonneg.mpr (hp u).le) n
  have hv := congrArg ENNReal.toReal (gauge_volume_lintegral hc h0 hp)
  rw [← ofReal_integral_eq_lintegral_ofReal (hcont.div_const n |>.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)) (Eventually.of_forall (fun u => div_nonneg (hnn u) (Nat.cast_nonneg n))),
    ENNReal.toReal_ofReal (integral_nonneg (fun u => div_nonneg (hnn u) (Nat.cast_nonneg n))),
    integral_div] at hv
  change volume.real K = _ at hv
  rw [hv,mean,sigma,integral_smul_measure,ENNReal.toReal_inv,smul_eq_mul]
  change _ = kappa n * (((surface n).real univ)⁻¹ * _)
  rw [surface_real_univ]
  field_simp [(kappa_pos n).ne',(Nat.cast_pos.mpr (NeZero.pos n) : (0:ℝ)<n).ne']

lemma wulff_volume {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u) :
    volume.real (wulff s) = kappa n * mean (fun u : Sphere n => (gauge (wulff s) (u : Space n))⁻¹ ^ n) := by
  apply gauge_volume (wulff_convex s) (wulff_nhds s hs)
  intro u
  rw [gauge_wulff_eq_max s hs]
  exact wulffMax_pos s hs (by intro h; simpa [h] using norm_coe u)

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace
namespace PettyProjection
open Spherical (Sphere norm_coe)

lemma wulff_sphere_gauge_bounds {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ))
    {m M : ℝ} (hm : 0 < m) (hs : ∀ u, m ≤ s u ∧ s u ≤ M)
    (u : Sphere n) : M⁻¹ ≤ gauge (wulff s) (u : Space n) ∧
      gauge (wulff s) (u : Space n) ≤ m⁻¹ := by
  have hp : ∀ v, 0 < s v := fun v => hm.trans_le (hs v).1
  rw [gauge_wulff_eq_max s hp]
  constructor
  · have h := le_wulffMax s hp (u : Space n) u
    rw [real_inner_self_eq_norm_sq,norm_coe,one_pow,one_div] at h
    exact (inv_anti₀ (hp u) (hs u).2).trans h
  · obtain ⟨v,hv⟩ := wulffMax_attained s hp (u : Space n)
    rw [hv]
    have hi : ⟪(u : Space n),(v : Space n)⟫ ≤ 1 := by
      simpa only [norm_coe,one_mul] using real_inner_le_norm (u : Space n) (v : Space n)
    calc
      _ ≤ 1 / s v := div_le_div_of_nonneg_right hi (hp v).le
      _ ≤ m⁻¹ := by simpa only [one_div] using inv_anti₀ hm (hs v).1

lemma quotient_perturb_bound {a b c t r m B : ℝ} (hm : 0 < m)
    (ht : m ≤ b+t*c) (hr : m ≤ b+r*c) (ha : |a| ≤ 1) (hc : |c| ≤ B) :
    |a/(b+t*c)-a/(b+r*c)| ≤ (B/m^2)*|t-r| := by
  have ht0 := hm.trans_le ht
  have hr0 := hm.trans_le hr
  have hB : 0 ≤ B := (abs_nonneg c).trans hc
  have he : a/(b+t*c)-a/(b+r*c) = a*c*(r-t)/((b+t*c)*(b+r*c)) := by
    rw [div_sub_div _ _ ht0.ne' hr0.ne']
    congr 1
    ring
  rw [he,abs_div,abs_mul,abs_mul,abs_mul,abs_of_pos ht0,abs_of_pos hr0,abs_sub_comm r t]
  calc
    _ ≤ (1*B)*|t-r|/(m*m) := by gcongr
    _ = _ := by ring

lemma wulff_gauge_param_sub_le {n : ℕ} [NeZero n] (s φ : C(Sphere n,ℝ))
    {m t r : ℝ} (hm : 0 < m) (ht : ∀ u, m ≤ (s+t • φ) u)
    (hr : ∀ u, m ≤ (s+r • φ) u) (u : Sphere n) :
    gauge (wulff ⇑(s+t • φ)) (u : Space n)-gauge (wulff ⇑(s+r • φ)) (u : Space n) ≤
      (‖φ‖/m^2)*|t-r| := by
  have htp : ∀ v, 0 < (s+t • φ) v := fun v => hm.trans_le (ht v)
  have hrp : ∀ v, 0 < (s+r • φ) v := fun v => hm.trans_le (hr v)
  rw [gauge_wulff_eq_max (s+t • φ) htp,gauge_wulff_eq_max (s+r • φ) hrp]
  obtain ⟨v,hv⟩ := wulffMax_attained (s+t • φ) htp (u : Space n)
  rw [hv]
  have hi : |⟪(u : Space n),(v : Space n)⟫| ≤ 1 := by
    simpa only [norm_coe,one_mul] using abs_real_inner_le_norm (u : Space n) (v : Space n)
  calc
    _ ≤ ⟪(u : Space n),(v : Space n)⟫/(s+t • φ) v - ⟪(u : Space n),(v : Space n)⟫/(s+r • φ) v :=
      sub_le_sub_left (le_wulffMax (s+r • φ) hrp _ v) _
    _ ≤ |⟪(u : Space n),(v : Space n)⟫/(s+t • φ) v - ⟪(u : Space n),(v : Space n)⟫/(s+r • φ) v| := le_abs_self _
    _ ≤ _ := quotient_perturb_bound hm (ht v) (hr v) hi (φ.norm_coe_le_norm v)

lemma wulff_gauge_param_lipschitz {n : ℕ} [NeZero n] (s φ : C(Sphere n,ℝ))
    {m : ℝ} (hm : 0 < m) {T : Set ℝ} (hT : ∀ t ∈ T, ∀ u, m ≤ (s+t • φ) u)
    (u : Sphere n) : LipschitzOnWith ⟨‖φ‖/m^2,by positivity⟩
      (fun t : ℝ => gauge (wulff ⇑(s+t • φ)) (u : Space n)) T := by
  apply LipschitzOnWith.of_dist_le_mul
  intro t ht r hr
  change |gauge (wulff ⇑(s+t • φ)) (u : Space n)-gauge (wulff ⇑(s+r • φ)) (u : Space n)| ≤ (‖φ‖/m^2)*|t-r|
  apply abs_le.mpr
  constructor
  · have h := wulff_gauge_param_sub_le s φ hm (hT r hr) (hT t ht) u
    rw [abs_sub_comm r t] at h
    linarith
  · exact wulff_gauge_param_sub_le s φ hm (hT t ht) (hT r hr) u

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Gradient
namespace PettyProjection
open Spherical (Sphere norm_coe sigma mean)

lemma measurable_gradient {n : ℕ} (f : Space n → ℝ) : Measurable (gradient f) := by
  exact (InnerProductSpace.toDual ℝ (Space n)).symm.continuous.measurable.comp (measurable_fderiv ℝ f)

lemma wulff_invpow_param_lipschitz {n : ℕ} [NeZero n]
    (s φ : C(Sphere n,ℝ)) (hs : ∀ u,0 < s u) :
    ∃ T ∈ 𝓝 (0 : ℝ), ∃ C : ℝ≥0, ∀ u : Sphere n,
      LipschitzOnWith C (fun t : ℝ => (gauge (wulff ⇑(s+t • φ)) (u : Space n))⁻¹ ^ n) T := by
  obtain ⟨m,M,hm,hM,he⟩ := positive_constraints_eventually s φ hs
  let T : Set ℝ := {t | ∀ u, m ≤ (s+t • φ) u ∧ (s+t • φ) u ≤ M}
  have hT : T ∈ 𝓝 (0 : ℝ) := he
  have hc : ContDiffOn ℝ 1 (fun a : ℝ => a⁻¹^n) (Icc M⁻¹ m⁻¹) := by
    intro a ha
    exact ((contDiffAt_id.inv ((inv_pos.mpr hM).trans_le ha.1).ne').pow n).contDiffWithinAt
  obtain ⟨D,hD⟩ := hc.exists_lipschitzOnWith (by norm_num) (convex_Icc _ _) isCompact_Icc
  let C : ℝ≥0 := ⟨‖φ‖/m^2,by positivity⟩
  refine ⟨T,hT,D*C,?_⟩
  intro u
  apply hD.comp (wulff_gauge_param_lipschitz s φ hm (fun t ht v => (ht v).1) u)
  intro t ht
  exact wulff_sphere_gauge_bounds (s+t • φ) hm ht u

lemma wulff_invpow_derivative {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ))
    (hs : ∀ u,0 < s u) (φ : Space n → ℝ) (hφ : Continuous φ)
    (hh : ∀ (a : ℝ),0 < a → ∀ x,φ (a • x)=a*φ x)
    {u : Sphere n} (hd : DifferentiableAt ℝ (gauge (wulff s)) (u : Space n)) :
    HasDerivAt (fun t : ℝ => (gauge (wulff ⇑(s+t • (⟨fun v : Sphere n => φ v,
      hφ.comp continuous_subtype_val⟩ : C(Sphere n,ℝ)))) (u : Space n))⁻¹^n)
      (n*(gauge (wulff s) (u : Space n))⁻¹^n*φ (∇ (gauge (wulff s)) (u : Space n))) 0 := by
  have hp : 0 < gauge (wulff s) (u : Space n) := by
    rw [gauge_wulff_eq_max s hs]
    exact wulffMax_pos s hs (by intro h; simpa [h] using norm_coe u)
  have h := ((wulff_derivative s hs φ hφ hh hd).inv
    (by simpa only [zero_smul,add_zero] using hp.ne')).pow n
  simp only [zero_smul,add_zero] at h
  apply h.congr_deriv
  simp only [Pi.inv_apply,zero_smul,add_zero]
  let q := gauge (wulff s) (u : Space n)
  have hn : n-1+1 = n := Nat.sub_add_cancel (NeZero.one_le : 1 ≤ n)
  have he : (q⁻¹)^(n-1)*q⁻¹ = (q⁻¹)^n := by rw [← pow_succ,hn]
  change (n:ℝ)*q⁻¹^(n-1)*(-(-q*_)/q^2) = (n:ℝ)*q⁻¹^n*_
  rw [← he]
  field_simp [show q ≠ 0 from hp.ne']

/-- Actual two-sided first variation in positive Wulff constraints. This is
valid for arbitrary continuous degree-one tests, not only support functions. -/
theorem wulff_volume_derivative {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ))
    (hs : ∀ u,0 < s u) (φ : Space n → ℝ) (hφ : Continuous φ)
    (hh : ∀ (a : ℝ),0 < a → ∀ x,φ (a • x)=a*φ x) :
    HasDerivAt (fun t : ℝ => volume.real (wulff ⇑(s+t • (⟨fun u : Sphere n => φ u,
      hφ.comp continuous_subtype_val⟩ : C(Sphere n,ℝ)))))
      (n*kappa n*mean (fun u : Sphere n => (gauge (wulff s) (u : Space n))⁻¹^n*
        φ (∇ (gauge (wulff s)) (u : Space n)))) 0 := by
  let φs : C(Sphere n,ℝ) := ⟨fun u => φ u,hφ.comp continuous_subtype_val⟩
  let F : ℝ → Sphere n → ℝ := fun t u => (gauge (wulff ⇑(s+t • φs)) (u : Space n))⁻¹^n
  let F' : Sphere n → ℝ := fun u => (n:ℝ)*(gauge (wulff s) (u : Space n))⁻¹^n*
    φ (∇ (gauge (wulff s)) (u : Space n))
  have hg : Continuous (gauge (wulff s)) := continuous_gauge (wulff_convex s) (wulff_nhds s hs)
  have hgp : ∀ u : Sphere n,0 < gauge (wulff s) (u : Space n) := by
    intro u
    rw [gauge_wulff_eq_max s hs]
    exact wulffMax_pos s hs (by intro h; simpa [h] using norm_coe u)
  have hc : Continuous (F 0) := by
    change Continuous (fun u : Sphere n => (gauge (wulff ⇑(s+0 • φs)) (u : Space n))⁻¹^n)
    simp only [zero_smul,add_zero]
    exact ((hg.comp continuous_subtype_val).inv₀ (fun u => (hgp u).ne')).pow n
  obtain ⟨T,hT,C,hC⟩ := wulff_invpow_param_lipschitz s φs hs
  have hFm : ∀ᶠ t in 𝓝 (0:ℝ), AEStronglyMeasurable (F t) (sigma n) := by
    filter_upwards [positive_constraints_nhds s φs hs] with t ht
    exact (((continuous_gauge (wulff_convex _) (wulff_nhds (s+t • φs) ht)).comp
      continuous_subtype_val).measurable.inv.pow_const n).aestronglyMeasurable
  have hF'm : AEStronglyMeasurable F' (sigma n) := by
    apply Measurable.aestronglyMeasurable
    exact (measurable_const.mul ((hg.measurable.comp measurable_subtype_coe).inv.pow_const n)).mul
      (hφ.measurable.comp ((measurable_gradient _).comp measurable_subtype_coe))
  have hder : ∀ᵐ u ∂sigma n, HasDerivAt (fun t => F t u) (F' u) 0 := by
    filter_upwards [gauge_ae_differentiable_sphere (wulff_convex s) (wulff_nhds s hs)] with u hu
    exact wulff_invpow_derivative s hs φ hφ hh hu
  have hI := (hasDerivAt_integral_of_dominated_loc_of_lip hT hFm
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) hF'm
    (Eventually.of_forall (fun u => by simpa only [Real.nnabs_coe] using hC u))
    (integrable_const (C:ℝ)) hder).2
  have he : (fun t => volume.real (wulff ⇑(s+t • φs))) =ᶠ[𝓝 (0:ℝ)]
      (fun t => kappa n * ∫ u,F t u ∂sigma n) := by
    filter_upwards [positive_constraints_nhds s φs hs] with t ht
    exact wulff_volume (s+t • φs) ht
  have h := (hI.const_mul (kappa n)).congr_of_eventuallyEq he
  apply h.congr_deriv
  dsimp only [F']
  simp_rw [mul_assoc (n:ℝ)]
  rw [integral_const_mul]
  dsimp only [mean]
  ring

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Pointwise Gradient
namespace PettyProjection
open Spherical (Sphere norm_coe sigma mean)

lemma support_smul_set {n : ℕ} {K : Set (Space n)} (hK : IsCompact K) (hKn : K.Nonempty)
    {t : ℝ} (ht : 0 ≤ t) (u : Space n) : support (t • K) u = t*support K u := by
  have hn : (t • K).Nonempty := by obtain ⟨x,hx⟩ := hKn; exact ⟨t • x,smul_mem_smul_set hx⟩
  apply le_antisymm
  · apply (support_le_iff (hK.smul t) hn).mpr
    rintro _ ⟨x,hx,rfl⟩
    rw [real_inner_smul_right]
    exact mul_le_mul_of_nonneg_left (inner_le_support hK hx u) ht
  · obtain ⟨x,hx,he⟩ := support_attained hK hKn u
    rw [he]
    simpa only [real_inner_smul_right] using
      inner_le_support (hK.smul t) (smul_mem_smul_set hx) u

lemma support_pos_of_nhds {n : ℕ} {K : Set (Space n)} (hK : IsCompact K)
    (h0 : K ∈ 𝓝 (0 : Space n)) (u : Sphere n) : 0 < support K u := by
  obtain ⟨r,hr,hrK⟩ := Metric.mem_nhds_iff.mp h0
  have hx : (r/2) • (u : Space n) ∈ K := by
    apply hrK
    rw [mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity),norm_coe,mul_one]
    linarith
  have h := inner_le_support hK hx (u : Space n)
  rw [real_inner_smul_right,real_inner_self_eq_norm_sq,norm_coe,one_pow,mul_one] at h
  linarith

/-- First-variation identity for actual Minkowski addition; the added
set is allowed to have any dimension. -/
theorem minkowski_volume_derivative {n : ℕ} [NeZero n] {K M : Set (Space n)}
    (hK : IsCompact K) (hcK : Convex ℝ K) (h0 : K ∈ 𝓝 (0 : Space n))
    (hM : IsCompact M) (hcM : Convex ℝ M) (hMn : M.Nonempty) :
    HasDerivWithinAt (fun t : ℝ => volume.real (K+t • M))
      (n*kappa n*mean (fun u : Sphere n => (gauge K (u : Space n))⁻¹^n*
        support M (∇ (gauge K) (u : Space n)))) (Ici 0) 0 := by
  have hKn : K.Nonempty := ⟨0,mem_of_mem_nhds h0⟩
  let s : C(Sphere n,ℝ) := ⟨fun u => support K u,(support_continuous hK).comp continuous_subtype_val⟩
  have hs : ∀ u,0 < s u := support_pos_of_nhds hK h0
  let φ : C(Sphere n,ℝ) := ⟨fun u => support M u,(support_continuous hM).comp continuous_subtype_val⟩
  have he : ∀ t : ℝ, 0 ≤ t → wulff ⇑(s+t • φ) = K+t • M := by
    intro t ht
    have hf : ⇑(s+t • φ) = fun u : Sphere n => support (K+t • M) u := by
      funext u
      simp only [ContinuousMap.coe_add,ContinuousMap.coe_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      change support K u+t*support M u = support (K+t • M) u
      rw [support_minkowski hK hKn (hM.smul t)
        (by obtain ⟨x,hx⟩ := hMn; exact ⟨t • x,smul_mem_smul_set hx⟩),
        support_smul_set hM hMn ht]
    rw [hf]
    exact wulff_support (hK.add (hM.smul t)) (hcK.add (hcM.smul t)) (hKn.add (by obtain ⟨x,hx⟩ := hMn; exact ⟨t • x,smul_mem_smul_set hx⟩))
  have h := (wulff_volume_derivative s hs (support M) (support_continuous hM)
    (fun a ha x => support_smul hM hMn ha.le x)).hasDerivWithinAt (s := Ici (0:ℝ))
  have hw : wulff s = K := wulff_support hK hcK hKn
  rw [hw] at h
  exact h.congr (fun t ht => congrArg volume.real (he t ht).symm)
    (congrArg volume.real (he 0 le_rfl).symm)

end PettyProjection
end

end OAI
end
end DevelopmentSource24

/- Source module: Projection.Rigidity.RadialLocalization. SHA256: 5b3b119f4f57aee873328783ad6fd15d419ee9e46f77324457dfc06a8f31ddf7 -/
section DevelopmentSource25






/-!
# Localized first variation of an actual convex body

Polar integration converts a volume integral with a continuous spatial test
function into a one-dimensional primitive along each ray. Differentiating the
radial endpoint gives the localized form of the Wulff variation formula. The
body may be nonsmooth and the added body may have any affine dimension.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Pointwise Gradient

namespace OAI.PettyProjection
open Spherical (Sphere norm_coe surface sigma mean)

/-- The actual radial endpoint of the body in a unit direction. -/
def bodyRadius {n : ℕ} (K : Set (Space n)) (u : Sphere n) : ℝ :=
  (gauge K (u : Space n))⁻¹

/-- A weighted radial primitive; the polar Jacobian is included. -/
def radialPrimitive {n : ℕ} (ψ : Space n → ℝ) (u : Sphere n) (r : ℝ) : ℝ :=
  ∫ a in (0 : ℝ)..r, a ^ (n - 1) * ψ (a • (u : Space n))

theorem continuous_radialPrimitive {n : ℕ} {ψ : Space n → ℝ}
    (hψ : Continuous ψ) : Continuous (fun p : Sphere n × ℝ => radialPrimitive ψ p.1 p.2) := by
  have hc : Continuous (fun p : (Sphere n × ℝ) × ℝ =>
      (p.1.2 * p.2) ^ (n - 1) * ψ ((p.1.2 * p.2) • (p.1.1 : Space n))) := by
    fun_prop
  have hi := continuous_parametric_integral_of_continuous
    (X := Sphere n × ℝ) (Y := ℝ) (E := ℝ) (μ := volume)
    (f := fun (p : Sphere n × ℝ) (a : ℝ) =>
      (p.2 * a) ^ (n - 1) * ψ ((p.2 * a) • (p.1 : Space n))) hc
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))
  have he (p : Sphere n × ℝ) : radialPrimitive ψ p.1 p.2 =
      p.2 * ∫ a in Icc (0 : ℝ) 1,
        (p.2 * a) ^ (n - 1) * ψ ((p.2 * a) • (p.1 : Space n)) := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le zero_le_one]
    simpa only [smul_eq_mul, mul_zero, mul_one, radialPrimitive] using
      (intervalIntegral.smul_integral_comp_mul_left
        (fun a : ℝ => a ^ (n - 1) * ψ (a • (p.1 : Space n)))
        (a := 0) (b := 1) p.2).symm
  simp_rw [he]
  exact continuous_snd.mul hi

theorem radialPrimitive_hasDerivAt {n : ℕ} {ψ : Space n → ℝ}
    (hψ : Continuous ψ) (u : Sphere n) (r : ℝ) :
    HasDerivAt (radialPrimitive ψ u)
      (r ^ (n - 1) * ψ (r • (u : Space n))) r := by
  exact (show Continuous (fun a : ℝ =>
    a ^ (n - 1) * ψ (a • (u : Space n))) by fun_prop).integral_hasStrictDerivAt 0 r
    |>.hasDerivAt

theorem radialPrimitive_lipschitz {n : ℕ} {ψ : Space n → ℝ}
    (hψ : Continuous ψ) {R B : ℝ} (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hb : ∀ x ∈ closedBall (0 : Space n) R, ‖ψ x‖ ≤ B) (u : Sphere n) :
    LipschitzOnWith (NNReal.mk (R ^ (n - 1) * B) (by positivity))
      (radialPrimitive ψ u) (Icc 0 R) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro r hr s hs
  have hc : Continuous (fun a : ℝ => a ^ (n - 1) * ψ (a • (u : Space n))) := by
    fun_prop
  rw [Real.dist_eq, Real.dist_eq, ← Real.norm_eq_abs]
  change ‖(∫ a in (0 : ℝ)..r, a ^ (n - 1) * ψ (a • (u : Space n))) -
      ∫ a in (0 : ℝ)..s, a ^ (n - 1) * ψ (a • (u : Space n))‖ ≤ _
  rw [intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := s) (b := r) (C := R ^ (n - 1) * B) (f := fun a : ℝ =>
      a ^ (n - 1) * ψ (a • (u : Space n))) (fun a ha => by
        have ha0 : 0 ≤ a := (le_min hs.1 hr.1).trans ha.1.le
        have haR : a ≤ R := ha.2.trans (max_le hs.2 hr.2)
        have hx : a • (u : Space n) ∈ closedBall (0 : Space n) R := by
          simpa only [mem_closedBall, dist_zero_right, norm_smul, norm_coe,
            mul_one, Real.norm_of_nonneg ha0] using haR
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ha0 _)]
        exact mul_le_mul (pow_le_pow_left₀ ha0 haR _) (hb _ hx)
          (norm_nonneg _) (pow_nonneg hR _))
  simpa only [NNReal.coe_mk, Real.norm_eq_abs, abs_sub_comm s r] using h

theorem surface_integral_eq_mul_mean {n : ℕ} [NeZero n] (f : Sphere n → ℝ) :
    (∫ u, f u ∂surface n) = (n : ℝ) * kappa n * mean f := by
  rw [mean, sigma, integral_smul_measure, ENNReal.toReal_inv]
  simp only [smul_eq_mul]
  change _ = (n : ℝ) * kappa n * (((surface n).real univ)⁻¹ * _)
  rw [surface_real_univ, ← mul_assoc]
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  rw [mul_inv_cancel₀ (mul_ne_zero hn (kappa_pos n).ne'), one_mul]

/-- Polar integration with an arbitrary continuous spatial test. -/
theorem integral_body_eq_radialPrimitive {n : ℕ} [NeZero n]
    {K : Set (Space n)} (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : K ∈ 𝓝 (0 : Space n)) {ψ : Space n → ℝ} (hψ : Continuous ψ) :
    (∫ x in K, ψ x) = (n : ℝ) * kappa n *
      mean (fun u : Sphere n => radialPrimitive ψ u (bodyRadius K u)) := by
  have hp (u : Sphere n) : 0 < gauge K (u : Space n) := by
    apply (gauge_pos (absorbent_nhds_zero h0)
      ((NormedSpace.isVonNBounded_iff ℝ).2 hK.isBounded)).2
    intro hu
    simpa [hu] using norm_coe u
  have hi : Integrable (K.indicator ψ) volume :=
    (hψ.continuousOn.integrableOn_compact hK).integrable_indicator hK.measurableSet
  rw [← integral_indicator hK.measurableSet,
    TauCeti.integral_eq_integral_toSphere_integral_Ioi _ hi]
  have hinner (u : Sphere n) :
      (∫ r in Ioi (0 : ℝ), r ^ (Module.finrank ℝ (Space n) - 1) •
        K.indicator ψ (r • (u : Space n))) = radialPrimitive ψ u (bodyRadius K u) := by
    have hmem (r : ℝ) (hr : 0 < r) :
        r • (u : Space n) ∈ K ↔ r ≤ bodyRadius K u := by
      have hmem' : r • (u : Space n) ∈ K ↔
          gauge K (r • (u : Space n)) ≤ 1 := by
        simpa only [hK.isClosed.closure_eq] using
          (gauge_le_one_iff_mem_closure (x := r • (u : Space n)) hc h0).symm
      rw [hmem', gauge_smul_of_nonneg (α := ℝ) hr.le, smul_eq_mul]
      change r * gauge K (u : Space n) ≤ 1 ↔ r ≤ (gauge K (u : Space n))⁻¹
      rw [inv_eq_one_div, le_div_iff₀ (hp u)]
    have he : (fun r : ℝ => r ^ (Module.finrank ℝ (Space n) - 1) •
        K.indicator ψ (r • (u : Space n))) =ᶠ[ae (volume.restrict (Ioi 0))]
        (Iic (bodyRadius K u)).indicator
          (fun r : ℝ => r ^ (n - 1) * ψ (r • (u : Space n))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      by_cases hm : r ≤ bodyRadius K u
      · simp only [indicator_of_mem ((hmem r hr).mpr hm),
          indicator_of_mem (show r ∈ Iic (bodyRadius K u) from hm), finrank_euclideanSpace_fin, smul_eq_mul]
      · simp only [indicator_of_notMem (fun hk => hm ((hmem r hr).mp hk)),
          indicator_of_notMem (show r ∉ Iic (bodyRadius K u) from hm), smul_zero]
    rw [integral_congr_ae he, setIntegral_indicator measurableSet_Iic, Ioi_inter_Iic]
    exact (intervalIntegral.integral_of_le (inv_nonneg.mpr (hp u).le)).symm
  simp_rw [hinner]
  exact surface_integral_eq_mul_mean _

theorem wulff_radius_param_bounds {n : ℕ} [NeZero n]
    (s φ : C(Sphere n, ℝ)) (hs : ∀ u, 0 < s u) :
    ∃ T ∈ 𝓝 (0 : ℝ), ∃ R : ℝ, 0 < R ∧ ∃ C : ℝ≥0,
      (∀ t ∈ T, ∀ u : Sphere n, 0 ≤ bodyRadius (wulff ⇑(s + t • φ)) u ∧
        bodyRadius (wulff ⇑(s + t • φ)) u ≤ R) ∧
      ∀ u : Sphere n, LipschitzOnWith C
        (fun t : ℝ => bodyRadius (wulff ⇑(s + t • φ)) u) T := by
  obtain ⟨m, M, hm, hM, he⟩ := positive_constraints_eventually s φ hs
  let T : Set ℝ := {t | ∀ u, m ≤ (s + t • φ) u ∧ (s + t • φ) u ≤ M}
  have hT : T ∈ 𝓝 (0 : ℝ) := he
  have hc : ContDiffOn ℝ 1 (fun a : ℝ => a⁻¹) (Icc M⁻¹ m⁻¹) := by
    intro a ha
    exact (contDiffAt_id.inv ((inv_pos.mpr hM).trans_le ha.1).ne').contDiffWithinAt
  obtain ⟨D, hD⟩ := hc.exists_lipschitzOnWith (by norm_num) (convex_Icc _ _) isCompact_Icc
  let C : ℝ≥0 := NNReal.mk (‖φ‖ / m ^ 2) (by positivity)
  refine ⟨T, hT, M, hM, D * C, ?_, ?_⟩
  · intro t ht u
    have hq := wulff_sphere_gauge_bounds (s + t • φ) hm ht u
    have hqp : 0 < gauge (wulff ⇑(s + t • φ)) (u : Space n) :=
      (inv_pos.mpr hM).trans_le hq.1
    refine ⟨inv_nonneg.mpr hqp.le, ?_⟩
    simpa only [inv_inv, bodyRadius] using inv_anti₀ (inv_pos.mpr hM) hq.1
  · intro u
    apply hD.comp (wulff_gauge_param_lipschitz s φ hm (fun t ht v => (ht v).1) u)
    intro t ht
    exact wulff_sphere_gauge_bounds (s + t • φ) hm ht u

theorem wulff_radius_derivative {n : ℕ} [NeZero n]
    (s : C(Sphere n, ℝ)) (hs : ∀ u, 0 < s u)
    (φ : Space n → ℝ) (hφ : Continuous φ)
    (hh : ∀ a : ℝ, 0 < a → ∀ x, φ (a • x) = a * φ x)
    {u : Sphere n} (hd : DifferentiableAt ℝ (gauge (wulff s)) (u : Space n)) :
    HasDerivAt (fun t : ℝ => bodyRadius
      (wulff ⇑(s + t • (⟨fun v : Sphere n => φ v,
        hφ.comp continuous_subtype_val⟩ : C(Sphere n, ℝ)))) u)
      (bodyRadius (wulff s) u * φ (∇ (gauge (wulff s)) (u : Space n))) 0 := by
  have hp : 0 < gauge (wulff s) (u : Space n) := by
    rw [gauge_wulff_eq_max s hs]
    exact wulffMax_pos s hs (by intro h; simpa [h] using norm_coe u)
  have h := (wulff_derivative s hs φ hφ hh hd).inv
    (by simpa only [zero_smul, add_zero] using hp.ne')
  apply h.congr_deriv
  simp only [bodyRadius, zero_smul, add_zero]
  field_simp [hp.ne']

/-- Localized two-sided Wulff first variation. The test `ψ` is a genuine
continuous function on the ambient space and is evaluated at boundary points. -/
theorem wulff_integral_derivative {n : ℕ} [NeZero n]
    (s : C(Sphere n, ℝ)) (hs : ∀ u, 0 < s u)
    (φ : Space n → ℝ) (hφ : Continuous φ)
    (hh : ∀ a : ℝ, 0 < a → ∀ x, φ (a • x) = a * φ x)
    (ψ : Space n → ℝ) (hψ : Continuous ψ) :
    HasDerivAt (fun t : ℝ => ∫ x in
      wulff ⇑(s + t • (⟨fun u : Sphere n => φ u,
        hφ.comp continuous_subtype_val⟩ : C(Sphere n, ℝ))), ψ x)
      ((n : ℝ) * kappa n * mean (fun u : Sphere n =>
        bodyRadius (wulff s) u ^ n *
          ψ (bodyRadius (wulff s) u • (u : Space n)) *
          φ (∇ (gauge (wulff s)) (u : Space n)))) 0 := by
  let φs : C(Sphere n, ℝ) := ⟨fun u => φ u, hφ.comp continuous_subtype_val⟩
  let ρ : ℝ → Sphere n → ℝ := fun t u => bodyRadius (wulff ⇑(s + t • φs)) u
  let F : ℝ → Sphere n → ℝ := fun t u => radialPrimitive ψ u (ρ t u)
  let F' : Sphere n → ℝ := fun u => bodyRadius (wulff s) u ^ n *
    ψ (bodyRadius (wulff s) u • (u : Space n)) *
    φ (∇ (gauge (wulff s)) (u : Space n))
  have hρc (t : ℝ) (ht : ∀ u, 0 < (s + t • φs) u) : Continuous (ρ t) := by
    apply ((continuous_gauge (wulff_convex _) (wulff_nhds (s + t • φs) ht)).comp
      continuous_subtype_val).inv₀
    intro u
    change gauge (wulff ⇑(s + t • φs)) (u : Space n) ≠ 0
    rw [gauge_wulff_eq_max (s + t • φs) ht]
    exact (wulffMax_pos (s + t • φs) ht (by intro h; simpa [h] using norm_coe u)).ne'
  have hFc (t : ℝ) (ht : ∀ u, 0 < (s + t • φs) u) : Continuous (F t) :=
    (continuous_radialPrimitive hψ).comp (continuous_id.prodMk (hρc t ht))
  have hF0 : Continuous (F 0) := hFc 0 (by simpa using hs)
  obtain ⟨T, hT, R, hR, C, hρbound, hρlip⟩ := wulff_radius_param_bounds s φs hs
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : Space n) R).exists_bound_of_continuousOn
    hψ.continuousOn
  have hB0 : 0 ≤ B := (norm_nonneg (ψ 0)).trans (hB 0 (by simp [hR.le]))
  let L : ℝ≥0 := NNReal.mk (R ^ (n - 1) * B) (by positivity)
  have hFl (u : Sphere n) : LipschitzOnWith (L * C) (fun t => F t u) T :=
    (radialPrimitive_lipschitz hψ hR.le hB0 hB u).comp (hρlip u)
      (fun t ht => hρbound t ht u)
  have hFm : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (F t) (sigma n) :=
    (positive_constraints_nhds s φs hs).mono (fun t ht => (hFc t ht).aestronglyMeasurable)
  have hF'm : AEStronglyMeasurable F' (sigma n) := by
    have hrad : Continuous (bodyRadius (wulff s)) := by simpa only [ρ, zero_smul, add_zero] using hρc 0 (by simpa using hs)
    apply Measurable.aestronglyMeasurable
    exact ((hrad.measurable.pow_const n).mul
      (hψ.measurable.comp (hrad.measurable.smul measurable_subtype_coe))).mul
        (hφ.measurable.comp ((measurable_gradient _).comp measurable_subtype_coe))
  have hd : ∀ᵐ u ∂sigma n, HasDerivAt (fun t => F t u) (F' u) 0 := by
    filter_upwards [gauge_ae_differentiable_sphere (wulff_convex s) (wulff_nhds s hs)] with u hu
    have h := (radialPrimitive_hasDerivAt hψ u (ρ 0 u)).comp 0
      (wulff_radius_derivative s hs φ hφ hh hu)
    simp only [ρ, zero_smul, add_zero] at h
    apply h.congr_deriv
    have hn : n - 1 + 1 = n := Nat.sub_add_cancel (NeZero.one_le : 1 ≤ n)
    have hp : bodyRadius (wulff s) u ^ (n - 1) * bodyRadius (wulff s) u =
        bodyRadius (wulff s) u ^ n := by rw [← pow_succ, hn]
    dsimp only [F']
    calc
      _ = (bodyRadius (wulff s) u ^ (n - 1) * bodyRadius (wulff s) u) *
          ψ (bodyRadius (wulff s) u • (u : Space n)) *
          φ (∇ (gauge (wulff s)) (u : Space n)) := by ring
      _ = _ := by rw [hp]
  have hI := (hasDerivAt_integral_of_dominated_loc_of_lip hT hFm
    (hF0.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) hF'm
    (Eventually.of_forall (fun u => by simpa only [Real.nnabs_coe] using hFl u))
    (integrable_const ((L * C : ℝ≥0) : ℝ)) hd).2
  have he : (fun t : ℝ => ∫ x in wulff ⇑(s + t • φs), ψ x) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => (n : ℝ) * kappa n * ∫ u, F t u ∂sigma n) := by
    filter_upwards [positive_constraints_nhds s φs hs] with t ht
    exact integral_body_eq_radialPrimitive (wulff_compact _ ht) (wulff_convex _)
      (wulff_nhds _ ht) hψ
  exact (hI.const_mul ((n : ℝ) * kappa n)).congr_of_eventuallyEq he

/-- The localized first variation under actual Minkowski addition. -/
theorem minkowski_integral_derivative {n : ℕ} [NeZero n]
    {K A : Set (Space n)} (hK : IsCompact K) (hcK : Convex ℝ K)
    (h0 : K ∈ 𝓝 (0 : Space n)) (hA : IsCompact A) (hcA : Convex ℝ A)
    (hAn : A.Nonempty) (ψ : Space n → ℝ) (hψ : Continuous ψ) :
    HasDerivWithinAt (fun t : ℝ => ∫ x in K + t • A, ψ x)
      ((n : ℝ) * kappa n * mean (fun u : Sphere n => bodyRadius K u ^ n *
        ψ (bodyRadius K u • (u : Space n)) *
        support A (∇ (gauge K) (u : Space n)))) (Ici 0) 0 := by
  have hKn : K.Nonempty := ⟨0, mem_of_mem_nhds h0⟩
  let s : C(Sphere n, ℝ) := ⟨fun u => support K u,
    (support_continuous hK).comp continuous_subtype_val⟩
  have hs : ∀ u, 0 < s u := support_pos_of_nhds hK h0
  let φ : C(Sphere n, ℝ) := ⟨fun u => support A u,
    (support_continuous hA).comp continuous_subtype_val⟩
  have he (t : ℝ) (ht : 0 ≤ t) : wulff ⇑(s + t • φ) = K + t • A := by
    have hf : ⇑(s + t • φ) = fun u : Sphere n => support (K + t • A) u := by
      funext u
      change support K u + t * support A u = support (K + t • A) u
      rw [support_minkowski hK hKn (hA.smul t) (hAn.smul_set (a := t)),
        support_smul_set hA hAn ht]
    rw [hf]
    exact wulff_support (hK.add (hA.smul t)) (hcK.add (hcA.smul t))
      (hKn.add (hAn.smul_set (a := t)))
  have h := (wulff_integral_derivative s hs (support A) (support_continuous hA)
    (fun a ha x => support_smul hA hAn ha.le x) ψ hψ).hasDerivWithinAt (s := Ici (0 : ℝ))
  have hw : wulff s = K := wulff_support hK hcK hKn
  rw [hw] at h
  exact h.congr (fun t ht => congrArg (fun B => ∫ x in B, ψ x) (he t ht).symm)
    (congrArg (fun B => ∫ x in B, ψ x) (he 0 le_rfl).symm)

end OAI.PettyProjection
end
end
end DevelopmentSource25

/- Source module: Projection.Rigidity.RidgeUniqueness. SHA256: b295000acf423e9307298c02bc66d88c917eaf4350a3baf6ad3166f557c04b8d -/
section DevelopmentSource26









/-!
# Uniqueness from one-dimensional smooth tests

Sine and cosine tests suffice to determine a finite measure. Consequently, a
real integrable density on a compact parameter space is determined by these
tests after a continuous injective parametrization. This is the precise
measure-theoretic bridge from quantile variations to radial boundary data.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory Filter
open scoped RealInnerProductSpace

namespace RankThreeProjection.Rigidity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]

/-- Smooth one-dimensional ridge tests determine finite measures. -/
theorem measure_eq_of_cos_sin_integrals (μ ν : Measure E)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hcos : ∀ ξ : E, (∫ x, Real.cos ⟪x, ξ⟫ ∂μ) = ∫ x, Real.cos ⟪x, ξ⟫ ∂ν)
    (hsin : ∀ ξ : E, (∫ x, Real.sin ⟪x, ξ⟫ ∂μ) = ∫ x, Real.sin ⟪x, ξ⟫ ∂ν) :
    μ = ν := by
  apply Measure.ext_of_charFun
  funext ξ
  have hi (η : Measure E) [IsFiniteMeasure η] :
      Integrable (fun x : E => Complex.exp ((⟪x, ξ⟫ : ℂ) * Complex.I)) η := by
    apply (integrable_const (1 : ℝ)).mono (by fun_prop)
    filter_upwards with x
    simp only [Complex.norm_exp_ofReal_mul_I, norm_one, le_refl]
  have hre (η : Measure E) [IsFiniteMeasure η] :
      (∫ x : E, Complex.exp ((⟪x, ξ⟫ : ℂ) * Complex.I) ∂η).re =
        ∫ x : E, Real.cos ⟪x, ξ⟫ ∂η := by
    simpa only [Complex.reCLM_apply, Function.comp_def, Complex.exp_ofReal_mul_I_re] using
      (Complex.reCLM.integral_comp_comm (hi η)).symm
  have him (η : Measure E) [IsFiniteMeasure η] :
      (∫ x : E, Complex.exp ((⟪x, ξ⟫ : ℂ) * Complex.I) ∂η).im =
        ∫ x : E, Real.sin ⟪x, ξ⟫ ∂η := by
    simpa only [Complex.imCLM_apply, Function.comp_def, Complex.exp_ofReal_mul_I_im] using
      (Complex.imCLM.integral_comp_comm (hi η)).symm
  apply Complex.ext
  · simpa only [charFun_apply, hre μ, hre ν] using hcos ξ
  · simpa only [charFun_apply, him μ, him ν] using hsin ξ

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- A positive integrable density is recovered from its sine/cosine moments
under any measurable embedding. No differentiability of the embedding is
required. -/
theorem ae_eq_of_weighted_ridge_integrals {r : X → E} (hr : MeasurableEmbedding r)
    {f g : X → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hcos : ∀ ξ : E, (∫ x, f x * Real.cos ⟪r x, ξ⟫ ∂μ) =
      ∫ x, g x * Real.cos ⟪r x, ξ⟫ ∂μ)
    (hsin : ∀ ξ : E, (∫ x, f x * Real.sin ⟪r x, ξ⟫ ∂μ) =
      ∫ x, g x * Real.sin ⟪r x, ξ⟫ ∂μ) : f =ᵐ[μ] g := by
  let μf := μ.withDensity (fun x => ENNReal.ofReal (f x))
  let μg := μ.withDensity (fun x => ENNReal.ofReal (g x))
  have hfm : AEMeasurable (fun x => ENNReal.ofReal (f x)) μ :=
    hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hgm : AEMeasurable (fun x => ENNReal.ofReal (g x)) μ :=
    hg.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hfi : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≠ ⊤ :=
    (lintegral_ofReal_ne_top_iff_integrable hf.aestronglyMeasurable
      (Eventually.of_forall hf0)).mpr hf
  letI : IsFiniteMeasure μf := isFiniteMeasure_withDensity hfi
  letI : IsFiniteMeasure μg := isFiniteMeasure_withDensity
    ((lintegral_ofReal_ne_top_iff_integrable hg.aestronglyMeasurable
      (Eventually.of_forall hg0)).mpr hg)
  have hfint (φ : E → ℝ) (hφ : Measurable φ) :
      (∫ y, φ y ∂μf.map r) = ∫ x, f x * φ (r x) ∂μ := by
    rw [integral_map hr.measurable.aemeasurable hφ.aestronglyMeasurable,
      integral_withDensity_eq_integral_toReal_smul₀ hfm
        (Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (hf0 _), smul_eq_mul]
  have hgint (φ : E → ℝ) (hφ : Measurable φ) :
      (∫ y, φ y ∂μg.map r) = ∫ x, g x * φ (r x) ∂μ := by
    rw [integral_map hr.measurable.aemeasurable hφ.aestronglyMeasurable,
      integral_withDensity_eq_integral_toReal_smul₀ hgm
        (Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (hg0 _), smul_eq_mul]
  have he : μf.map r = μg.map r := by
    apply measure_eq_of_cos_sin_integrals
    · intro ξ
      rw [hfint _ (by fun_prop), hgint _ (by fun_prop)]
      exact hcos ξ
    · intro ξ
      rw [hfint _ (by fun_prop), hgint _ (by fun_prop)]
      exact hsin ξ
  have he' : μf = μg := hr.map_injective he
  have hae := (withDensity_eq_iff hfm hgm hfi).mp he'
  filter_upwards [hae] with x hx
  simpa only [ENNReal.toReal_ofReal (hf0 x), ENNReal.toReal_ofReal (hg0 x)] using
    congrArg ENNReal.toReal hx

/-- The signed-density form, used when the two comparison bodies differ by
a translation. It only requires sine and cosine moments, not every spatial
continuous test. -/
theorem ae_zero_of_weighted_ridge_integrals {r : X → E} (hr : MeasurableEmbedding r)
    {f : X → ℝ} (hf : Integrable f μ)
    (hcos : ∀ ξ : E, (∫ x, f x * Real.cos ⟪r x, ξ⟫ ∂μ) = 0)
    (hsin : ∀ ξ : E, (∫ x, f x * Real.sin ⟪r x, ξ⟫ ∂μ) = 0) :
    f =ᵐ[μ] 0 := by
  have hprod (g : X → ℝ) (hg : Integrable g μ) (φ : X → ℝ)
      (hφm : Measurable φ) (hφb : ∀ x, ‖φ x‖ ≤ 1) :
      Integrable (fun x => g x * φ x) μ := by
    apply hg.norm.mono (hg.aestronglyMeasurable.mul hφm.aestronglyMeasurable)
    filter_upwards with x
    rw [Pi.mul_apply, norm_mul, norm_norm]
    exact mul_le_of_le_one_right (norm_nonneg _) (hφb x)
  have hm (φ : X → ℝ) (hφm : Measurable φ) (hφb : ∀ x, ‖φ x‖ ≤ 1)
      (hzero : (∫ x, f x * φ x ∂μ) = 0) :
      (∫ x, max (f x) 0 * φ x ∂μ) = ∫ x, max (-f x) 0 * φ x ∂μ := by
    apply sub_eq_zero.mp
    rw [← integral_sub (hprod _ hf.pos_part _ hφm hφb)
      (hprod _ hf.neg_part _ hφm hφb)]
    convert hzero using 1
    congr 1
    funext x
    rw [← sub_mul, max_zero_sub_max_neg_zero_eq_self]
  have he := ae_eq_of_weighted_ridge_integrals hr hf.pos_part hf.neg_part
    (fun x => le_max_right (f x) 0) (fun x => le_max_right (-f x) 0)
    (fun ξ => hm _ (by fun_prop)
      (fun x => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one ⟪r x, ξ⟫)
      (hcos ξ))
    (fun ξ => hm _ (by fun_prop)
      (fun x => by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one ⟪r x, ξ⟫)
      (hsin ξ))
  filter_upwards [he] with x hx
  change f x = 0
  have hp := max_zero_sub_max_neg_zero_eq_self (f x)
  rw [hx, sub_self] at hp
  exact hp.symm

/-- A convenient topological version for compact radial parametrizations. -/
theorem ae_zero_of_continuous_injective_ridge_integrals
    [TopologicalSpace X] [CompactSpace X] [BorelSpace X]
    {r : X → E} (hrc : Continuous r) (hri : Function.Injective r)
    {f : X → ℝ} (hf : Integrable f μ)
    (hcos : ∀ ξ : E, (∫ x, f x * Real.cos ⟪r x, ξ⟫ ∂μ) = 0)
    (hsin : ∀ ξ : E, (∫ x, f x * Real.sin ⟪r x, ξ⟫ ∂μ) = 0) :
    f =ᵐ[μ] 0 :=
  ae_zero_of_weighted_ridge_integrals (hrc.isClosedEmbedding hri).measurableEmbedding
    hf hcos hsin

end RankThreeProjection.Rigidity
end
end
end DevelopmentSource26

/- Source module: Projection.Rigidity.RadialBoundary. SHA256: 22a3b307e65f89bb615397734bd10b13887db84e369dcf57e47ac127827a9dea -/
section DevelopmentSource27






/-!
# Recovering boundary variations from projected variations

The radial boundary map is a continuous injection. Fourier uniqueness therefore
turns equality of the actual sine/cosine first variations into equality of the
support variations at almost every differentiability point of the gauge.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Pointwise Gradient

namespace OAI.PettyProjection
open Spherical (Sphere norm_coe sigma mean)

variable {n : ℕ} [NeZero n]

theorem bodyRadius_pos {K : Set (Space n)} (hK : IsCompact K)
    (h0 : K ∈ 𝓝 (0 : Space n)) (u : Sphere n) : 0 < bodyRadius K u := by
  apply inv_pos.mpr
  apply (gauge_pos (absorbent_nhds_zero h0)
    ((NormedSpace.isVonNBounded_iff ℝ).2 hK.isBounded)).2
  intro hu
  simpa [hu] using norm_coe u

theorem continuous_bodyRadius {K : Set (Space n)} (hK : IsCompact K)
    (hcK : Convex ℝ K) (h0 : K ∈ 𝓝 (0 : Space n)) : Continuous (bodyRadius K) := by
  apply ((continuous_gauge hcK h0).comp continuous_subtype_val).inv₀
  intro u
  exact (inv_pos.mp (bodyRadius_pos hK h0 u)).ne'

/-- The point where the ray through `u` meets the boundary of the actual body. -/
def radialBoundary (K : Set (Space n)) (u : Sphere n) : Space n :=
  bodyRadius K u • (u : Space n)

theorem continuous_radialBoundary {K : Set (Space n)} (hK : IsCompact K)
    (hcK : Convex ℝ K) (h0 : K ∈ 𝓝 (0 : Space n)) : Continuous (radialBoundary K) :=
  (continuous_bodyRadius hK hcK h0).smul continuous_subtype_val

theorem radialBoundary_injective {K : Set (Space n)} (hK : IsCompact K)
    (h0 : K ∈ 𝓝 (0 : Space n)) : Function.Injective (radialBoundary K) := by
  intro u v huv
  have hn : bodyRadius K u = bodyRadius K v := by
    simpa only [radialBoundary, norm_smul, norm_coe, mul_one,
      Real.norm_of_nonneg (bodyRadius_pos hK h0 u).le,
      Real.norm_of_nonneg (bodyRadius_pos hK h0 v).le] using congrArg norm huv
  apply Subtype.ext
  apply smul_right_injective (Space n) (bodyRadius_pos hK h0 u).ne'
  change bodyRadius K u • (u : Space n) = bodyRadius K u • (v : Space n)
  rw [hn]
  simpa only [radialBoundary, hn] using huv

/-- The density in the localized first-variation formula, omitting its
universal positive factor `n * κ_n`. -/
def radialDensity (K : Set (Space n)) (φ : Space n → ℝ) (u : Sphere n) : ℝ :=
  bodyRadius K u ^ n * φ (∇ (gauge K) (u : Space n))

theorem integrable_radialDensity {K : Set (Space n)} (hK : IsCompact K)
    (hcK : Convex ℝ K) (h0 : K ∈ 𝓝 (0 : Space n))
    {φ : Space n → ℝ} (hφ : Continuous φ) :
    Integrable (radialDensity K φ) (sigma n) := by
  obtain ⟨C, hC⟩ := hcK.lipschitz_gauge h0
  have hg (u : Sphere n) : ‖∇ (gauge K) (u : Space n)‖ ≤ (C : ℝ) := by
    simpa only [gradient, LinearIsometryEquiv.norm_map] using
      (norm_fderiv_le_of_lipschitz ℝ (x₀ := (u : Space n)) hC)
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : Space n) (C : ℝ)).exists_bound_of_continuousOn
    hφ.continuousOn
  have hρi : Integrable (fun u : Sphere n => bodyRadius K u ^ n) (sigma n) :=
    ((continuous_bodyRadius hK hcK h0).pow n).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  apply hρi.mul_bdd (c := B)
    ((hφ.measurable.comp ((measurable_gradient _).comp measurable_subtype_coe)).aestronglyMeasurable)
  filter_upwards with u
  apply hB
  simpa only [mem_closedBall, dist_zero_right, Function.comp_apply] using hg u

theorem minkowski_integral_derivative_radial {K A : Set (Space n)}
    (hK : IsCompact K) (hcK : Convex ℝ K) (h0 : K ∈ 𝓝 (0 : Space n))
    (hA : IsCompact A) (hcA : Convex ℝ A) (hAn : A.Nonempty)
    (ψ : Space n → ℝ) (hψ : Continuous ψ) :
    HasDerivWithinAt (fun t : ℝ => ∫ x in K + t • A, ψ x)
      ((n : ℝ) * kappa n * ∫ u, radialDensity K (support A) u *
        ψ (radialBoundary K u) ∂sigma n) (Ici 0) 0 := by
  apply (minkowski_integral_derivative hK hcK h0 hA hcA hAn ψ hψ).congr_deriv
  congr 1
  apply integral_congr_ae
  filter_upwards with u
  dsimp only [radialDensity, radialBoundary, mean]
  ring

/-- Equality of actual projected first variations forces equality of the
support functions at almost every radial normal. The hypotheses are the
one-dimensional Fourier tests supplied by the quantitative BM argument. -/
theorem support_gradient_ae_eq_of_ridge_variations {K A B : Set (Space n)}
    (hK : IsCompact K) (hcK : Convex ℝ K) (h0 : K ∈ 𝓝 (0 : Space n))
    (hA : IsCompact A) (hcA : Convex ℝ A) (hAn : A.Nonempty)
    (hB : IsCompact B) (hcB : Convex ℝ B) (hBn : B.Nonempty)
    (hcos : ∀ ξ : Space n, HasDerivWithinAt
      (fun t : ℝ => (∫ x in K + t • A, Real.cos ⟪x, ξ⟫) -
        ∫ x in K + t • B, Real.cos ⟪x, ξ⟫) 0 (Ici 0) 0)
    (hsin : ∀ ξ : Space n, HasDerivWithinAt
      (fun t : ℝ => (∫ x in K + t • A, Real.sin ⟪x, ξ⟫) -
        ∫ x in K + t • B, Real.sin ⟪x, ξ⟫) 0 (Ici 0) 0) :
    ∀ᵐ (u : Sphere n) ∂sigma n,
      support A (∇ (gauge K) (u : Space n)) =
        support B (∇ (gauge K) (u : Space n)) := by
  let a := radialDensity K (support A)
  let b := radialDensity K (support B)
  have hai : Integrable a (sigma n) := integrable_radialDensity hK hcK h0 (support_continuous hA)
  have hbi : Integrable b (sigma n) := integrable_radialDensity hK hcK h0 (support_continuous hB)
  have moment_zero (ψ : Space n → ℝ) (hψ : Continuous ψ) (hψb : ∀ x, ‖ψ x‖ ≤ 1)
      (hv : HasDerivWithinAt
        (fun t : ℝ => (∫ x in K + t • A, ψ x) - ∫ x in K + t • B, ψ x)
        0 (Ici 0) 0) :
      (∫ u, (a u - b u) * ψ (radialBoundary K u) ∂sigma n) = 0 := by
    have ha := minkowski_integral_derivative_radial hK hcK h0 hA hcA hAn ψ hψ
    have hb := minkowski_integral_derivative_radial hK hcK h0 hB hcB hBn ψ hψ
    have hz := (uniqueDiffWithinAt_Ici (0 : ℝ)).eq_deriv (Ici 0) (ha.fun_sub hb) hv
    have hprod (f : Sphere n → ℝ) (hf : Integrable f (sigma n)) :
        Integrable (fun u => f u * ψ (radialBoundary K u)) (sigma n) :=
      hf.mul_bdd ((hψ.comp (continuous_radialBoundary hK hcK h0)).aestronglyMeasurable)
        (Eventually.of_forall (fun u => hψb _))
    have he : (∫ u, (a u - b u) * ψ (radialBoundary K u) ∂sigma n) =
        (∫ u, a u * ψ (radialBoundary K u) ∂sigma n) -
          ∫ u, b u * ψ (radialBoundary K u) ∂sigma n := by
      simp_rw [sub_mul]
      exact integral_sub (hprod a hai) (hprod b hbi)
    rw [he]
    have hn : (n : ℝ) * kappa n ≠ 0 := mul_ne_zero
      (by exact_mod_cast NeZero.ne n) (kappa_pos n).ne'
    apply (mul_eq_zero.mp (show ((n : ℝ) * kappa n) *
      ((∫ u, a u * ψ (radialBoundary K u) ∂sigma n) -
        ∫ u, b u * ψ (radialBoundary K u) ∂sigma n) = 0 by
          rw [mul_sub]; exact hz)).resolve_left hn
  have hdiffi : Integrable (fun u => a u - b u) (sigma n) := by
    simpa only [Pi.sub_def] using hai.sub hbi
  have he := RankThreeProjection.Rigidity.ae_zero_of_continuous_injective_ridge_integrals
    (continuous_radialBoundary hK hcK h0) (radialBoundary_injective hK h0)
    hdiffi
    (fun ξ => moment_zero _ (by fun_prop)
      (fun x => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one ⟪x, ξ⟫) (hcos ξ))
    (fun ξ => moment_zero _ (by fun_prop)
      (fun x => by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one ⟪x, ξ⟫) (hsin ξ))
  filter_upwards [he] with u hu
  have hp : bodyRadius K u ^ n ≠ 0 := (pow_pos (bodyRadius_pos hK h0 u) n).ne'
  dsimp only [a, b, radialDensity, Pi.sub_apply, Pi.zero_apply] at hu
  exact mul_left_cancel₀ hp (sub_eq_zero.mp hu)

end OAI.PettyProjection
end
end
end DevelopmentSource27

/- Source module: Projection.Rigidity.CentroidVariation. SHA256: 7f083e232bfcd9292fe0ce394602765735a3bb18cd4f346c0e18be0768fd4441 -/
section DevelopmentSource28







/-!
# A single vector for all directional centroid variations

The scalar localized first variation determines a vector first moment. The
ordinary quotient rule then differentiates the normalized uniform mean. This
ensures that the constants obtained independently from one-dimensional
quantiles are the components of one translation vector.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory Metric Filter Topology Function ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace Pointwise Gradient

namespace OAI.PettyProjection
open Spherical (Sphere sigma)

variable {n : ℕ} [NeZero n]

def radialMassVariation (K : Set (Space n)) (φ : Space n → ℝ) : ℝ :=
  (n : ℝ) * kappa n * ∫ u, radialDensity K φ u ∂sigma n

def radialFirstMomentVariation (K : Set (Space n)) (φ : Space n → ℝ) : Space n :=
  ((n : ℝ) * kappa n) • ∫ u, radialDensity K φ u • radialBoundary K u ∂sigma n

theorem integrable_radialFirstMoment {K : Set (Space n)} (hK : IsCompact K)
    (hcK : Convex ℝ K) (h0 : K ∈ 𝓝 (0 : Space n))
    {φ : Space n → ℝ} (hφ : Continuous φ) :
    Integrable (fun u => radialDensity K φ u • radialBoundary K u) (sigma n) := by
  have hr := continuous_radialBoundary hK hcK h0
  have hc : IsCompact (univ : Set (Sphere n)) := isCompact_univ
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn hr.continuousOn
  simpa only [Pi.smul_def'] using
    (integrable_radialDensity hK hcK h0 hφ).smul_bdd C hr.aestronglyMeasurable
      (Eventually.of_forall (fun u => hC u (mem_univ u)))

theorem inner_radialFirstMomentVariation {K : Set (Space n)} (hK : IsCompact K)
    (hcK : Convex ℝ K) (h0 : K ∈ 𝓝 (0 : Space n))
    {φ : Space n → ℝ} (hφ : Continuous φ) (e : Space n) :
    ⟪e, radialFirstMomentVariation K φ⟫ =
      (n : ℝ) * kappa n * ∫ u, radialDensity K φ u * ⟪e, radialBoundary K u⟫ ∂sigma n := by
  have hi := (innerSL ℝ e).integral_comp_comm
    (integrable_radialFirstMoment hK hcK h0 hφ)
  simp only [innerSL_apply_apply] at hi
  rw [radialFirstMomentVariation, real_inner_smul_right]
  congr 1
  change ⟪e, ∫ u, radialDensity K φ u • radialBoundary K u ∂sigma n⟫ = _
  rw [← hi]
  apply integral_congr_ae
  filter_upwards with u
  exact real_inner_smul_right _ _ _

def bodyFirstMoment (K : ConvexBody (Space n)) : Space n :=
  ∫ x in (K : Set (Space n)), x

/-- The derivative vector of the normalized centroid along a Minkowski ray. -/
def centroidVariation (K A : ConvexBody (Space n)) : Space n :=
  (volume.real (K : Set (Space n)) ^ 2)⁻¹ •
    (volume.real (K : Set (Space n)) •
        radialFirstMomentVariation (K : Set (Space n)) (support (A : Set (Space n))) -
      radialMassVariation (K : Set (Space n)) (support (A : Set (Space n))) • bodyFirstMoment K)

theorem conditional_inner_eq_integral_div (K : ConvexBody (Space n)) (e : Space n) :
    (∫ x, ⟪e, x⟫ ∂volume[|(K : Set (Space n))]) =
      (∫ x in (K : Set (Space n)), ⟪e, x⟫) / volume.real (K : Set (Space n)) := by
  rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv]
  simp only [smul_eq_mul, measureReal_def, div_eq_mul_inv]
  rw [mul_comm]

/-- All directional conditional means differentiate with one common vector.
There is no equal-volume hypothesis in this existence statement. -/
theorem hasDerivWithinAt_conditional_inner (K A : ConvexBody (Space n))
    (h0 : (K : Set (Space n)) ∈ 𝓝 (0 : Space n)) (e : Space n) :
    HasDerivWithinAt (fun t : ℝ => ∫ x, ⟪e, x⟫
      ∂volume[|((K + t • A : ConvexBody (Space n)) : Set (Space n))])
      ⟪e, centroidVariation K A⟫ (Ici 0) 0 := by
  have hm : HasDerivWithinAt
      (fun t : ℝ => ∫ x in ((K + t • A : ConvexBody (Space n)) : Set (Space n)), ⟪e, x⟫)
      ⟪e, radialFirstMomentVariation (K : Set (Space n)) (support (A : Set (Space n)))⟫
      (Ici 0) 0 := by
    rw [inner_radialFirstMomentVariation K.isCompact K.convex h0 (support_continuous A.isCompact)]
    simpa only [ConvexBody.coe_add, ConvexBody.coe_smul] using
      minkowski_integral_derivative_radial K.isCompact K.convex h0 A.isCompact A.convex
        A.nonempty (fun x => ⟪e, x⟫) (by fun_prop)
  have hv : HasDerivWithinAt
      (fun t : ℝ => volume.real ((K + t • A : ConvexBody (Space n)) : Set (Space n)))
      (radialMassVariation (K : Set (Space n)) (support (A : Set (Space n)))) (Ici 0) 0 := by
    simpa only [ConvexBody.coe_add, ConvexBody.coe_smul, radialMassVariation,
      radialDensity, bodyRadius, Spherical.mean] using
      minkowski_volume_derivative K.isCompact K.convex h0 A.isCompact A.convex A.nonempty
  have hV : 0 < volume.real (K : Set (Space n)) :=
    ENNReal.toReal_pos (Measure.measure_pos_of_mem_nhds volume h0).ne' K.isCompact.measure_lt_top.ne
  have hq := hm.fun_div hv (by simpa only [VolumePolynomials.body_zero_smul, add_zero] using hV.ne')
  simp only [VolumePolynomials.body_zero_smul, add_zero] at hq
  have he : (fun t : ℝ => ∫ x, ⟪e, x⟫
      ∂volume[|((K + t • A : ConvexBody (Space n)) : Set (Space n))]) =
      (fun t : ℝ => (∫ x in ((K + t • A : ConvexBody (Space n)) : Set (Space n)), ⟪e, x⟫) /
        volume.real ((K + t • A : ConvexBody (Space n)) : Set (Space n))) := by
    funext t
    exact conditional_inner_eq_integral_div (K + t • A) e
  rw [he]
  apply hq.congr_deriv
  have hid : IntegrableOn (fun x : Space n => x) (K : Set (Space n)) volume :=
    continuous_id.continuousOn.integrableOn_compact K.isCompact
  have hmi := (innerSL ℝ e).integral_comp_comm hid
  simp only [innerSL_apply_apply] at hmi
  change _ = ⟪e, (volume.real (K : Set (Space n)) ^ 2)⁻¹ •
    (volume.real (K : Set (Space n)) •
        radialFirstMomentVariation (K : Set (Space n)) (support (A : Set (Space n))) -
      radialMassVariation (K : Set (Space n)) (support (A : Set (Space n))) •
        ∫ x in (K : Set (Space n)), x)⟫
  rw [real_inner_smul_right, inner_sub_right, real_inner_smul_right, real_inner_smul_right,
    ← hmi]
  simp only [div_eq_mul_inv]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- The translation vector that identifies the directional quantile limits
is the derivative of the actual centroid difference. -/
theorem exists_centroid_difference_derivative (K A C : ConvexBody (Space n))
    (h0 : (K : Set (Space n)) ∈ 𝓝 (0 : Space n)) :
    ∃ v : Space n, ∀ e : Space n, HasDerivWithinAt
      (fun t : ℝ => (∫ x, ⟪e, x⟫
        ∂volume[|((K + t • C : ConvexBody (Space n)) : Set (Space n))]) -
        ∫ x, ⟪e, x⟫ ∂volume[|((K + t • A : ConvexBody (Space n)) : Set (Space n))])
      ⟪e, v⟫ (Ici 0) 0 := by
  refine ⟨centroidVariation K C - centroidVariation K A, fun e => ?_⟩
  simpa only [inner_sub_right] using
    (hasDerivWithinAt_conditional_inner K C h0 e).fun_sub
      (hasDerivWithinAt_conditional_inner K A h0 e)

end OAI.PettyProjection
end
end
end DevelopmentSource28

/- Source module: Projection.Rigidity.LipschitzVariation. SHA256: 73c8b25ea6baf2529e2a885b946dfbec24a2c6a0662b29207eb4b2ec383c15d0 -/
section DevelopmentSource29








/-!
# Lipschitz tests of centered quantiles

The centered quantile difference converges in L¹ after division by the ray
parameter. Every fixed Lipschitz test consequently has zero first variation.
Normalizing a nonzero Fourier frequency reduces it to a unit height direction,
so unit-direction quantile control supplies every characteristic-function test.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory Filter
open scoped Topology NNReal RealInnerProductSpace

namespace RankThreeProjection.QuantileStability

/-- A Lipschitz scalar test preserves integrability on a finite measure
space. The constant value at zero is kept explicitly. -/
theorem integrable_lipschitz_test
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    {f : X → ℝ} (hf : Integrable f μ)
    (ψ : ℝ → ℝ) (L : ℝ≥0) (hψ : LipschitzWith L ψ) :
    Integrable (fun x => ψ (f x)) μ := by
  have hi : Integrable (fun x => (L : ℝ) * ‖f x‖ + ‖ψ 0‖) μ :=
    (hf.norm.const_mul (L : ℝ)).add (integrable_const _)
  apply hi.mono' (hψ.continuous.comp_aestronglyMeasurable hf.aestronglyMeasurable)
  filter_upwards with x
  have hb : ‖ψ (f x) - ψ 0‖ ≤ (L : ℝ) * ‖f x‖ := by
    simpa only [dist_eq_norm, sub_zero] using hψ.dist_le_mul (f x) 0
  calc
    ‖ψ (f x)‖ ≤ ‖ψ (f x) - ψ 0‖ + ‖ψ 0‖ := by
      simpa only [sub_add_cancel] using norm_add_le (ψ (f x) - ψ 0) (ψ 0)
    _ ≤ (L : ℝ) * ‖f x‖ + ‖ψ 0‖ := add_le_add hb le_rfl

theorem integral_lipschitz_difference_quotient_le_mul
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f g : X → ℝ) (ψ : ℝ → ℝ) (L : ℝ≥0) (t : ℝ)
    (hψ : LipschitzWith L ψ)
    (hfi : Integrable (fun x => ψ (f x)) μ)
    (hgi : Integrable (fun x => ψ (g x)) μ)
    (hdi : Integrable (fun x => (g x - f x) / t) μ) :
    |((∫ x, ψ (g x) ∂μ) - ∫ x, ψ (f x) ∂μ) / t| ≤
      (L : ℝ) * ∫ x, |(g x - f x) / t| ∂μ := by
  rw [← integral_sub hgi hfi, ← integral_div, ← integral_const_mul]
  calc
    _ ≤ ∫ x, |(ψ (g x) - ψ (f x)) / t| ∂μ := by
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (fun x => (ψ (g x) - ψ (f x)) / t)
    _ ≤ _ := by
      apply integral_mono ((hgi.sub hfi).div_const t).norm (hdi.norm.const_mul (L : ℝ))
      intro x
      have h := div_le_div_of_nonneg_right (hψ.dist_le_mul (g x) (f x)) (abs_nonneg t)
      simpa only [Pi.sub_apply, Real.dist_eq, Real.norm_eq_abs, abs_div, mul_div_assoc] using h

theorem tendsto_lipschitz_test_difference_quotient_zero
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f g : ℝ → X → ℝ) (ψ : ℝ → ℝ) (L : ℝ≥0) (hψ : LipschitzWith L ψ)
    (hint : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      Integrable (fun x => ψ (f t x)) μ ∧ Integrable (fun x => ψ (g t x)) μ ∧
        Integrable (fun x => (g t x - f t x) / t) μ)
    (hL1 : Tendsto (fun t : ℝ => ∫ x, |(g t x - f t x) / t| ∂μ)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun t : ℝ =>
      ((∫ x, ψ (g t x) ∂μ) - ∫ x, ψ (f t x) ∂μ) / t)
      (𝓝[>] 0) (𝓝 0) := by
  have hbound : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      |((∫ x, ψ (g t x) ∂μ) - ∫ x, ψ (f t x) ∂μ) / t| ≤
        (L : ℝ) * ∫ x, |(g t x - f t x) / t| ∂μ := by
    filter_upwards [hint] with t ht
    exact integral_lipschitz_difference_quotient_le_mul μ (f t) (g t) ψ L t hψ
      ht.1 ht.2.1 ht.2.2
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [Real.norm_eq_abs] using
    squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) hbound
      (by simpa only [mul_zero] using tendsto_const_nhds.mul hL1)

/-- A direct zero first derivative, with no differentiation of the Lipschitz
test itself. The base quantiles only need to agree almost everywhere. -/
theorem hasDerivWithinAt_lipschitz_test_difference_zero
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f g : ℝ → X → ℝ) (ψ : ℝ → ℝ) (L : ℝ≥0) (hψ : LipschitzWith L ψ)
    (hbase : g 0 =ᵐ[μ] f 0)
    (hint : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      Integrable (fun x => ψ (f t x)) μ ∧ Integrable (fun x => ψ (g t x)) μ ∧
        Integrable (fun x => (g t x - f t x) / t) μ)
    (hL1 : Tendsto (fun t : ℝ => ∫ x, |(g t x - f t x) / t| ∂μ)
      (𝓝[>] 0) (𝓝 0)) :
    HasDerivWithinAt (fun t : ℝ =>
      (∫ x, ψ (g t x) ∂μ) - ∫ x, ψ (f t x) ∂μ) 0 (Ici 0) 0 := by
  have hzero : (∫ x, ψ (g 0 x) ∂μ) - ∫ x, ψ (f 0 x) ∂μ = 0 := by
    apply sub_eq_zero.mpr
    exact integral_congr_ae (hbase.fun_comp ψ)
  exact (hasDerivWithinAt_Ici_zero_iff_div hzero).mpr
    (tendsto_lipschitz_test_difference_quotient_zero μ f g ψ L hψ hint hL1)

section Frequency

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem exists_unit_frequency (ξ : E) (hξ : ξ ≠ 0) :
    ∃ e : E, ‖e‖ = 1 ∧ ∀ x : E, ⟪x, ξ⟫ = ‖ξ‖ * ⟪e, x⟫ := by
  have hp : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  refine ⟨‖ξ‖⁻¹ • ξ, ?_, ?_⟩
  · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hp.le), inv_mul_cancel₀ hp.ne']
  · intro x
    rw [real_inner_smul_left, ← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul, real_inner_comm]

variable [MeasurableSpace E]

/-- Unit height directions and arbitrary Lipschitz scalar tests provide all
Fourier frequencies. The zero frequency follows from the actual probability
normalization, and is not discarded. -/
theorem all_frequencies_of_unit_lipschitz_variations
    (μ ν : ℝ → Measure E)
    (hμ : ∀ t, IsProbabilityMeasure (μ t)) (hν : ∀ t, IsProbabilityMeasure (ν t))
    (hunit : ∀ e : E, ‖e‖ = 1 → ∀ (ψ : ℝ → ℝ) (L : ℝ≥0), LipschitzWith L ψ →
      HasDerivWithinAt (fun t : ℝ => (∫ x, ψ ⟪e, x⟫ ∂μ t) - ∫ x, ψ ⟪e, x⟫ ∂ν t)
        0 (Ici 0) 0)
    (ψ : ℝ → ℝ) (L : ℝ≥0) (hψ : LipschitzWith L ψ) (ξ : E) :
    HasDerivWithinAt (fun t : ℝ => (∫ x, ψ ⟪x, ξ⟫ ∂μ t) - ∫ x, ψ ⟪x, ξ⟫ ∂ν t)
      0 (Ici 0) 0 := by
  by_cases hξ : ξ = 0
  · subst ξ
    have he : (fun t : ℝ => (∫ x, ψ ⟪x, (0 : E)⟫ ∂μ t) -
        ∫ x, ψ ⟪x, (0 : E)⟫ ∂ν t) = fun _ => 0 := by
      funext t
      letI := hμ t
      letI := hν t
      simp
    rw [he]
    exact hasDerivWithinAt_const _ _ _
  · obtain ⟨e, he, hinner⟩ := exists_unit_frequency ξ hξ
    have hscaled : LipschitzWith (L * ‖(‖ξ‖ : ℝ)‖₊)
        (fun s : ℝ => ψ (‖ξ‖ * s)) := by
      simpa only [Function.comp_def, smul_eq_mul] using
        hψ.comp (lipschitzWith_smul (β := ℝ) ‖ξ‖)
    simpa only [← hinner] using hunit e he (fun s => ψ (‖ξ‖ * s)) _ hscaled

theorem fourier_variations_of_unit_lipschitz_variations
    (μ ν : ℝ → Measure E)
    (hμ : ∀ t, IsProbabilityMeasure (μ t)) (hν : ∀ t, IsProbabilityMeasure (ν t))
    (hunit : ∀ e : E, ‖e‖ = 1 → ∀ (ψ : ℝ → ℝ) (L : ℝ≥0), LipschitzWith L ψ →
      HasDerivWithinAt (fun t : ℝ => (∫ x, ψ ⟪e, x⟫ ∂μ t) - ∫ x, ψ ⟪e, x⟫ ∂ν t)
        0 (Ici 0) 0) :
    (∀ ξ : E, HasDerivWithinAt
      (fun t : ℝ => (∫ x, Real.cos ⟪x, ξ⟫ ∂μ t) - ∫ x, Real.cos ⟪x, ξ⟫ ∂ν t)
      0 (Ici 0) 0) ∧
    (∀ ξ : E, HasDerivWithinAt
      (fun t : ℝ => (∫ x, Real.sin ⟪x, ξ⟫ ∂μ t) - ∫ x, Real.sin ⟪x, ξ⟫ ∂ν t)
      0 (Ici 0) 0) :=
  ⟨all_frequencies_of_unit_lipschitz_variations μ ν hμ hν hunit
      Real.cos 1 Real.lipschitzWith_cos,
    all_frequencies_of_unit_lipschitz_variations μ ν hμ hν hunit
      Real.sin 1 Real.lipschitzWith_sin⟩

end Frequency
end RankThreeProjection.QuantileStability
end
end
end DevelopmentSource29

/- Source module: Projection.ConvexHullValuation. SHA256: 4d2bef626558b8451d4af77802512354014081a34d98bf34d724a42aeffe0d6b -/
section DevelopmentSource30







@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory Module
open scoped Pointwise BigOperators

namespace RankThreeProjection
open VolumePolynomials

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Membership in the actual convex hull of two compact convex bodies. -/
theorem mem_joinBody_iff (A B : ConvexBody E) (x : E) :
    x ∈ joinBody A B ↔ ∃ t ∈ Icc (0 : ℝ) 1, ∃ a ∈ A, ∃ b ∈ B,
      x = (1 - t) • a + t • b := by
  constructor
  · intro hx
    obtain ⟨a, ha, b, hb, hx⟩ := mem_convexJoin.mp hx
    rw [segment_eq_image] at hx
    obtain ⟨t, ht, he⟩ := hx
    exact ⟨t, ht, a, ha, b, hb, he.symm⟩
  · rintro ⟨t, ht, a, ha, b, hb, rfl⟩
    apply mem_convexJoin.mpr
    refine ⟨a, ha, b, hb, ?_⟩
    rw [segment_eq_image]
    exact ⟨t, ht, rfl⟩

theorem le_joinBody_left (A B : ConvexBody E) : A ≤ joinBody A B :=
  subset_convexJoin_left B.nonempty

theorem le_joinBody_right (A B : ConvexBody E) : B ≤ joinBody A B :=
  subset_convexJoin_right A.nonempty

/-- The Cayley union identity, including an arbitrary common Minkowski
summand. Every body and sum in this identity has its usual set meaning. -/
theorem joinBody_cayley_union (A B R : ConvexBody E) :
    ((joinBody A B + A + R : ConvexBody E) : Set E) ∪
        ((joinBody A B + B + R : ConvexBody E) : Set E) =
      ((joinBody A B + joinBody A B + R : ConvexBody E) : Set E) := by
  let D := joinBody A B
  have hA : A ≤ D := le_joinBody_left A B
  have hB : B ≤ D := le_joinBody_right A B
  apply subset_antisymm
  · rintro x (hx | hx)
    · rcases hx with ⟨y, ⟨d, hd, a, ha, rfl⟩, r, hr, rfl⟩
      exact ⟨d + a, ⟨d, hd, a, hA ha, rfl⟩, r, hr, rfl⟩
    · rcases hx with ⟨y, ⟨d, hd, b, hb, rfl⟩, r, hr, rfl⟩
      exact ⟨d + b, ⟨d, hd, b, hB hb, rfl⟩, r, hr, rfl⟩
  · have hdouble : D + D = (2 : ℝ) • D := by
      simpa only [one_smul, one_add_one_eq_two] using
        (body_add_smul D (a := 1) (b := 1) zero_le_one zero_le_one).symm
    intro x hx
    change x ∈ ((D + D + R : ConvexBody E) : Set E) at hx
    rw [hdouble] at hx
    rcases hx with ⟨y, ⟨d, hd, rfl⟩, r, hr, rfl⟩
    obtain ⟨t, ht, a, ha, b, hb, rfl⟩ := (mem_joinBody_iff A B d).mp hd
    by_cases ht2 : t ≤ 1 / 2
    · left
      have hd' : (1 - 2 * t) • a + (2 * t) • b ∈ D :=
        D.convex (hA ha) (hB hb) (by linarith) (by linarith [ht.1]) (by ring)
      refine ⟨((1 - 2 * t) • a + (2 * t) • b) + a,
        ⟨_, hd', a, ha, rfl⟩, r, hr, ?_⟩
      module
    · right
      have hd' : (2 * (1 - t)) • a + (2 * t - 1) • b ∈ D :=
        D.convex (hA ha) (hB hb) (by linarith [ht.2]) (by linarith) (by ring)
      refine ⟨((2 * (1 - t)) • a + (2 * t - 1) • b) + b,
        ⟨_, hd', b, hb, rfl⟩, r, hr, ?_⟩
      module

/-- The Cayley intersection identity. The common summand may contribute
different points to the two representations; convexity combines them. -/
theorem joinBody_cayley_inter (A B R : ConvexBody E) :
    ((joinBody A B + A + R : ConvexBody E) : Set E) ∩
        ((joinBody A B + B + R : ConvexBody E) : Set E) =
      ((A + B + R : ConvexBody E) : Set E) := by
  let D := joinBody A B
  have hA : A ≤ D := le_joinBody_left A B
  have hB : B ≤ D := le_joinBody_right A B
  apply subset_antisymm
  · intro x hx
    rcases hx.1 with ⟨y₁, ⟨d₁, hd₁, a₀, ha₀, rfl⟩, r₁, hr₁, hx₁⟩
    rcases hx.2 with ⟨y₂, ⟨d₂, hd₂, b₀, hb₀, rfl⟩, r₂, hr₂, hx₂⟩
    obtain ⟨t, ht, a₁, ha₁, b₁, hb₁, hd₁'⟩ := (mem_joinBody_iff A B d₁).mp hd₁
    obtain ⟨s, hs, a₂, ha₂, b₂, hb₂, hd₂'⟩ := (mem_joinBody_iff A B d₂).mp hd₂
    obtain ⟨a, ha, hea⟩ := A.convex.exists_mem_add_smul_eq ha₀ ha₁
      (show (0 : ℝ) ≤ 1 from zero_le_one) (sub_nonneg.mpr ht.2)
    obtain ⟨b, hb, heb⟩ := B.convex.exists_mem_add_smul_eq hb₀ hb₂
      (show (0 : ℝ) ≤ 1 from zero_le_one) hs.1
    have hea' : (2 - t) • a = a₀ + (1 - t) • a₁ := by
      simpa only [one_smul, show (1 : ℝ) + (1 - t) = 2 - t by ring] using hea
    have heb' : (1 + s) • b = b₀ + s • b₂ := by
      simpa only [one_smul] using heb
    have hleft : ((2 - t) • a + t • b₁) + r₁ = x := by
      calc
        _ = (d₁ + a₀) + r₁ := by rw [hea', hd₁']; module
        _ = x := hx₁
    have hright : ((1 - s) • a₂ + (1 + s) • b) + r₂ = x := by
      calc
        _ = (d₂ + b₀) + r₂ := by rw [heb', hd₂']; module
        _ = x := hx₂
    by_cases hden : 1 - t + s = 0
    · have ht1 : t = 1 := by linarith [ht.2, hs.1]
      refine ⟨a + b₁, ⟨a, ha, b₁, hb₁, rfl⟩, r₁, hr₁, ?_⟩
      simpa only [ht1, sub_self, add_zero, one_smul,
        show (2 : ℝ) - 1 = 1 by ring] using hleft
    · have hdenpos : 0 < 1 - t + s :=
        lt_of_le_of_ne (by linarith [ht.2, hs.1]) (Ne.symm hden)
      let w : ℝ := s / (1 - t + s)
      have hw0 : 0 ≤ w := div_nonneg hs.1 hdenpos.le
      have hw1 : w ≤ 1 := (div_le_one hdenpos).mpr (by linarith [ht.2])
      have hw : w * (1 - t + s) = s := div_mul_cancel₀ _ hden
      let a' := (w * (2 - t)) • a + ((1 - w) * (1 - s)) • a₂
      let b' := (w * t) • b₁ + ((1 - w) * (1 + s)) • b
      let r' := w • r₁ + (1 - w) • r₂
      have ha' : a' ∈ A := A.convex ha ha₂
        (mul_nonneg hw0 (by linarith [ht.2]))
        (mul_nonneg (sub_nonneg.mpr hw1) (sub_nonneg.mpr hs.2)) (by nlinarith [hw])
      have hb' : b' ∈ B := B.convex hb₁ hb
        (mul_nonneg hw0 ht.1)
        (mul_nonneg (sub_nonneg.mpr hw1) (by linarith [hs.1])) (by nlinarith [hw])
      have hr' : r' ∈ R := R.convex hr₁ hr₂ hw0 (sub_nonneg.mpr hw1) (by ring)
      refine ⟨a' + b', ⟨a', ha', b', hb', rfl⟩, r', hr', ?_⟩
      calc
        _ = w • (((2 - t) • a + t • b₁) + r₁) +
            (1 - w) • (((1 - s) • a₂ + (1 + s) • b) + r₂) := by
              dsimp [a', b', r']
              module
        _ = w • x + (1 - w) • x := by rw [hleft, hright]
        _ = x := by module
  · rintro x ⟨y, ⟨a, ha, b, hb, rfl⟩, r, hr, rfl⟩
    constructor
    · refine ⟨b + a, ⟨b, hB hb, a, ha, rfl⟩, r, hr, ?_⟩
      rw [add_comm b a]
    · exact ⟨a + b, ⟨a, hA ha, b, hb, rfl⟩, r, hr, rfl⟩

theorem joinBody_smul (A B : ConvexBody E) {s : ℝ} (hs : 0 ≤ s) :
    joinBody (s • A) (s • B) = s • joinBody A B := by
  apply supportContinuous_injective
  ext u
  have hjoin := congrArg (fun f : C(NormalSphere E, ℝ) => f u)
    (supportContinuous_join A B)
  change BodySupport.support (joinBody A B) u.val =
    max (BodySupport.support A u.val) (BodySupport.support B u.val) at hjoin
  rw [supportContinuous_join]
  change max (BodySupport.support (s • A) u.val) (BodySupport.support (s • B) u.val) =
    BodySupport.support (s • joinBody A B) u.val
  rw [Support.smul_body A u.val hs, Support.smul_body B u.val hs,
    Support.smul_body (joinBody A B) u.val hs, hjoin]
  exact (mul_max_of_nonneg _ _ hs).symm

section Volume
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

/-- Ordinary Haar volume inclusion–exclusion on the actual Cayley sets. -/
theorem joinBody_cayley_volume (A B R : ConvexBody E) :
    μ.real ((joinBody A B + joinBody A B + R : ConvexBody E) : Set E) +
        μ.real ((A + B + R : ConvexBody E) : Set E) =
      μ.real ((joinBody A B + A + R : ConvexBody E) : Set E) +
        μ.real ((joinBody A B + B + R : ConvexBody E) : Set E) := by
  have h := measureReal_union_add_inter (μ := μ)
    (s := ((joinBody A B + A + R : ConvexBody E) : Set E))
    (t := ((joinBody A B + B + R : ConvexBody E) : Set E))
    (joinBody A B + B + R).isCompact.measurableSet
    (joinBody A B + A + R).isCompact.measure_lt_top.ne
    (joinBody A B + B + R).isCompact.measure_lt_top.ne
  rw [joinBody_cayley_union, joinBody_cayley_inter] at h
  exact h

/-- The quadratic mixed-volume valuation identity for a convex hull. It is
proved by ordinary volume inclusion–exclusion and polynomial coefficient
uniqueness, without postulating a valuation property of mixed volume. -/
theorem mixedVolume_joinBody_identity {d : ℕ} (K : Fin d → ConvexBody E)
    (A B : ConvexBody E) :
    mixedVolume μ (Fin.cons (joinBody A B) (Fin.cons (joinBody A B) K)) +
        mixedVolume μ (Fin.cons A (Fin.cons B K)) =
      mixedVolume μ (Fin.cons (joinBody A B) (Fin.cons A K)) +
        mixedVolume μ (Fin.cons (joinBody A B) (Fin.cons B K)) := by
  let D := joinBody A B
  let p (L : ConvexBody E) := volumePolynomial μ (Fin.cons L (Fin.cons L K))
  have hpoly : p (D + D) + p (A + B) = p (D + A) + p (D + B) := by
    apply MvPolynomial.funext_set (fun _ => Ici (0 : ℝ)) (fun _ => Ici_infinite 0)
    intro t ht
    have ht' : ∀ i, 0 ≤ t i := fun i => ht i (mem_univ i)
    let s : ℝ := t 0 + t 1
    have hs : 0 ≤ s := add_nonneg (ht' 0) (ht' 1)
    let R : ConvexBody E := ∑ i : Fin d, t i.succ.succ • K i
    have hsum (L : ConvexBody E) :
        (∑ i, t i • (Fin.cons L (Fin.cons L K)) i) = s • L + R := by
      dsimp [s, R]
      simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.succ_zero_eq_one]
      rw [← add_assoc, ← body_add_smul L (ht' 0) (ht' 1)]
    simp only [MvPolynomial.eval_add, p, volumePolynomial_eval μ _ t ht', hsum]
    have h := joinBody_cayley_volume μ (s • A) (s • B) R
    rw [joinBody_smul A B hs] at h
    simpa only [← smul_add, D] using h
  have hcoeff := congrArg (fun P : MvPolynomial (Fin (d + 2)) ℝ =>
    P.coeff (squarefreeExponent (d + 2)) / (d + 2).factorial) hpoly
  have hquad :
      mixedVolume μ (Fin.cons (D + D) (Fin.cons (D + D) K)) +
          mixedVolume μ (Fin.cons (A + B) (Fin.cons (A + B) K)) =
        mixedVolume μ (Fin.cons (D + A) (Fin.cons (D + A) K)) +
          mixedVolume μ (Fin.cons (D + B) (Fin.cons (D + B) K)) := by
    simpa only [p, mixedVolume, MvPolynomial.coeff_add, add_div] using hcoeff
  let q : ConvexBody E → ConvexBody E → ℝ :=
    fun X Y => mixedVolume μ (Fin.cons X (Fin.cons Y K))
  have hadd (X Y T : ConvexBody E) : q (X + Y) T = q X T + q Y T :=
    PolyhedralSupport.mixedVolume_cons_add μ X Y (Fin.cons T K)
  have hsymm (X Y : ConvexBody E) : q X Y = q Y X :=
    PolyhedralSupport.mixedVolume_cons_cons_swap μ X Y K
  have hadd_right (X Y T : ConvexBody E) : q X (Y + T) = q X Y + q X T := by
    rw [hsymm, hadd, hsymm Y X, hsymm T X]
  change q (D + D) (D + D) + q (A + B) (A + B) =
    q (D + A) (D + A) + q (D + B) (D + B) at hquad
  simp only [hadd, hadd_right] at hquad
  rw [hsymm A D, hsymm B D, hsymm B A] at hquad
  change q D D + q A B = q D A + q D B
  linarith

end Volume
end RankThreeProjection
end
end
end DevelopmentSource30

/- Source module: Projection.Rigidity.RadialMixedVolume. SHA256: b09a7d4ed1f6be3b2200cc4eb7b68cdee3db3cf6ee1891b636850923830e8ed3 -/
section DevelopmentSource31






/-!
# The weak mixed-volume consequence of projected equality

This file connects the radial first variation of actual volume to the mixed
volume already defined by the Minkowski polynomial. A convex-hull argument
then extracts the nonnegative support difference needed for weak rigidity.
The conclusion is an equality of genuine mixed volumes, so it transfers
between Euclidean and other finite-dimensional normed coordinate models
without transporting any normal sphere or area measure.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory Metric Filter Topology Function Module
open scoped ENNReal NNReal RealInnerProductSpace Pointwise Gradient

namespace OAI.PettyProjection
open Spherical (Sphere norm_coe sigma mean)
open VolumePolynomials RankThreeProjection

theorem support_joinBody {n : ℕ} (A B : ConvexBody (Space n)) (u : Space n) :
    support (joinBody A B : Set (Space n)) u =
      max (support (A : Set (Space n)) u) (support (B : Set (Space n)) u) := by
  apply le_antisymm
  · apply (support_le_iff (joinBody A B).isCompact (joinBody A B).nonempty).mpr
    intro z hz
    obtain ⟨a, ha, b, hb, r, t, hr, ht, hrt, rfl⟩ := mem_convexJoin.mp hz
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    have ha' := (inner_le_support A.isCompact ha u).trans
      (le_max_left (support (A : Set (Space n)) u) (support (B : Set (Space n)) u))
    have hb' := (inner_le_support B.isCompact hb u).trans
      (le_max_right (support (A : Set (Space n)) u) (support (B : Set (Space n)) u))
    calc
      _ ≤ r * max (support (A : Set (Space n)) u) (support (B : Set (Space n)) u) +
          t * max (support (A : Set (Space n)) u) (support (B : Set (Space n)) u) :=
        add_le_add (mul_le_mul_of_nonneg_left ha' hr) (mul_le_mul_of_nonneg_left hb' ht)
      _ = _ := by rw [← add_mul, hrt, one_mul]
  · apply max_le
    · obtain ⟨a, ha, hea⟩ := support_attained A.isCompact A.nonempty u
      rw [hea]
      exact inner_le_support (joinBody A B).isCompact (le_joinBody_left A B ha) u
    · obtain ⟨b, hb, heb⟩ := support_attained B.isCompact B.nonempty u
      rw [heb]
      exact inner_le_support (joinBody A B).isCompact (le_joinBody_right A B hb) u

/-- First variation of actual Minkowski volume, identified with the exact
coefficient of its actual volume polynomial. -/
theorem mixedVolume_first_radial {d : ℕ}
    (K A : ConvexBody (Space (d + 1))) (h0 : (K : Set (Space (d + 1))) ∈ 𝓝 0) :
    (d + 1 : ℝ) * mixedVolume volume (Fin.cons A (fun _ : Fin d => K)) =
      (d + 1 : ℝ) * kappa (d + 1) *
        ∫ u, radialDensity (K : Set (Space (d + 1)))
          (support (A : Set (Space (d + 1)))) u ∂sigma (d + 1) := by
  have hdim : finrank ℝ (Space (d + 1)) = d + 1 := finrank_euclideanSpace_fin
  have hp' := RankThreeProjection.Rigidity.hasDerivWithinAt_minkowskiRayVolume
    volume K A hdim
  have hr := minkowski_volume_derivative K.isCompact K.convex h0 A.isCompact A.convex A.nonempty
  have hr' : HasDerivWithinAt
      (fun t : ℝ => volume.real ((K + t • A : ConvexBody (Space (d + 1))) : Set (Space (d + 1))))
      ((d + 1 : ℝ) * kappa (d + 1) *
        ∫ u, radialDensity (K : Set (Space (d + 1)))
          (support (A : Set (Space (d + 1)))) u ∂sigma (d + 1)) (Ici 0) 0 := by
    simpa only [ConvexBody.coe_add, ConvexBody.coe_smul, radialDensity, bodyRadius,
      mean, Nat.cast_add, Nat.cast_one] using hr
  exact (uniqueDiffWithinAt_Ici (0 : ℝ)).eq_deriv (Ici 0) hp' hr'

/-- Equality at almost every radial normal makes the first mixed volume of
the actual convex hull equal to that of each comparison body. -/
theorem mixedVolume_join_eq_of_radial_equality {d : ℕ}
    (K A B : ConvexBody (Space (d + 1))) (h0 : (K : Set (Space (d + 1))) ∈ 𝓝 0)
    (he : ∀ᵐ (u : Sphere (d + 1)) ∂sigma (d + 1),
      support (A : Set (Space (d + 1))) (∇ (gauge (K : Set (Space (d + 1)))) (u : Space (d + 1))) =
      support (B : Set (Space (d + 1))) (∇ (gauge (K : Set (Space (d + 1)))) (u : Space (d + 1)))) :
    mixedVolume volume (Fin.cons (joinBody A B) (fun _ : Fin d => K)) =
        mixedVolume volume (Fin.cons A (fun _ : Fin d => K)) ∧
      mixedVolume volume (Fin.cons (joinBody A B) (fun _ : Fin d => K)) =
        mixedVolume volume (Fin.cons B (fun _ : Fin d => K)) := by
  have hI : (∫ u, radialDensity (K : Set (Space (d + 1)))
      (support (joinBody A B : Set (Space (d + 1)))) u ∂sigma (d + 1)) =
      ∫ u, radialDensity (K : Set (Space (d + 1)))
        (support (A : Set (Space (d + 1)))) u ∂sigma (d + 1) := by
    apply integral_congr_ae
    filter_upwards [he] with u hu
    simp only [radialDensity, support_joinBody, ← hu, max_self]
  have hAB : (∫ u, radialDensity (K : Set (Space (d + 1)))
      (support (A : Set (Space (d + 1)))) u ∂sigma (d + 1)) =
      ∫ u, radialDensity (K : Set (Space (d + 1)))
        (support (B : Set (Space (d + 1)))) u ∂sigma (d + 1) := by
    apply integral_congr_ae
    filter_upwards [he] with u hu
    simp only [radialDensity, hu]
  have hn : (d + 1 : ℝ) ≠ 0 := by positivity
  constructor
  · apply mul_left_cancel₀ hn
    rw [mixedVolume_first_radial K (joinBody A B) h0, mixedVolume_first_radial K A h0, hI]
  · apply mul_left_cancel₀ hn
    rw [mixedVolume_first_radial K (joinBody A B) h0, mixedVolume_first_radial K B h0, hI, hAB]

/-- Norm-independent weak conclusion from equality of the actual projected
first variations. This is the exact bridge consumed by convex-hull rigidity. -/
theorem mixedVolume_join_eq_of_ridge_variations {d : ℕ}
    (K A B : ConvexBody (Space (d + 1))) (h0 : (K : Set (Space (d + 1))) ∈ 𝓝 0)
    (hcos : ∀ ξ : Space (d + 1), HasDerivWithinAt
      (fun t : ℝ => (∫ x in (K : Set (Space (d + 1))) + t • (A : Set (Space (d + 1))),
        Real.cos ⟪x, ξ⟫) -
        ∫ x in (K : Set (Space (d + 1))) + t • (B : Set (Space (d + 1))),
          Real.cos ⟪x, ξ⟫) 0 (Ici 0) 0)
    (hsin : ∀ ξ : Space (d + 1), HasDerivWithinAt
      (fun t : ℝ => (∫ x in (K : Set (Space (d + 1))) + t • (A : Set (Space (d + 1))),
        Real.sin ⟪x, ξ⟫) -
        ∫ x in (K : Set (Space (d + 1))) + t • (B : Set (Space (d + 1))),
          Real.sin ⟪x, ξ⟫) 0 (Ici 0) 0) :
    mixedVolume volume (Fin.cons (joinBody A B) (fun _ : Fin d => K)) =
        mixedVolume volume (Fin.cons A (fun _ : Fin d => K)) ∧
      mixedVolume volume (Fin.cons (joinBody A B) (fun _ : Fin d => K)) =
        mixedVolume volume (Fin.cons B (fun _ : Fin d => K)) := by
  apply mixedVolume_join_eq_of_radial_equality K A B h0
  exact support_gradient_ae_eq_of_ridge_variations K.isCompact K.convex h0
    A.isCompact A.convex A.nonempty B.isCompact B.convex B.nonempty hcos hsin

end OAI.PettyProjection
end
end
end DevelopmentSource31

/- Source module: Projection.Rigidity.QuantileTranslation. SHA256: 738ce1d3597b7a910d8c23f2b99017a3c44400d3a86af0c8b880f8c4b796d5a2 -/
section DevelopmentSource32







/-!
# Exact translation of conditional height laws and quantiles

Translating the comparison body by `v` translates its Minkowski ray at time
`t` by `t • v`. The height quantile is consequently shifted by `t * ⟪e,v⟫`.
These are identities of the actual bodies and their normalized Haar measures.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory ProbabilityTheory
open scoped Pointwise RealInnerProductSpace

namespace RankThreeProjection.Rigidity
open VolumePolynomials QuantileStability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Normalizing Haar measure on a translated set commutes with translation. -/
theorem map_cond_vadd (v : E) (K : Set E) :
    (volume[|K]).map (fun x : E => v + x) = volume[|v +ᵥ K] := by
  have hpre : (fun x : E => v + x) ⁻¹' (v +ᵥ K) = K := by
    ext x
    simp only [mem_preimage, mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
      neg_add_cancel_left]
  have hrestrict : (volume.restrict K).map (fun x : E => v + x) =
      volume.restrict (v +ᵥ K) := by
    have h := (MeasurableEquiv.addLeft v).measurableEmbedding.restrict_map
      (volume : Measure E) (v +ᵥ K)
    change ((volume : Measure E).map (fun x => v + x)).restrict (v +ᵥ K) =
      (volume.restrict ((fun x => v + x) ⁻¹' (v +ᵥ K))).map (fun x => v + x) at h
    rw [map_add_left_eq_self, hpre] at h
    exact h.symm
  rw [ProbabilityTheory.cond, ProbabilityTheory.cond, Measure.map_smul _ (by fun_prop), measure_vadd, hrestrict]

/-- The one-dimensional height law shifts by the corresponding scalar. -/
theorem heightLaw_vadd (K : Set E) (v e : E) :
    (volume[|v +ᵥ K]).map (fun x => ⟪e, x⟫) =
      ((volume[|K]).map (fun x => ⟪e, x⟫)).map (fun s : ℝ => ⟪e, v⟫ + s) := by
  rw [← map_cond_vadd, Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  exact inner_add_right e v x

theorem conditional_ridge_integral_vadd (K : Set E) (v e : E)
    (ψ : ℝ → ℝ) (hψ : Continuous ψ) :
    (∫ x, ψ ⟪e, x⟫ ∂volume[|v +ᵥ K]) =
      ∫ x, ψ (⟪e, v⟫ + ⟪e, x⟫) ∂volume[|K] := by
  rw [← map_cond_vadd, integral_map (by fun_prop) (by fun_prop)]
  apply integral_congr_ae
  filter_upwards with x
  rw [inner_add_right]

theorem heightQuantile_translateBody (K : ConvexBody E) (v e : E)
    (hK : volume (K : Set E) ≠ 0) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    heightQuantile (translateBody v K : Set E) e u =
      heightQuantile (K : Set E) e u + ⟪e, v⟫ := by
  letI : IsProbabilityMeasure (volume[|(K : Set E)]) :=
    cond_isProbabilityMeasure_of_finite hK K.isCompact.measure_lt_top.ne
  letI : IsProbabilityMeasure ((volume[|(K : Set E)]).map (fun x => ⟪e, x⟫)) :=
    inferInstance
  unfold heightQuantile
  rw [coe_translateBody, heightLaw_vadd]
  rw [Measure.quantile_map_of_monotone (fun _ _ h => add_le_add le_rfl h)
    (by fun_prop) hu.1 hu.2]
  exact add_comm _ _

/-- Translation acts on the actual Minkowski ray with its usual factor. -/
theorem minkowskiRay_translate_comparison (K C : ConvexBody E) (v : E) (t : ℝ) :
    K + t • translateBody v C = translateBody (t • v) (K + t • C) := by
  simp only [translateBody, smul_add, ← pointBody_smul]
  ac_rfl

theorem minkowskiRay_volume_translate_comparison (K C : ConvexBody E) (v : E) (t : ℝ) :
    volume.real ((K + t • translateBody v C : ConvexBody E) : Set E) =
      volume.real ((K + t • C : ConvexBody E) : Set E) := by
  simp only [minkowskiRay_translate_comparison, coe_translateBody,
    Measure.real, measure_vadd]

theorem volume_minkowskiRay_ne_zero (K C : ConvexBody E)
    (hK : volume (K : Set E) ≠ 0) (t : ℝ) :
    volume ((K + t • C : ConvexBody E) : Set E) ≠ 0 := by
  obtain ⟨c, hc⟩ := C.nonempty
  have hsub : translateBody (t • c) K ≤ K + t • C := by
    intro x hx
    change x ∈ (translateBody (t • c) K : Set E) at hx
    rw [coe_translateBody] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    exact ⟨k, hk, t • c, smul_mem_smul_set hc, by simp only [vadd_eq_add, add_comm]⟩
  have hm := measure_mono (μ := volume) hsub
  rw [coe_translateBody, measure_vadd] at hm
  intro hz
  exact hK (le_zero_iff.mp (hz ▸ hm))

/-- This exact shift removes the centroid drift in every projected quantile. -/
theorem heightQuantile_minkowskiRay_translate (K C : ConvexBody E)
    (v e : E) (hK : volume (K : Set E) ≠ 0) (t : ℝ)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    heightQuantile ((K + t • translateBody v C : ConvexBody E) : Set E) e u =
      heightQuantile ((K + t • C : ConvexBody E) : Set E) e u + t * ⟪e, v⟫ := by
  rw [minkowskiRay_translate_comparison,
    heightQuantile_translateBody (K + t • C) (t • v) e
      (volume_minkowskiRay_ne_zero K C hK t) hu, real_inner_smul_right]

theorem heightQuantile_minkowskiRay_sub_translation (K C : ConvexBody E)
    (v e : E) (hK : volume (K : Set E) ≠ 0) (t : ℝ)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    heightQuantile ((K + t • translateBody (-v) C : ConvexBody E) : Set E) e u =
      heightQuantile ((K + t • C : ConvexBody E) : Set E) e u - t * ⟪e, v⟫ := by
  rw [heightQuantile_minkowskiRay_translate K C (-v) e hK t hu, inner_neg_right]
  ring

end RankThreeProjection.Rigidity
end
end
end DevelopmentSource32

/- Source module: Projection.Rigidity.NormalizedVariation. SHA256: ab34837ec408f87c059b7cbb38ddd2fe7fc0f5b84e1a2d6ef1934fc6b09121d1 -/
section DevelopmentSource33






/-!
# Removing probability normalization from first variations

The quantile argument compares conditional probability measures. The radial
first-variation argument compares unnormalised volume integrals. This lemma
connects them when the actual masses have the same first derivative.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Set

namespace RankThreeProjection.Rigidity

set_option backward.isDefEq.respectTransparency false in
/-- If two masses and two numerators agree at the base point, the masses
have equal first derivatives, and the normalized difference has zero first
derivative, then the unnormalised difference has zero first derivative.
Existence of the individual derivatives is explicit; in the application it
comes from the localized radial first-variation theorem. -/
theorem raw_difference_derivative_zero_of_normalized
    (V W F G : ℝ → ℝ) (v f g x : ℝ) (s : Set ℝ)
    (hs : UniqueDiffWithinAt ℝ s x)
    (hV : HasDerivWithinAt V v s x)
    (hW : HasDerivWithinAt W v s x)
    (hF : HasDerivWithinAt F f s x)
    (hG : HasDerivWithinAt G g s x)
    (hVW : V x = W x) (hFG : F x = G x) (hV0 : V x ≠ 0)
    (hzero : HasDerivWithinAt (fun t => F t / V t - G t / W t) 0 s x) :
    HasDerivWithinAt (fun t => F t - G t) 0 s x := by
  have hW0 : W x ≠ 0 := by rwa [← hVW]
  have hquot := (hF.fun_div hV hV0).fun_sub (hG.fun_div hW hW0)
  have he := hs.eq_deriv s hquot hzero
  rw [← hVW, ← hFG] at he
  field_simp [hV0] at he
  have hprod : (f - g) * V x = 0 := by nlinarith [he]
  have hfg : f = g := sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hV0)
  simpa only [hfg, sub_self] using hF.fun_sub hG

end RankThreeProjection.Rigidity
end
end
end DevelopmentSource33

/- Source module: Projection.Rigidity.ProjectedVariation. SHA256: befffe2e5521b04099f13a62c4bc22bfd35171078f897b9326e4216768a8b82a -/
section DevelopmentSource34







/-!
# From normalized projected variations to the weak hull conclusion

The quantile argument uses conditional probability measures. The localized
radial formula uses unnormalized Lebesgue integrals. Equal first volume
derivatives remove this difference, including after the exact translation of
one comparison body. Every mass and numerator below is an actual integral.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory Metric Filter Topology Function Module ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace Pointwise Gradient

namespace OAI.PettyProjection
open Spherical (Sphere sigma mean)
open VolumePolynomials RankThreeProjection.Rigidity

theorem conditional_integral_eq_div {n : ℕ} (K : Set (Space n)) (ψ : Space n → ℝ) :
    (∫ x, ψ x ∂volume[|K]) = (∫ x in K, ψ x) / volume.real K := by
  rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv]
  simp only [smul_eq_mul, measureReal_def, div_eq_mul_inv]
  rw [mul_comm]

/-- Removing normalization for one actual continuous spatial test. -/
theorem raw_variation_zero_of_conditional {d : ℕ}
    (K A B : ConvexBody (Space (d + 1)))
    (h0 : (K : Set (Space (d + 1))) ∈ 𝓝 (0 : Space (d + 1)))
    (hmass : HasDerivWithinAt
      (fun t : ℝ => volume.real ((K + t • A : ConvexBody (Space (d + 1))) : Set (Space (d + 1))) -
        volume.real ((K + t • B : ConvexBody (Space (d + 1))) : Set (Space (d + 1))))
      0 (Ici 0) 0)
    (ψ : Space (d + 1) → ℝ) (hψ : Continuous ψ)
    (hnorm : HasDerivWithinAt
      (fun t : ℝ => (∫ x, ψ x
        ∂volume[|((K + t • A : ConvexBody (Space (d + 1))) : Set (Space (d + 1)))]) -
        ∫ x, ψ x
          ∂volume[|((K + t • B : ConvexBody (Space (d + 1))) : Set (Space (d + 1)))])
      0 (Ici 0) 0) :
    HasDerivWithinAt
      (fun t : ℝ => (∫ x in (K : Set (Space (d + 1))) + t • (A : Set (Space (d + 1))), ψ x) -
        ∫ x in (K : Set (Space (d + 1))) + t • (B : Set (Space (d + 1))), ψ x)
      0 (Ici 0) 0 := by
  let V : ℝ → ℝ := fun t => volume.real ((K + t • A : ConvexBody (Space (d + 1))) : Set (Space (d + 1)))
  let W : ℝ → ℝ := fun t => volume.real ((K + t • B : ConvexBody (Space (d + 1))) : Set (Space (d + 1)))
  let F : ℝ → ℝ := fun t => ∫ x in ((K + t • A : ConvexBody (Space (d + 1))) : Set (Space (d + 1))), ψ x
  let G : ℝ → ℝ := fun t => ∫ x in ((K + t • B : ConvexBody (Space (d + 1))) : Set (Space (d + 1))), ψ x
  have hdim : finrank ℝ (Space (d + 1)) = d + 1 := finrank_euclideanSpace_fin
  have hV := hasDerivWithinAt_minkowskiRayVolume volume K A hdim
  have hW := hasDerivWithinAt_minkowskiRayVolume volume K B hdim
  have hsame := (uniqueDiffWithinAt_Ici (0 : ℝ)).eq_deriv (Ici 0) (hV.fun_sub hW) hmass
  have hsame' := sub_eq_zero.mp hsame
  rw [← hsame'] at hW
  have hF : HasDerivWithinAt F
      ((d + 1 : ℝ) * kappa (d + 1) * mean (fun u : Sphere (d + 1) =>
        bodyRadius (K : Set (Space (d + 1))) u ^ (d + 1) *
          ψ (radialBoundary (K : Set (Space (d + 1))) u) *
          support (A : Set (Space (d + 1)))
            (∇ (gauge (K : Set (Space (d + 1)))) (u : Space (d + 1))))) (Ici 0) 0 := by
    simpa only [F, ConvexBody.coe_add, ConvexBody.coe_smul, radialBoundary,
      Nat.cast_add, Nat.cast_one] using
      minkowski_integral_derivative K.isCompact K.convex h0 A.isCompact A.convex A.nonempty ψ hψ
  have hG : HasDerivWithinAt G
      ((d + 1 : ℝ) * kappa (d + 1) * mean (fun u : Sphere (d + 1) =>
        bodyRadius (K : Set (Space (d + 1))) u ^ (d + 1) *
          ψ (radialBoundary (K : Set (Space (d + 1))) u) *
          support (B : Set (Space (d + 1)))
            (∇ (gauge (K : Set (Space (d + 1)))) (u : Space (d + 1))))) (Ici 0) 0 := by
    simpa only [G, ConvexBody.coe_add, ConvexBody.coe_smul, radialBoundary,
      Nat.cast_add, Nat.cast_one] using
      minkowski_integral_derivative K.isCompact K.convex h0 B.isCompact B.convex B.nonempty ψ hψ
  have hVpos : 0 < V 0 := by
    simpa only [V, body_zero_smul, add_zero, Measure.real] using
      (ENNReal.toReal_pos (Measure.measure_pos_of_mem_nhds volume h0).ne' K.isCompact.measure_lt_top.ne)
  have hz : HasDerivWithinAt (fun t => F t / V t - G t / W t) 0 (Ici 0) 0 := by
    simpa only [conditional_integral_eq_div, F, G, V, W] using hnorm
  have h := raw_difference_derivative_zero_of_normalized V W F G _ _ _ 0 (Ici 0)
    (uniqueDiffWithinAt_Ici 0) hV hW hF hG
    (by simp only [V, W, body_zero_smul, add_zero])
    (by simp only [F, G, body_zero_smul, add_zero]) hVpos.ne' hz
  simpa only [F, G, ConvexBody.coe_add, ConvexBody.coe_smul] using h

theorem mixedVolume_join_eq_of_conditional_ridge_variations {d : ℕ}
    (K A B : ConvexBody (Space (d + 1)))
    (h0 : (K : Set (Space (d + 1))) ∈ 𝓝 (0 : Space (d + 1)))
    (hmass : HasDerivWithinAt
      (fun t : ℝ => volume.real ((K + t • A : ConvexBody (Space (d + 1))) : Set (Space (d + 1))) -
        volume.real ((K + t • B : ConvexBody (Space (d + 1))) : Set (Space (d + 1))))
      0 (Ici 0) 0)
    (hcos : ∀ ξ : Space (d + 1), HasDerivWithinAt
      (fun t : ℝ => (∫ x, Real.cos ⟪x, ξ⟫
        ∂volume[|((K + t • A : ConvexBody (Space (d + 1))) : Set (Space (d + 1)))]) -
        ∫ x, Real.cos ⟪x, ξ⟫
          ∂volume[|((K + t • B : ConvexBody (Space (d + 1))) : Set (Space (d + 1)))])
      0 (Ici 0) 0)
    (hsin : ∀ ξ : Space (d + 1), HasDerivWithinAt
      (fun t : ℝ => (∫ x, Real.sin ⟪x, ξ⟫
        ∂volume[|((K + t • A : ConvexBody (Space (d + 1))) : Set (Space (d + 1)))]) -
        ∫ x, Real.sin ⟪x, ξ⟫
          ∂volume[|((K + t • B : ConvexBody (Space (d + 1))) : Set (Space (d + 1)))])
      0 (Ici 0) 0) :
    mixedVolume volume (Fin.cons (RankThreeProjection.joinBody A B) (fun _ : Fin d => K)) =
      mixedVolume volume (Fin.cons A (fun _ : Fin d => K)) := by
  exact (mixedVolume_join_eq_of_ridge_variations K A B h0
    (fun ξ => raw_variation_zero_of_conditional K A B h0 hmass _ (by fun_prop) (hcos ξ))
    (fun ξ => raw_variation_zero_of_conditional K A B h0 hmass _ (by fun_prop) (hsin ξ))).1

/-- Final radial assembly under actual AF equality. The only analytic input
is the centered conditional sine/cosine variation supplied by the quantiles. -/
theorem weak_hull_of_AF_conditional_ridge_variations {d : ℕ}
    (K A C : ConvexBody (Space (d + 2)))
    (h0 : (K : Set (Space (d + 2))) ∈ 𝓝 (0 : Space (d + 2)))
    (a : ℝ) (ha : 0 < a)
    (hAA : mixedVolume volume (Fin.cons A (Fin.cons A (fun _ : Fin d => K))) = a)
    (hAC : mixedVolume volume (Fin.cons A (Fin.cons C (fun _ : Fin d => K))) = a)
    (hCC : mixedVolume volume (Fin.cons C (Fin.cons C (fun _ : Fin d => K))) = a)
    (v : Space (d + 2))
    (hcos : ∀ ξ : Space (d + 2), HasDerivWithinAt
      (fun t : ℝ => (∫ x, Real.cos ⟪x, ξ⟫
        ∂volume[|((K + t • A : ConvexBody (Space (d + 2))) : Set (Space (d + 2)))]) -
        ∫ x, Real.cos ⟪x, ξ⟫
          ∂volume[|((K + t • translateBody v C : ConvexBody (Space (d + 2))) : Set (Space (d + 2)))])
      0 (Ici 0) 0)
    (hsin : ∀ ξ : Space (d + 2), HasDerivWithinAt
      (fun t : ℝ => (∫ x, Real.sin ⟪x, ξ⟫
        ∂volume[|((K + t • A : ConvexBody (Space (d + 2))) : Set (Space (d + 2)))]) -
        ∫ x, Real.sin ⟪x, ξ⟫
          ∂volume[|((K + t • translateBody v C : ConvexBody (Space (d + 2))) : Set (Space (d + 2)))])
      0 (Ici 0) 0) :
    mixedVolume volume (Fin.cons (RankThreeProjection.joinBody A (translateBody v C))
      (Fin.cons K (fun _ : Fin d => K))) =
      mixedVolume volume (Fin.cons A (Fin.cons K (fun _ : Fin d => K))) := by
  have hdim : finrank ℝ (Space (d + 2)) = d + 2 := finrank_euclideanSpace_fin
  have hmass := actual_ray_volume_difference_derivative_zero volume K hdim A C a ha hAA hAC hCC
  have hmass' : HasDerivWithinAt
      (fun t : ℝ => volume.real ((K + t • A : ConvexBody (Space (d + 2))) : Set (Space (d + 2))) -
        volume.real ((K + t • translateBody v C : ConvexBody (Space (d + 2))) : Set (Space (d + 2))))
      0 (Ici 0) 0 := by
    simpa only [minkowskiRay_volume_translate_comparison] using hmass
  simpa only [MultilinearDiagonal.cons_const] using
    mixedVolume_join_eq_of_conditional_ridge_variations K A (translateBody v C) h0 hmass' hcos hsin

end OAI.PettyProjection
end
end
end DevelopmentSource34

/- Source module: Projection.Rigidity.EuclideanWeakHull. SHA256: 0ed6e714f4137cd77b88809c370a329cb8bcaf8e56b8547fb27c5ec5da66df78 -/
section DevelopmentSource35







/-!
# The Euclidean weak hull conclusion

Actual mixed-volume equality gives the centered L¹ limit for every height
quantile. The derivatives of all directional means come from one centroid
vector. Translating one comparison body by the negative of that vector makes
every normalized Lipschitz ridge variation vanish. Fourier uniqueness and
the localized radial formula then give the actual mixed-volume identity for
the convex hull. No rigidity statement is assumed in this assembly.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory ProbabilityTheory Filter Module
open scoped Pointwise RealInnerProductSpace Topology

namespace RankThreeProjection.QuantileStability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Inverse-transform sampling applies to every continuous height test,
including sine and cosine at an arbitrary frequency. -/
theorem integral_heightQuantile_test (K : ConvexBody E) (e : E)
    (hK : volume (K : Set E) ≠ 0) (ψ : ℝ → ℝ) (hψ : Continuous ψ) :
    (∫ τ in Ioo (0 : ℝ) 1, ψ (heightQuantile (K : Set E) e τ)) =
      ∫ x, ψ ⟪e, x⟫ ∂volume[|(K : Set E)] := by
  letI : IsProbabilityMeasure (volume[|(K : Set E)]) :=
    cond_isProbabilityMeasure_of_finite hK K.isCompact.measure_lt_top.ne
  let ν : Measure ℝ := (volume[|(K : Set E)]).map (fun x => ⟪e, x⟫)
  letI : IsProbabilityMeasure ν := inferInstance
  change (∫ τ in Ioo (0 : ℝ) 1, ψ (ν.quantile τ)) = _
  rw [← integral_map (Measure.measurable_quantile ν).aemeasurable
    hψ.aestronglyMeasurable, Measure.map_quantile_volume_Ioo]
  exact integral_map (continuous_const.inner continuous_id).measurable.aemeasurable
    hψ.aestronglyMeasurable

end RankThreeProjection.QuantileStability

namespace OAI.PettyProjection

open VolumePolynomials RankThreeProjection.Rigidity RankThreeProjection.QuantileStability

/-- The weak hull identity for arbitrary origin-containing comparison bodies
and an origin-interior Euclidean reference body. The comparison bodies may
have any dimension. Every hypothesis is an actual mixed-volume equality. -/
theorem euclidean_origin_weak_hull {d : ℕ}
    (K A C : ConvexBody (Space (d + 2)))
    (hK : (0 : Space (d + 2)) ∈ interior (K : Set (Space (d + 2))))
    (hA : (0 : Space (d + 2)) ∈ A) (hC : (0 : Space (d + 2)) ∈ C)
    (a : ℝ) (ha : 0 < a)
    (hAA : mixedVolume volume (Fin.cons A (Fin.cons A (fun _ : Fin d => K))) = a)
    (hAC : mixedVolume volume (Fin.cons A (Fin.cons C (fun _ : Fin d => K))) = a)
    (hCC : mixedVolume volume (Fin.cons C (Fin.cons C (fun _ : Fin d => K))) = a) :
    ∃ w : Space (d + 2),
      mixedVolume volume (Fin.cons (RankThreeProjection.joinBody A (translateBody w C))
        (Fin.cons K (fun _ : Fin d => K))) =
      mixedVolume volume (Fin.cons A (Fin.cons K (fun _ : Fin d => K))) := by
  letI : NeZero (d + 2) := ⟨by omega⟩
  have h0 : (K : Set (Space (d + 2))) ∈ 𝓝 (0 : Space (d + 2)) :=
    mem_interior_iff_mem_nhds.mp hK
  have hK0 : volume (K : Set (Space (d + 2))) ≠ 0 :=
    (Measure.measure_pos_of_mem_nhds volume h0).ne'
  have hdim : finrank ℝ (Space (d + 2)) = d + 2 := finrank_euclideanSpace_fin
  obtain ⟨v, hv⟩ := exists_centroid_difference_derivative K A C h0
  let B : ConvexBody (Space (d + 2)) := translateBody (-v) C
  let μ : ℝ → Measure (Space (d + 2)) := fun t =>
    volume[|((K + t • A : ConvexBody (Space (d + 2))) : Set (Space (d + 2)))]
  let ν : ℝ → Measure (Space (d + 2)) := fun t =>
    volume[|((K + t • B : ConvexBody (Space (d + 2))) : Set (Space (d + 2)))]
  have hAt (t : ℝ) := volume_minkowskiRay_ne_zero K A hK0 t
  have hBt (t : ℝ) := volume_minkowskiRay_ne_zero K B hK0 t
  have hμ (t : ℝ) : IsProbabilityMeasure (μ t) :=
    cond_isProbabilityMeasure_of_finite (hAt t) (K + t • A).isCompact.measure_lt_top.ne
  have hν (t : ℝ) : IsProbabilityMeasure (ν t) :=
    cond_isProbabilityMeasure_of_finite (hBt t) (K + t • B).isCompact.measure_lt_top.ne
  have hunit (e : Space (d + 2)) (he : ‖e‖ = 1)
      (ψ : ℝ → ℝ) (L : NNReal) (hψ : LipschitzWith L ψ) :
      HasDerivWithinAt
        (fun t : ℝ => (∫ x, ψ ⟪e, x⟫ ∂μ t) - ∫ x, ψ ⟪e, x⟫ ∂ν t)
        0 (Ici 0) 0 := by
    let η : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)
    let f : ℝ → ℝ → ℝ := fun t τ =>
      heightQuantile ((K + t • A : ConvexBody (Space (d + 2))) : Set (Space (d + 2))) e τ
    let g : ℝ → ℝ → ℝ := fun t τ =>
      heightQuantile ((K + t • B : ConvexBody (Space (d + 2))) : Set (Space (d + 2))) e τ
    have hf (t : ℝ) : Integrable (f t) η :=
      integrableOn_heightQuantile (K + t • A) e (hAt t)
    have hg (t : ℝ) : Integrable (g t) η :=
      integrableOn_heightQuantile (K + t • B) e (hBt t)
    have hlim := actual_centered_quantile_L1_limit K A C hdim hK hA hC
      a ha hAA hAC hCC he ⟪e, v⟫ (hv e)
    have hL1 : Tendsto (fun t : ℝ => ∫ τ, |(g t τ - f t τ) / t| ∂η)
        (𝓝[>] 0) (𝓝 0) := by
      apply Filter.Tendsto.congr' _ hlim
      filter_upwards [self_mem_nhdsWithin] with t ht
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with τ hτ
      dsimp only [g, f, B]
      rw [heightQuantile_minkowskiRay_sub_translation K C v e hK0 t hτ]
      congr 1
      field_simp [ne_of_gt ht]
      ring
    have hbase : g 0 =ᵐ[η] f 0 := by
      filter_upwards with τ
      simp only [g, f, body_zero_smul, add_zero]
    have hint : ∀ᶠ t in 𝓝[>] (0 : ℝ),
        Integrable (fun τ => ψ (f t τ)) η ∧
          Integrable (fun τ => ψ (g t τ)) η ∧
            Integrable (fun τ => (g t τ - f t τ) / t) η := by
      apply Eventually.of_forall
      intro t
      exact ⟨integrable_lipschitz_test η (hf t) ψ L hψ,
        integrable_lipschitz_test η (hg t) ψ L hψ, ((hg t).sub (hf t)).div_const t⟩
    have hderiv :=
      (hasDerivWithinAt_lipschitz_test_difference_zero η f g ψ L hψ hbase hint hL1).neg
    simp only [Pi.neg_def, neg_zero, neg_sub] at hderiv
    have hfa (t : ℝ) : (∫ τ, ψ (f t τ) ∂η) = ∫ x, ψ ⟪e, x⟫ ∂μ t :=
      integral_heightQuantile_test (K + t • A) e (hAt t) ψ hψ.continuous
    have hgb (t : ℝ) : (∫ τ, ψ (g t τ) ∂η) = ∫ x, ψ ⟪e, x⟫ ∂ν t :=
      integral_heightQuantile_test (K + t • B) e (hBt t) ψ hψ.continuous
    simpa only [hfa, hgb] using hderiv
  obtain ⟨hcos, hsin⟩ := fourier_variations_of_unit_lipschitz_variations μ ν hμ hν hunit
  refine ⟨-v, ?_⟩
  exact weak_hull_of_AF_conditional_ridge_variations K A C h0 a ha hAA hAC hCC (-v)
    hcos hsin

end OAI.PettyProjection
end
end
end DevelopmentSource35

#check @OAI.PettyProjection.euclidean_origin_weak_hull
#print axioms OAI.PettyProjection.euclidean_origin_weak_hull
#assert_standard_axioms OAI.PettyProjection.euclidean_origin_weak_hull
#export_checked_module_dependencies ".lake/reports/verification/AnalyticRigidity.dependencies.json"
