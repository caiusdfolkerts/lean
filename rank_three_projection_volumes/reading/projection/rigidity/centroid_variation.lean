module

public import Projection.Rigidity.RadialBoundary
public import Projection.Basic
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Analysis.Calculus.Deriv.Inv

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
