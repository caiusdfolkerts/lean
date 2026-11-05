module

public import Projection.Rigidity.RadialLocalization
public import Projection.Rigidity.RidgeUniqueness
public import Mathlib.Algebra.Module.Torsion.Free

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
