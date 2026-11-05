module

public import VolumePolynomials.NaturalBoundary
public import VolumePolynomials.RationalTaylor
public import Mathlib.Analysis.Analytic.Constructions

@[expose] public section
noncomputable section

namespace VolumePolynomials

open Metric

theorem one_sub_sq_ne_zero_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) : 1 - z ^ 2 ≠ 0 := by
  first
  | intro h
    have heq : z ^ 2 = 1 := (sub_eq_zero.mp h).symm
    have hn := congrArg norm heq
    rw [norm_pow, norm_one] at hn
    exact ((sq_lt_one_iff₀ (norm_nonneg z)).mpr hz).ne hn

/-- The area formula extends holomorphically to the entire open unit disk. -/
theorem areaGeneratingFunction_analyticOnNhd (θ : ℝ) (hsin : Real.sin θ ≠ 0) :
    AnalyticOnNhd ℂ (areaGeneratingFunction θ) (ball 0 1) := by
  first
  | apply (sineGeneratingFunction_analyticOnNhd θ).div
    · fun_prop
    · intro z hz
      apply mul_ne_zero (one_sub_sq_ne_zero_of_norm_lt_one (by simpa using hz))
      exact_mod_cast hsin

/-- Multiplication by the polynomial denominator would turn any local continuation of area
into one of the sine generating function, including at the points `1` and `-1`. -/
theorem areaGeneratingFunction_no_boundary_extension {θ : ℝ}
    (hθ : Real.cos θ = 1 / 3) (hsin : Real.sin θ ≠ 0) (ζ : Circle) :
    ¬ HasLocalContinuousExtension (areaGeneratingFunction θ) ζ := by
  first
  | rintro ⟨δ, hδ, g, hg, hgeq⟩
    apply sineGeneratingFunction_no_boundary_extension hθ ζ
    refine ⟨δ, hδ, fun z => g z * ((1 - z ^ 2) * (Real.sin θ : ℂ)), ?_, ?_⟩
    · exact hg.mul (by fun_prop)
    · intro z hz hznorm
      change g z * ((1 - z ^ 2) * (Real.sin θ : ℂ)) = sineGeneratingFunction θ z
      rw [hgeq z hz hznorm, areaGeneratingFunction]
      apply div_mul_cancel₀
      apply mul_ne_zero (one_sub_sq_ne_zero_of_norm_lt_one hznorm)
      exact_mod_cast hsin

/-- The exact angle and area formula appearing in Theorem 7.3 have the stated analytic
properties, with no unspecified sign choice for the angular parameter. -/
theorem holonomy_area_analytic_properties :
    AnalyticOnNhd ℂ (areaGeneratingFunction Holonomy.angle) (ball 0 1) ∧
    (∀ ζ : Circle, ¬ HasLocalContinuousExtension (areaGeneratingFunction Holonomy.angle) ζ) ∧
    (∀ n : ℕ, iteratedDeriv n (areaGeneratingFunction Holonomy.angle) 0 / (n.factorial : ℂ) =
      (areaTaylorCoefficient n : ℂ)) := by
  first
  | exact ⟨areaGeneratingFunction_analyticOnNhd _ Holonomy.sin_angle_pos.ne',
      areaGeneratingFunction_no_boundary_extension Holonomy.cos_angle Holonomy.sin_angle_pos.ne',
      areaGeneratingFunction_rational_taylor Holonomy.cos_angle Holonomy.sin_angle_pos⟩

end VolumePolynomials
