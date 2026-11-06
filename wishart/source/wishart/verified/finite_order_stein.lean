module

public import wishart.verified.finite_order_growth

/-!
# Stein identities for finite-order tests

Only C¹ regularity and polynomial bounds for the value and first derivative
are required.  For Wishart tests the bounds are imposed on the positive
semidefinite cone alone, the support of the actual measure.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti.Probability Matrix Filter Set
open WishartVerification
open scoped RealInnerProductSpace Matrix.Norms.Operator

namespace Wishart.FiniteOrder

theorem gaussian_stein_c1 {p : ℕ} {C : Matrix (Fin p) (Fin p) ℝ}
    (hC : C.PosDef) {g : EuclideanSpace ℝ (Fin p) → ℝ}
    (hg : C1PolynomialOn univ g) (h : EuclideanSpace ℝ (Fin p)) :
    (∫ x, ⟪h, C⁻¹.toEuclideanLin x⟫ * g x ∂multivariateGaussian 0 C) =
      ∫ x, fderiv ℝ g x h ∂multivariateGaussian 0 C := by
  have hμ := allFiniteMoments_gaussian_norm (μ := multivariateGaussian 0 C)
  have hs : (fun x : EuclideanSpace ℝ (Fin p) => ⟪h, C⁻¹.toEuclideanLin x⟫).HasTemperateGrowth :=
    (innerSL ℝ h).hasTemperateGrowth.comp C⁻¹.toEuclideanLin.toContinuousLinearMap.hasTemperateGrowth
  have hsupport : ∀ᵐ x ∂multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) C,
      x ∈ (univ : Set (EuclideanSpace ℝ (Fin p))) := Eventually.of_forall (mem_univ ·)
  symm
  apply extend_compact_stein continuous_const hs.1.continuous
    (fun f hf hcpt => (gaussian_stein_compact hC hf hcpt h).symm) hg.regular
  · exact ((PolynomialBoundOn.of_temperate hs).mul hg.value).integrable hμ
      (hs.1.continuous.mul hg.regular.continuous).aestronglyMeasurable hsupport
  · exact (hg.derivative.clm_apply (PolynomialBoundOn.const univ h)).integrable hμ
      ((hg.regular.continuous_fderiv (by norm_num)).clm_apply continuous_const).aestronglyMeasurable
      hsupport
  · exact ((PolynomialBoundOn.const univ h).norm.mul hg.value.norm).integrable hμ
      (continuous_const.mul hg.regular.continuous.norm).aestronglyMeasurable hsupport

set_option backward.isDefEq.respectTransparency false in
theorem wishart_stein_c1 {p : ℕ} {S : Matrix (Fin p) (Fin p) ℝ}
    (hS : S.PosDef) {ν : ℝ} (hν : (p : ℝ) - 1 < ν)
    {g : SymmetricMatrix p → ℝ} (hg : C1PolynomialOn (psdCone p) g)
    (A : Matrix (Fin p) (Fin p) ℝ) :
    (∫ X, fderiv ℝ g X (congruenceVelocity A X) ∂nonsingularWishartMeasure ν S) =
      ∫ X, (Matrix.trace (S⁻¹ * A * (X : Matrix (Fin p) (Fin p) ℝ)) -
        ν * Matrix.trace A) * g X ∂nonsingularWishartMeasure ν S := by
  letI := isProbabilityMeasure_nonsingularWishartMeasure hS hν
  have hμ := allFiniteMoments_wishart_norm ν S
  have hb := (congruenceVelocity A).hasTemperateGrowth
  let L : SymmetricMatrix p →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    ((Matrix.traceLinearMap (Fin p) ℝ ℝ).comp
      ((LinearMap.mulLeft ℝ (S⁻¹ * A)).comp
        (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)).subtype))
  have hs : (fun X : SymmetricMatrix p =>
      Matrix.trace (S⁻¹ * A * (X : Matrix (Fin p) (Fin p) ℝ)) -
        ν * Matrix.trace A).HasTemperateGrowth :=
    L.hasTemperateGrowth.sub (Function.HasTemperateGrowth.const _)
  have hsupport : ∀ᵐ X ∂nonsingularWishartMeasure ν S, X ∈ psdCone p := by
    filter_upwards [ae_posDef_nonsingularWishartMeasure ν S] with X hX
    exact hX.posSemidef
  apply extend_compact_stein (congruenceVelocity A).continuous hs.1.continuous
    (fun f hf hcpt => wishart_stein_compact hS hν hf hcpt A) hg.regular
  · exact ((PolynomialBoundOn.of_temperate hs).mul hg.value).integrable hμ
      (hs.1.continuous.mul hg.regular.continuous).aestronglyMeasurable hsupport
  · exact (hg.derivative.clm_apply (PolynomialBoundOn.of_temperate hb)).integrable hμ
      ((hg.regular.continuous_fderiv (by norm_num)).clm_apply hb.1.continuous).aestronglyMeasurable
      hsupport
  · exact ((allFiniteMoments_temperate_norm hμ hb).mul
      (hg.value.allFiniteMoments_norm hμ hg.regular.continuous.aestronglyMeasurable
        hsupport)).integrable

theorem wishart_stein_translate_c1 {p : ℕ} {S : Matrix (Fin p) (Fin p) ℝ}
    (hS : S.PosDef) {ν : ℝ} (hν : (p : ℝ) - 1 < ν)
    {g : SymmetricMatrix p → ℝ} (hg : C1PolynomialOn (psdCone p) g)
    (A : Matrix (Fin p) (Fin p) ℝ) (Z : SymmetricMatrix p) (hZ : Z ∈ psdCone p) :
    (∫ X, fderiv ℝ g (X + Z) (congruenceVelocity A X) ∂nonsingularWishartMeasure ν S) =
      ∫ X, (Matrix.trace (S⁻¹ * A * (X : Matrix (Fin p) (Fin p) ℝ)) -
        ν * Matrix.trace A) * g (X + Z) ∂nonsingularWishartMeasure ν S := by
  have hshift : C1PolynomialOn (psdCone p) (fun X : SymmetricMatrix p => X + Z) :=
    C1PolynomialOn.of_temperate
      (Function.HasTemperateGrowth.id.add (Function.HasTemperateGrowth.const Z))
  have htest := hg.comp hshift (add_psd_mapsTo hZ)
  have hid := wishart_stein_c1 hS hν htest A
  have hd (X H : SymmetricMatrix p) :
      fderiv ℝ (fun Y => g (Y + Z)) X H = fderiv ℝ g (X + Z) H := by
    have hcomp := ((hg.regular.differentiable (by norm_num) _).hasFDerivAt.comp X
      ((hasFDerivAt_id X).add_const Z)).fderiv
    have heq : fderiv ℝ (fun Y => g (Y + Z)) X = fderiv ℝ g (X + Z) := by
      simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using hcomp
    exact congrArg (fun T : SymmetricMatrix p →L[ℝ] ℝ => T H) heq
  simpa only [hd] using hid

end Wishart.FiniteOrder
