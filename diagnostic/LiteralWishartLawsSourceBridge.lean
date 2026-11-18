module

public import LiteralWishartLaws
public import TauCeti.Probability.Distributions.Wishart.Nonsingular
public import TauCeti.Probability.Distributions.Wishart.Inverse.Basic

/-! Actual two-module source equality bridge, prepared but uncompiled.
LiteralWishartLaws must first compile as its own canonical-Mathlib-only module.
Importing it here preserves those elaborated definitions before the canonical
Tau Ceti source instances are introduced. This is diagnostic evidence only,
not an official full-preflight replacement or a complete Wishart Challenge. -/

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal Matrix

namespace WishartLiteralLaws

private theorem cast_two : (Nat.cast 2 : ℝ) = 2 := by norm_num
private theorem cast_four : (Nat.cast 4 : ℝ) = 4 := by norm_num

/-- The pointwise inverse coordinate map is precisely the source reconstruction,
including diagonal entries and both index orders. -/
theorem reconstruct_eq (p : ℕ) :
    (reconstruct : (UpperTriangle p → ℝ) → SymmetricMatrix p) =
      (TauCeti.symmetricCoordinates p).symm := by
  funext x
  apply Subtype.ext
  ext i j
  change (if h : i ≤ j then x ⟨(i, j), h⟩ else x ⟨(j, i), le_of_not_ge h⟩) = _
  by_cases h : i ≤ j
  · rw [dif_pos h]
    exact (TauCeti.coe_symmetricCoordinates_symm_apply_of_le x h).symm
  · rw [dif_neg h]
    exact (TauCeti.coe_symmetricCoordinates_symm_apply_of_ge x (le_of_not_ge h)).symm

/-- The exact source measure normalization is retained, not only an unspecified
multiple of Haar measure. -/
theorem symmetricLebesgue_eq (p : ℕ) : symmetricLebesgue p = TauCeti.symmetricLebesgue p := by
  unfold symmetricLebesgue TauCeti.symmetricLebesgue
  rw [reconstruct_eq p]

theorem multivariateGamma_eq : multivariateGamma = TauCeti.multivariateGamma := by
  funext p a
  unfold multivariateGamma TauCeti.multivariateGamma
  rw [cast_two, cast_four]

theorem wishartPDFReal_eq {p : ℕ} :
    @wishartPDFReal p = @TauCeti.Probability.nonsingularWishartPDFReal p := by
  funext n S A
  unfold wishartPDFReal TauCeti.Probability.nonsingularWishartPDFReal
  rw [cast_two, multivariateGamma_eq]

theorem wishartPDF_eq {p : ℕ} :
    @wishartPDF p = @TauCeti.Probability.nonsingularWishartPDF p := by
  funext n S A
  unfold wishartPDF TauCeti.Probability.nonsingularWishartPDF
  rw [wishartPDFReal_eq]

/-- Every real degree and scale, including invalid parameters, is quantified. -/
theorem nonsingularWishartMeasure_eq {p : ℕ} :
    @nonsingularWishartMeasure p = @TauCeti.Probability.nonsingularWishartMeasure p := by
  funext n S
  unfold nonsingularWishartMeasure TauCeti.Probability.nonsingularWishartMeasure
  rw [symmetricLebesgue_eq, wishartPDF_eq]

theorem symmetricInv_eq {p : ℕ} : @symmetricInv p = @TauCeti.symmetricInv p := by
  funext A
  apply Subtype.ext
  rfl

/-- The source inverse law is the exact same map of the exact inverted-scale law. -/
theorem inverseWishartMeasure_eq {p : ℕ} :
    @inverseWishartMeasure p = @TauCeti.Probability.inverseWishartMeasure p := by
  funext n S
  unfold inverseWishartMeasure TauCeti.Probability.inverseWishartMeasure
  rw [nonsingularWishartMeasure_eq, symmetricInv_eq]

end WishartLiteralLaws
