module

public import PaperVerification.AlternatingSectionFamilyIdeal
public import PaperVerification.AlternatingFormsPluckerIsotropy

/-!
# The original chart ideal is the image of the section functional

This comparison uses the normalized row matrix before imposing any
isotropy equations.  The finite family of original two-forms induces a
map from the direct sum of actual exterior squares to the polynomial
chart ring.  Its image is exactly the original `isotropicChartIdeal`.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace PaperVerification.AlternatingForms

variable {K : Type*} [Field K] {t n m : ℕ}

/-- The original form with its coefficients in the polynomial chart ring. -/
def chartCoefficientForm (p : PluckerIndex (t + 2) n) (f : StrictPairs n → K) :
    AlternatingMap (MvPolynomial (PluckerChartVariable p) K)
      (Fin n → MvPolynomial (PluckerChartVariable p) K)
      (MvPolynomial (PluckerChartVariable p) K) (Fin 2) :=
  AlternatingSectionAlgebra.coefficientForm
    (fun a : StrictPairs n ↦ a.val.1) (fun a : StrictPairs n ↦ a.val.2)
    (fun a ↦ MvPolynomial.C (f a))

/-- The coefficient formula is the exact original alternating row pairing. -/
theorem chartCoefficientForm_rows (p : PluckerIndex (t + 2) n)
    (f : StrictPairs n → K) (i j : Fin (t + 2)) :
    chartCoefficientForm p f ![pluckerChartMatrix p i, pluckerChartMatrix p j] =
      alternatingRowPair f (pluckerChartMatrix p) i j := by
  simp only [chartCoefficientForm, AlternatingSectionAlgebra.coefficientForm_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, alternatingRowPair,
    Algebra.smul_def, MvPolynomial.algebraMap_eq]

/-- The genuine finite-family functional in the original normalized chart. -/
def isotropicChartSectionFunctional (p : PluckerIndex (t + 2) n)
    (forms : Fin m → StrictPairs n → K) :
    (Fin m → ⋀[MvPolynomial (PluckerChartVariable p) K]^2
      (Fin (t + 2) → MvPolynomial (PluckerChartVariable p) K)) →ₗ[
        MvPolynomial (PluckerChartVariable p) K] MvPolynomial (PluckerChartVariable p) K :=
  AlternatingSectionFamilyIdeal.familyFunctional
    (fun l ↦ chartCoefficientForm p (forms l)) (pluckerChartMatrix p)

/-- Equality of ideals identifies the section's zero equations with the
paper's original scheme equations, including all scheme structure. -/
theorem isotropicChartSectionFunctional_range
    (p : PluckerIndex (t + 2) n) (forms : Fin m → StrictPairs n → K) :
    LinearMap.range (isotropicChartSectionFunctional p forms) =
      isotropicChartIdeal p forms := by
  rw [isotropicChartSectionFunctional,
    AlternatingSectionFamilyIdeal.range_familyFunctional_eq_ideal]
  simp only [chartCoefficientForm_rows]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨l, i, j⟩, rfl⟩
    exact alternatingRowPair_mem_chartIdeal p forms l i j
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨l, ij⟩, rfl⟩
    exact Ideal.subset_span ⟨(l, ij.val.1, ij.val.2), rfl⟩

end PaperVerification.AlternatingForms
