module

public import PaperVerification.AlternatingFormsOddAffineDimension
public import PaperVerification.AlternatingFormsSectionFourCoordinates

/-!
# Rationality for the literal Section 4 coefficients

The existing coordinate comparison proves equality of the two actual
homogeneous ideals. Packaging an ideal together with its homogeneity proof
lets that equality transport the full scheme-theoretic birationality
statement, including its original ground-field structure morphism.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open AlgebraicGeometry CategoryTheory MvPolynomial
open scoped AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] [CharZero K]

/-- The finite-dimensional rationality assertion for the literal pair of
forms printed in Section 4, with no implicit coordinate convention left
for the reader to transport. -/
theorem paper_theorem_4_1_section_four_finite_rationality
    (k t : ℕ) (h : t+1 ≤ k) :
    ∃ N : Type, Finite N ∧ Nat.card N = 2*(t+2)*(k-(t+1)) ∧ Scheme.BirationalOver
      (isotropicStructureMap (t := t) (sectionFourPluckerForms (K := K) k))
      (𝔸(N; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K)) := by
  let H := {Q : Ideal (MvPolynomial (PluckerIndex (t+2) (2*k+1)) K) //
    Q.IsHomogeneous (homogeneousSubmodule (PluckerIndex (t+2) (2*k+1)) K)}
  let P : H → Prop := fun Q =>
    ∃ N : Type, Finite N ∧ Nat.card N = 2*(t+2)*(k-(t+1)) ∧ Scheme.BirationalOver
      (HomogeneousQuotientCharts.structureMap Q.val Q.property)
      (𝔸(N; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K))
  let Q₁ : H := ⟨isotropicPluckerIdeal (t := t) (sectionFourPluckerForms (K := K) k),
    isotropicPluckerIdeal_isHomogeneous (sectionFourPluckerForms k)⟩
  let Q₂ : H := ⟨isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k),
    isotropicPluckerIdeal_isHomogeneous (oddPluckerForms k)⟩
  have hQ : Q₁ = Q₂ := Subtype.ext (sectionFour_isotropicPluckerIdeal k t)
  change P Q₁
  rw [hQ]
  exact paper_theorem_4_1_rationality_with_dimension_at_least_two k t h

/-- The standard rationality property follows from the stronger finite
birational witness for the exact Section 4 pair. -/
theorem paper_theorem_4_1_section_four_rationality
    (k t : ℕ) (h : t+1 ≤ k) :
    Scheme.IsRationalOver
      (isotropicStructureMap (t := t) (sectionFourPluckerForms (K := K) k)) := by
  obtain ⟨N, _, _, hN⟩ := paper_theorem_4_1_section_four_finite_rationality (K := K) k t h
  exact ⟨N, hN⟩

end PaperVerification.AlternatingForms
