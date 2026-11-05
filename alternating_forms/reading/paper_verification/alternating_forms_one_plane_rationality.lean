module

public import PaperVerification.AlternatingFormsOddRationality
public import PaperVerification.OnePlaneIsotropyComparison

/-!
# Rationality for the literal one-plane isotropy scheme

The one-plane rationality theorem is transported across the proved equality
of schemes over the original field.  The equation ideal contains every
restriction to every pair of universal rows; its vanishing was proved over
arbitrary coefficient algebras in `OnePlaneIsotropyComparison`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

namespace PaperVerification.AlternatingForms

variable {K : Type} [Field K] [CharZero K] {m : ℕ}

/-- The rationality conclusion includes the original scheme equations and
base morphism, for every finite family of forms in odd ambient dimension. -/
theorem onePlaneIsotropic_finite_rationality (k : ℕ)
    (forms : Fin m → StrictPairs (2 * k + 1) → K) :
    ∃ N : Type, Finite N ∧ Scheme.BirationalOver
      (onePlaneIsotropicOver forms).hom
      (𝔸(N; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K)) := by
  rw [onePlaneIsotropicOver_eq]
  exact paper_theorem_4_1_finite_rationality_one_plane (K := K) k

end PaperVerification.AlternatingForms
