module

public import PaperVerification.AlternatingFormsOnePlane
public import PaperVerification.PolynomialQuotientProjectiveSections

/-!
# Complete sections in the original one-plane Plucker boundary

The actual one-row Plucker ideal is zero, as proved by the inverse minor
map.  The original homogeneous quotient grading therefore satisfies the
all-variable polynomial section theorem.  This includes k=0, when Proj
is a point, and every nonnegative Plucker degree.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms

open MvPolynomial AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type*} [Field K]

/-- Homogeneity of the actual one-plane kernel follows from its proved
vanishing; no higher-plane chart or dimension argument is needed. -/
theorem onePlane_matrixPluckerIdeal_isHomogeneous (n : ℕ) :
    (matrixPluckerIdeal (K := K) (s := 1) (n := n)).IsHomogeneous
      (homogeneousSubmodule (PluckerIndex 1 n) K) := by
  rw [onePlane_matrixPluckerIdeal]
  exact Ideal.IsHomogeneous.bot _

/-- The original homogeneous quotient grading for one-plane Plucker coordinates. -/
def onePlaneProjectiveGrading (k : ℕ) : ℕ → Submodule K
    (MvPolynomial (PluckerIndex 1 (2*k+1)) K⧸matrixPluckerIdeal) :=
  HomogeneousQuotientProjective.grading _ (onePlane_matrixPluckerIdeal_isHomogeneous (2*k+1))

instance onePlaneProjectiveGradedAlgebra (k : ℕ) :
    GradedAlgebra (onePlaneProjectiveGrading (K := K) k) :=
  HomogeneousQuotientProjective.quotientGradedAlgebra _ _

/-- The canonical map to complete actual twisting-sheaf sections is an
isomorphism in every degree, for every odd ambient dimension including one. -/
theorem onePlane_bijective_toTwistingSheaf_top (k d : ℕ) :
    Function.Bijective (Proj.toTwistingSheaf (onePlaneProjectiveGrading (K := K) k)
      (rfl : (d : ℤ)=d) ⊤) := by
  letI : Nonempty (PluckerIndex 1 (2*k+1)) := ⟨onePlaneIndex (0 : Fin (2*k+1))⟩
  exact PolynomialQuotientProjectiveSections.bijective_toTwistingSheaf_top
    (Q := matrixPluckerIdeal (K := K) (s := 1) (n := 2*k+1))
    (hQ := onePlane_matrixPluckerIdeal_isHomogeneous (2*k+1))
    (hbot := onePlane_matrixPluckerIdeal (K := K) (n := 2*k+1)) d

end PaperVerification.AlternatingForms
