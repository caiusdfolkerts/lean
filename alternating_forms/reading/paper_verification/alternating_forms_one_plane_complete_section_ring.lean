module

public import PaperVerification.AlternatingFormsOnePlaneSections
public import PaperVerification.ProjectiveSectionRing

/-!
# Complete section algebra of the one-plane Plucker quotient

The polynomial boundary is treated independently of the higher-plane
argument. The target is the actual graded algebra of global twisting-sheaf
sections, with its original multiplication and its canonical degree maps.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms

open AlgebraicGeometry MvPolynomial
open PaperVerification.ProjectiveSectionRing

variable {K : Type*} [Field K] [CharZero K]

/-- The same canonical comparison in the one-plane boundary, including
ambient dimension one and all nonnegative section degrees. -/
def onePlaneCompleteSectionRingEquiv (k : ℕ) :
    (MvPolynomial (PluckerIndex 1 (2*k+1)) K ⧸ matrixPluckerIdeal) ≃ₐ[K]
    SectionRing (onePlaneProjectiveGrading (K := K) k) :=
  completeSectionAlgEquiv (onePlaneProjectiveGrading (K := K) k)
    (onePlane_bijective_toTwistingSheaf_top k)

theorem onePlaneCompleteSectionRingEquiv_homogeneous (k d : ℕ)
    (r : onePlaneProjectiveGrading (K := K) k d) :
    onePlaneCompleteSectionRingEquiv (K := K) k r=
      DirectSum.of (fun j ↦ sectionPiece (onePlaneProjectiveGrading (K := K) k) j) d
        (Proj.toTwistingSheaf (onePlaneProjectiveGrading (K := K) k)
          (rfl : (d : ℤ)=d) ⊤ r) :=
  canonicalMap_homogeneous (onePlaneProjectiveGrading (K := K) k) d r

end PaperVerification.AlternatingForms
