module

public import PaperVerification.AlternatingFormsPointSections
public import PaperVerification.AlternatingFormsOnePlaneCompleteSectionRing
public import PaperVerification.ProjectiveSectionRing

/-!
# The actual complete Plucker section rings in every odd-pencil size

The target is the external direct sum of the actual global twisting-sheaf
sections on the original homogeneous quotient's projective spectrum.
Its homogeneous product is their literal pointwise product in the
localization rings, and its scalars are the actual constant sections.

The component proofs include every positive size: the one-plane
polynomial boundary, the strict good interval, and the singleton
maximal-size interval.  The resulting algebra isomorphisms are canonical
and send every homogeneous coordinate element r to the section r/1.
The separate chart comparison identifies this actual Proj with the
original common-isotropic atlas.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms

open AlgebraicGeometry MvPolynomial
open PaperVerification.ProjectiveSectionRing

variable {K : Type*} [Field K] [CharZero K]

/-- The canonical scalar-preserving comparison with the actual complete
section ring for every original odd-pencil size at least two. -/
def oddCompleteSectionRingEquiv (k t : ℕ) (hs : t+2≤k+1) :
    (MvPolynomial (PluckerIndex (t+2) (2*k+1)) K ⧸
      isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k)) ≃ₐ[K]
    SectionRing (oddProjectiveGrading (K := K) k t) :=
  completeSectionAlgEquiv (oddProjectiveGrading (K := K) k t)
    (odd_allSizes_bijective_toTwistingSheaf_top k t hs)

/-- Every homogeneous coordinate element retains its original geometric
meaning under the complete-section comparison. -/
theorem oddCompleteSectionRingEquiv_homogeneous (k t : ℕ) (hs : t+2≤k+1)
    (d : ℕ) (r : oddProjectiveGrading (K := K) k t d) :
    oddCompleteSectionRingEquiv (K := K) k t hs r=
      DirectSum.of (fun j ↦ sectionPiece (oddProjectiveGrading (K := K) k t) j) d
        (Proj.toTwistingSheaf (oddProjectiveGrading (K := K) k t)
          (rfl : (d : ℤ)=d) ⊤ r) :=
  canonicalMap_homogeneous (oddProjectiveGrading (K := K) k t) d r

/-- The two displayed comparisons cover exactly all positive sizes in
the paper's odd-pencil range; there is no excluded endpoint. -/
theorem positive_size_cases (k s : ℕ) (hs : 1≤s) (hsk : s≤k+1) :
    s=1 ∨ ∃ t : ℕ,s=t+2 ∧ t+2≤k+1 := by
  by_cases h : s=1
  · exact Or.inl h
  · exact Or.inr ⟨s-2,by omega,by omega⟩

end PaperVerification.AlternatingForms
