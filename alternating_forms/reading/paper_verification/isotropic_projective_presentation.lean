module

public import PaperVerification.HomogeneousQuotientProjectivePresentation
public import PaperVerification.IsotropicAttractingCanonicalComparison
public import OAI.AlgebraicGeometry.Foundations.Scheme.ClosedProjective

/-!
# The original common-isotropic scheme as a smooth projective presentation

The projective embedding is induced by the original homogeneous quotient,
with its actual scalar structure. Smoothness is transported by the proved
coordinate permutation. No cohomology or Chow hypothesis is part of this data.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.IsotropicAttractingCharts

open AlgebraicGeometry CategoryTheory MvPolynomial
open AlternatingForms IsotropicAttractingCoordinates
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The chain-coordinate model has the original closed projective
embedding, with its structure morphism to the complex numbers. -/
def chainProjectivePresentation (k t : ℕ) (hs : t+2 ≤ k+1) :
    OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation
      (Proj (isotropicProjectiveGrading (t := t)
        (canonicalForms (K := ℂ) (n := 2*k+1) (2*k+1) (2*k))))
      (isotropicStructureMap (canonicalForms (2*k+1) (2*k))) := by
  letI : Nonempty (PluckerIndex (t+2) (2*k+1)) := ⟨oddCoordinatePivot k t hs⟩
  exact HomogeneousQuotientProjective.projectivePresentation
    (isotropicPluckerIdeal (canonicalForms (2*k+1) (2*k)))
    (isotropicPluckerIdeal_isHomogeneous (canonicalForms (2*k+1) (2*k)))

theorem chain_isNoetherian (k t : ℕ) (hs : t+2 ≤ k+1) :
    AlgebraicGeometry.IsNoetherian
      (Proj (isotropicProjectiveGrading (t := t)
        (canonicalForms (K := ℂ) (n := 2*k+1) (2*k+1) (2*k)))) :=
  (chainProjectivePresentation k t hs).isNoetherian

/-- Packaging the proved geometric properties for the standard upstream
intersection and analytic APIs. -/
def chainSmoothProjectivePresentation (k t : ℕ) (hs : t+2 ≤ k+1) :
    OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation where
  carrier := Proj (isotropicProjectiveGrading (t := t)
    (canonicalForms (K := ℂ) (n := 2*k+1) (2*k+1) (2*k)))
  structureMap := isotropicStructureMap _
  projective := chainProjectivePresentation k t hs
  smooth := chainCanonical_isotropicStructureMap_smooth k t

end PaperVerification.IsotropicAttractingCharts
