module

public import Continuation.Runtime.AmpleDegreeOneFoundations
public import Continuation.Runtime.PolynomialSectionDegree
public import Continuation.Runtime.OrdinaryHomogeneousGeneration
public import Continuation.Runtime.SectionPresentation
public import Recovery.Unimodular.GraphicSectionRing.GeometricPresentation
public import Recovery.Unimodular.GraphicSectionRing.GeometricGrading

/-!
# Homogeneous generation by the genuine degree-one sections

Surjectivity of the ordinary section-ring presentation is converted into
homogeneous polynomial expressions in each tensor power. The degree-one
variables are recovered as actual sections, and the coefficient calculation
proves that no auxiliary grading is being substituted.

The final theorem constructs the actual degree-one morphism for every
ordinary ample invertible sheaf on the original graphic fan scheme. Closed
immersion and the pullback of O(1) are proved in the subsequent modules.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PaperVerification.ToricSchemes
open scoped Classical BigOperators BaseSections

namespace PaperVerification.ToricGeometry.SmoothCompleteFan.GraphicCoordinates

open Unimodular.GraphicSectionRing
open Unimodular.GraphicSectionRing.ActualSections

variable {n : ℕ} {F : SmoothCompleteFan n} (G : F.GraphicCoordinates)
  (k : Type u) [Field k] (D : CartierData (F.fanScheme k))

/-- The original graphic section-ring proof yields polynomial expressions
in every genuine tensor power of every input Cartier sheaf. -/
theorem cartier_homogeneous_generation (N : ℕ)
    (t : Γ((D.localCocycle.pow N).sheaf, ⊤)) :
    ∃ p : MvPolynomial (ULift.{u} (Point (G.constraints
      (F.cartierCoefficients k F.isPure D)))) k,
      p.IsHomogeneous N ∧
      D.localCocycle.sectionProjectiveFieldMap k
        (polynomialDegreeOneSection k D.localCocycle
          (G.liftedCartierPolynomialMap k D)) p =
        (D.localCocycle.pow N).toCartierData.sectionValue ⊤ t :=
  homogeneous_generation_of_surjective k D.localCocycle
    (G.liftedCartierPolynomialMap k D)
    (G.liftedCartierPolynomialMap_surjective k D)
    (G.liftedCartierPolynomialMap_homogeneous k D) N t

/-- Degree-one sections of any ordinary ample invertible sheaf generate it
on the original fan scheme. No invariant representative is assumed as input. -/
theorem ordinary_ample_degreeOne_cover
    (M : (F.fanScheme k).Modules) (hM : IsInvertibleModule M)
    (hample : Unimodular.NefBig.IsAmpleModule M) :
    let D := invertibleFractionalPresentation M hM
    let s := polynomialDegreeOneSection k D.localCocycle
      (G.liftedCartierPolynomialMap k D)
    (⨆ i, D.localCocycle.nonvanishingOpen (s i)) = ⊤ := by
  let D := invertibleFractionalPresentation M hM
  have hC : Unimodular.NefBig.IsAmpleModule D.localCocycle.sheaf :=
    Unimodular.NefBig.isAmpleModule_of_iso D.presentationIso hample
  exact D.localCocycle.nonvanishing_cover_of_homogeneous_generation k
    (polynomialDegreeOneSection k D.localCocycle (G.liftedCartierPolynomialMap k D))
    hC (G.cartier_homogeneous_generation k D)

end PaperVerification.ToricGeometry.SmoothCompleteFan.GraphicCoordinates

#print axioms Unimodular.GraphicSectionRing.ActualSections.degreeOnePolynomialEvaluation_coefficient
#print axioms Unimodular.GraphicSectionRing.ActualSections.homogeneous_generation_of_surjective
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.GraphicCoordinates.cartier_homogeneous_generation
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.GraphicCoordinates.ordinary_ample_degreeOne_cover

end
