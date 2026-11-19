module

public import Continuation.Runtime.OrdinaryDegreeOneSections
public import Recovery.Unimodular.GraphicSectionRing.GeometricPresentation
public import Recovery.Unimodular.GraphicSectionRing.GeometricGrading

/-!
# Genuine degree-one sections and the graphic polynomial map

These exact proof bodies are separated from the ample embedding machinery
so the actual homogeneous coordinate ring can be checked independently.
They recover genuine degree-one sections from their existing graded sum,
and merely lift variable labels to the scalar field's universe.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PaperVerification.ToricSchemes
open scoped Classical BigOperators BaseSections

namespace PaperVerification.ToricGeometry.SmoothCompleteFan.GraphicCoordinates

open Unimodular.GraphicSectionRing
open Unimodular.GraphicSectionRing.ActualSections

variable {n : ℕ} {F : SmoothCompleteFan n} (G : F.GraphicCoordinates)
  (k : Type u) [Field k] (D : CartierData (F.fanScheme k))

/-- Universe lifting only changes labels; the polynomial map still uses
the original actual section-ring homomorphism. -/
def liftedCartierPolynomialMap :
    MvPolynomial (ULift.{u} (Point (G.constraints
      (F.cartierCoefficients k F.isPure D)))) k →ₐ[k]
        ActualSections.sectionRing k D.localCocycle :=
  (G.cartierPolynomialMap k D).comp (MvPolynomial.rename ULift.down)

theorem liftedCartierPolynomialMap_surjective :
    Function.Surjective (G.liftedCartierPolynomialMap k D) :=
  (G.cartierPolynomialMap_surjective k D).comp
    (MvPolynomial.rename_surjective ULift.down (fun a => ⟨ULift.up a, rfl⟩))

theorem liftedCartierPolynomialMap_homogeneous
    (i : ULift.{u} (Point (G.constraints (F.cartierCoefficients k F.isPure D))))
    (d : ℕ) (hd : d ≠ 1) :
    (G.liftedCartierPolynomialMap k D (MvPolynomial.X i)).val.coeff d = 0 := by
  change (G.cartierPolynomialMap k D
    (MvPolynomial.rename ULift.down (MvPolynomial.X i))).val.coeff d = 0
  rw [MvPolynomial.rename_X, G.cartierPolynomialMap_X]
  exact G.arbitraryGraphicSectionRingEquiv_homogeneous k D
    (degreeOnePoint i.down) 1 d hd

end PaperVerification.ToricGeometry.SmoothCompleteFan.GraphicCoordinates

#print axioms Unimodular.GraphicSectionRing.ActualSections.polynomialDegreeOneSection_single
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.GraphicCoordinates.liftedCartierPolynomialMap_surjective
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.GraphicCoordinates.liftedCartierPolynomialMap_homogeneous

end
