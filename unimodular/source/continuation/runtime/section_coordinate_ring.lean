module

public import Continuation.Runtime.SectionPresentation
public import Continuation.Runtime.OrdinarySectionCoordinateRing
public import Continuation.Runtime.SectionRingNormality
public import Continuation.Runtime.FanNormalStalks

/-!
# The actual coordinate map and its normal homogeneous quotient

The polynomial evaluation below is defined directly from the supplied
degree-one sections and ordinary section multiplication. The graphic
presentation is proved equal to this map. Its quotient therefore is the
genuine homogeneous coordinate ring for the section embedding once the
separate pullback-O(1) comparison has identified its coordinate sections.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricSchemes
open scoped BaseSections


namespace PaperVerification.ToricGeometry.SmoothCompleteFan.GraphicCoordinates

open Unimodular.GraphicSectionRing
open Unimodular.GraphicSectionRing.ActualSections

variable {n : ℕ} {F : SmoothCompleteFan n} (G : F.GraphicCoordinates)
  (k : Type u) [Field k] (D : CartierData (F.fanScheme k))

theorem liftedCartierPolynomialMap_eq_actualCoordinateMap :
    degreeOneSectionMap k D.localCocycle
      (polynomialDegreeOneSection k D.localCocycle (G.liftedCartierPolynomialMap k D)) =
        G.liftedCartierPolynomialMap k D :=
  degreeOneSectionMap_eq k D.localCocycle (G.liftedCartierPolynomialMap k D)
    (G.liftedCartierPolynomialMap_homogeneous k D)

/-- The actual coordinate quotient is normal: normality of all original
fan-scheme local rings gives normality of the full ordinary section ring,
and actual degree-one generation identifies the two rings. -/
theorem actualCoordinateRing_isIntegrallyClosed :
    IsIntegrallyClosed (sectionCoordinateRing k D.localCocycle
      (polynomialDegreeOneSection k D.localCocycle (G.liftedCartierPolynomialMap k D))) := by
  letI : IsIntegrallyClosed (sectionRing k D.localCocycle) :=
    sectionRing_isIntegrallyClosed k D.localCocycle
      (Unimodular.NefBig.fanScheme_stalk_isIntegrallyClosed F k)
  have hsurj : Function.Surjective (degreeOneSectionMap k D.localCocycle
      (polynomialDegreeOneSection k D.localCocycle (G.liftedCartierPolynomialMap k D))) := by
    rw [G.liftedCartierPolynomialMap_eq_actualCoordinateMap k D]
    exact G.liftedCartierPolynomialMap_surjective k D
  exact IsIntegrallyClosed.of_equiv
    (Ideal.quotientKerAlgEquivOfSurjective hsurj).symm.toRingEquiv

/-- The same genuine quotient is a nonzero domain, through its injective
identification with the ordinary section ring inside the function-field
polynomial ring. -/
theorem actualCoordinateRing_isDomain :
    IsDomain (sectionCoordinateRing k D.localCocycle
      (polynomialDegreeOneSection k D.localCocycle (G.liftedCartierPolynomialMap k D))) := by
  have hsurj : Function.Surjective (degreeOneSectionMap k D.localCocycle
      (polynomialDegreeOneSection k D.localCocycle (G.liftedCartierPolynomialMap k D))) := by
    rw [G.liftedCartierPolynomialMap_eq_actualCoordinateMap k D]
    exact G.liftedCartierPolynomialMap_surjective k D
  let e := Ideal.quotientKerAlgEquivOfSurjective hsurj
  exact Function.Injective.isDomain e.toRingHom e.injective

/-- The normal-domain assertion includes nontriviality explicitly. -/
theorem actualCoordinateRing_normal_domain :
    IsDomain (sectionCoordinateRing k D.localCocycle
      (polynomialDegreeOneSection k D.localCocycle (G.liftedCartierPolynomialMap k D))) ∧
    IsIntegrallyClosed (sectionCoordinateRing k D.localCocycle
      (polynomialDegreeOneSection k D.localCocycle (G.liftedCartierPolynomialMap k D))) :=
  ⟨G.actualCoordinateRing_isDomain k D, G.actualCoordinateRing_isIntegrallyClosed k D⟩

end PaperVerification.ToricGeometry.SmoothCompleteFan.GraphicCoordinates

#print axioms Unimodular.GraphicSectionRing.ActualSections.degreeOneSectionMap_eq
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.GraphicCoordinates.actualCoordinateRing_isIntegrallyClosed
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.GraphicCoordinates.actualCoordinateRing_normal_domain

end
