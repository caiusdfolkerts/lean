module

public import PaperVerification.AlternatingFormsSectionZeroScheme
public import PaperVerification.TwistingSheafPullback

/-!
# The polarization in the ambient zero-scheme comparison

The original Proj twisting sheaf is the pullback of the ambient twisting
sheaf under the actual graded quotient map.  The zero-scheme isomorphism
therefore respects every integer Plücker twist, including the polarization.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace PaperVerification.AlternatingForms

variable {K : Type} [Field K] {t n m : ℕ}

/-- Every original Proj twist is the restriction of the ambient Plücker twist. -/
def isotropicAmbientTwistingPullbackIso (forms : Fin m → StrictPairs n → K) (r : ℤ) :
    (Scheme.Modules.pullback (isotropicAmbientImmersion (t := t) forms)).obj
        (Proj.twistingSheaf (isotropicProjectiveGrading (t := t)
          (emptyAlternatingTuple (K := K) (n := n))) r) ≅
      Proj.twistingSheaf (isotropicProjectiveGrading (t := t) forms) r :=
  TwistingSheafMap.pullbackIso_of_degreeOne_cover (ambientGradedQuotient forms)
    (irrelevant_le_map_of_gradedSurjective _
      (HomogeneousQuotientProjective.quotientGradedHom_surjective _ _ _ _ _))
    (fun p : PluckerIndex (t + 2) n ↦ Ideal.Quotient.mk _ (X p))
    (HomogeneousQuotientProjective.quotient_X_mem_one _ _)
    (isotropicProjBasicOpen_cover_arbitraryChar emptyAlternatingTuple) r

/-- The usual Plücker twist on the independently constructed zero scheme. -/
def ambientSectionZeroTwist (forms : Fin m → StrictPairs n → K) (r : ℤ) :
    (ambientSectionZeroScheme (t := t) forms).Modules :=
  (Scheme.Modules.pullback (ambientSectionZeroIdeal forms).subschemeι).obj
    (Proj.twistingSheaf (isotropicProjectiveGrading (t := t)
      (emptyAlternatingTuple (K := K) (n := n))) r)

/-- The comparison of schemes is a comparison of their actual Plücker twists. -/
def isotropicSectionZeroTwistingIso (forms : Fin m → StrictPairs n → K) (r : ℤ) :
    (Scheme.Modules.pullback (isotropicSectionZeroIso (t := t) forms).hom).obj
        (ambientSectionZeroTwist forms r) ≅
      Proj.twistingSheaf (isotropicProjectiveGrading (t := t) forms) r :=
  (Scheme.Modules.pullbackComp (isotropicSectionZeroIso forms).hom
    (ambientSectionZeroIdeal forms).subschemeι).app _ ≪≫
      eqToIso (congrArg (fun f ↦ (Scheme.Modules.pullback f).obj
        (Proj.twistingSheaf (isotropicProjectiveGrading (t := t)
          (emptyAlternatingTuple (K := K) (n := n))) r))
          (isotropicSectionZeroIso_over_ambient forms)) ≪≫
      isotropicAmbientTwistingPullbackIso forms r

end PaperVerification.AlternatingForms
