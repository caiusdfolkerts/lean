module

public import PaperVerification.RichardsonSchemeComparison
public import PaperVerification.TwistingSheafPullback

/-!
# Every Plücker twist in the Richardson scheme comparison

The isomorphism of the original interval Proj with the independent
opposite-flag rank scheme is over the ambient Grassmannian and preserves
its actual projective polarization, including all integer twists.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace PaperVerification.AlternatingForms

variable {K : Type} [Field K] {t n : ℕ}

def richardsonAmbientTwistingPullbackIso
    (α β : Fin (t + 2) → Fin n) (r : ℤ) :
    (Scheme.Modules.pullback (richardsonAmbientImmersion (K := K) α β)).obj
        (Proj.twistingSheaf (isotropicProjectiveGrading (t := t)
          (emptyAlternatingTuple (K := K) (n := n))) r) ≅
      Proj.twistingSheaf (richardsonProjectiveGrading α β) r :=
  TwistingSheafMap.pullbackIso_of_degreeOne_cover (richardsonAmbientGradedQuotient α β)
    (irrelevant_le_map_of_gradedSurjective _
      (HomogeneousQuotientProjective.quotientGradedHom_surjective _ _ _ _ _))
    (fun p : PluckerIndex (t + 2) n ↦ Ideal.Quotient.mk _ (X p))
    (HomogeneousQuotientProjective.quotient_X_mem_one _ _)
    (isotropicProjBasicOpen_cover_arbitraryChar emptyAlternatingTuple) r

/-- The actual restricted Plücker twist on the independent rank scheme. -/
def richardsonRankZeroTwist (α β : Fin (t + 2) → Fin n) (r : ℤ) :
    (richardsonRankZeroScheme (K := K) α β).Modules :=
  (Scheme.Modules.pullback (richardsonRankZeroIdeal α β).subschemeι).obj
    (Proj.twistingSheaf (isotropicProjectiveGrading (t := t)
      (emptyAlternatingTuple (K := K) (n := n))) r)

/-- Exact preservation of each integer twist under the proved scheme isomorphism. -/
def richardsonRankZeroTwistingIso (α β : Fin (t + 2) → Fin n) (r : ℤ) :
    (Scheme.Modules.pullback (richardsonRankZeroIso (K := K) α β).hom).obj
        (richardsonRankZeroTwist α β r) ≅
      Proj.twistingSheaf (richardsonProjectiveGrading α β) r :=
  (Scheme.Modules.pullbackComp (richardsonRankZeroIso α β).hom
    (richardsonRankZeroIdeal α β).subschemeι).app _ ≪≫
      eqToIso (congrArg (fun f ↦ (Scheme.Modules.pullback f).obj
        (Proj.twistingSheaf (isotropicProjectiveGrading (t := t)
          (emptyAlternatingTuple (K := K) (n := n))) r))
          (richardsonRankZeroIso_over_ambient α β)) ≪≫
      richardsonAmbientTwistingPullbackIso α β r

end PaperVerification.AlternatingForms
