module

public import PaperVerification.AlternatingFormsIntrinsicChartIdeal
public import PaperVerification.AlternatingFormsAmbientPolarization

/-!
# The intrinsic tautological zero scheme with every Plücker twist

This definition starts from the full image ideals of the alternating
functionals on the actual tautological sections of every ambient chart.
Only after constructing that zero scheme do we compare its ideals with
the original homogeneous quotient and prove the polarized isomorphism.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory

namespace PaperVerification.AlternatingForms

variable {K : Type} [Field K] {t n m : ℕ}

/-- The full actual local image ideal, expressed in polynomial chart coordinates. -/
def ambientIntrinsicPolynomialIdeal (p : PluckerIndex (t + 2) n)
    (forms : Fin m → StrictPairs n → K) :
    Ideal (MvPolynomial (PluckerChartVariable p) K) :=
  (ambientLocalExteriorImageIdeal p forms).comap
    (tautologicalChartPolynomialHom p emptyAlternatingTuple)

theorem ambientIntrinsicPolynomialIdeal_eq (p : PluckerIndex (t + 2) n)
    (forms : Fin m → StrictPairs n → K) :
    ambientIntrinsicPolynomialIdeal p forms = isotropicChartIdeal p forms := by
  rw [ambientIntrinsicPolynomialIdeal, ambientLocalExteriorImageIdeal_eq,
    ambientIntrinsicChartIdeal_eq_map,
    Ideal.comap_map_of_surjective _ (ambientChartPolynomialHom_bijective (K := K) p).surjective,
    ← RingHom.ker_eq_comap_bot,
    (RingHom.injective_iff_ker_eq_bot _).mp (ambientChartPolynomialHom_bijective (K := K) p).injective,
    sup_bot_eq]

def intrinsicChartImageIdeal (p : PluckerIndex (t + 2) n)
    (I : Ideal (MvPolynomial (PluckerChartVariable p) K)) :
    (ambientGrassmannian (K := K) t n).IdealSheafData :=
  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ ambientAffineChartι p).ker

/-- The zero ideal obtained solely from the actual tautological section images. -/
def ambientIntrinsicZeroIdeal (forms : Fin m → StrictPairs n → K) :
    (ambientGrassmannian (K := K) t n).IdealSheafData :=
  ⨅ p : PluckerIndex (t + 2) n,
    intrinsicChartImageIdeal p (ambientIntrinsicPolynomialIdeal p forms)

/-- The intrinsic section images give exactly the independently constructed
polynomial zero scheme, with no change on overlaps. -/
theorem ambientIntrinsicZeroIdeal_eq (forms : Fin m → StrictPairs n → K) :
    ambientIntrinsicZeroIdeal (t := t) forms = ambientSectionZeroIdeal forms := by
  apply iInf_congr
  intro p
  change intrinsicChartImageIdeal p (ambientIntrinsicPolynomialIdeal p forms) =
    intrinsicChartImageIdeal p (isotropicChartSectionFunctional p forms).range
  rw [ambientIntrinsicPolynomialIdeal_eq, isotropicChartSectionFunctional_range]

/-- Identification with the original homogeneous-coordinate closed immersion. -/
theorem ambientIntrinsicZeroIdeal_eq_kernel (forms : Fin m → StrictPairs n → K) :
    ambientIntrinsicZeroIdeal (t := t) forms = (isotropicAmbientImmersion forms).ker :=
  (ambientIntrinsicZeroIdeal_eq forms).trans (ambientSectionZeroIdeal_eq_kernel forms)

abbrev ambientIntrinsicZeroScheme (forms : Fin m → StrictPairs n → K) : Scheme :=
  (ambientIntrinsicZeroIdeal (t := t) forms).subscheme

def isotropicToIntrinsicZero (forms : Fin m → StrictPairs n → K) :
    Proj (isotropicProjectiveGrading (t := t) forms) ⟶ ambientIntrinsicZeroScheme (t := t) forms :=
  IsClosedImmersion.lift (ambientIntrinsicZeroIdeal forms).subschemeι
    (isotropicAmbientImmersion forms) (by
      rw [Scheme.IdealSheafData.ker_subschemeι, ambientIntrinsicZeroIdeal_eq_kernel])

instance isotropicToIntrinsicZero_isIso (forms : Fin m → StrictPairs n → K) :
    IsIso (isotropicToIntrinsicZero (t := t) forms) :=
  IsClosedImmersion.isIso_lift (ambientIntrinsicZeroIdeal forms).subschemeι
    (isotropicAmbientImmersion forms) (by
      rw [Scheme.IdealSheafData.ker_subschemeι, ambientIntrinsicZeroIdeal_eq_kernel])

/-- The original Proj is the zero scheme of the actual ambient tautological section. -/
def isotropicIntrinsicZeroIso (forms : Fin m → StrictPairs n → K) :
    Proj (isotropicProjectiveGrading (t := t) forms) ≅ ambientIntrinsicZeroScheme (t := t) forms :=
  asIso (isotropicToIntrinsicZero forms)

theorem isotropicIntrinsicZeroIso_over_ambient (forms : Fin m → StrictPairs n → K) :
    (isotropicIntrinsicZeroIso (t := t) forms).hom ≫
      (ambientIntrinsicZeroIdeal forms).subschemeι = isotropicAmbientImmersion forms :=
  IsClosedImmersion.lift_fac _ _ _

/-- The actual restricted Plücker twist of any integer degree. -/
def ambientIntrinsicZeroTwist (forms : Fin m → StrictPairs n → K) (r : ℤ) :
    (ambientIntrinsicZeroScheme (t := t) forms).Modules :=
  (Scheme.Modules.pullback (ambientIntrinsicZeroIdeal forms).subschemeι).obj
    (Proj.twistingSheaf (isotropicProjectiveGrading (t := t)
      (emptyAlternatingTuple (K := K) (n := n))) r)

/-- The intrinsic zero-scheme comparison preserves the original Plücker polarization
and every positive, zero, and negative integer twist. -/
def isotropicIntrinsicZeroTwistingIso (forms : Fin m → StrictPairs n → K) (r : ℤ) :
    (Scheme.Modules.pullback (isotropicIntrinsicZeroIso (t := t) forms).hom).obj
        (ambientIntrinsicZeroTwist forms r) ≅
      Proj.twistingSheaf (isotropicProjectiveGrading (t := t) forms) r :=
  (Scheme.Modules.pullbackComp (isotropicIntrinsicZeroIso forms).hom
    (ambientIntrinsicZeroIdeal forms).subschemeι).app _ ≪≫
      eqToIso (congrArg (fun f ↦ (Scheme.Modules.pullback f).obj
        (Proj.twistingSheaf (isotropicProjectiveGrading (t := t)
          (emptyAlternatingTuple (K := K) (n := n))) r))
          (isotropicIntrinsicZeroIso_over_ambient forms)) ≪≫
      isotropicAmbientTwistingPullbackIso forms r

end PaperVerification.AlternatingForms
