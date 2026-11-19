module

public import PaperVerification.AlternatingFormsAmbientCharts
public import PaperVerification.AlternatingFormsSectionEquationIdeal
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# The independent zero scheme of the alternating section

On each polynomial Grassmannian chart, take the genuine image ideal of the
finite family of alternating functionals on the normalized tautological
frame.  Map its affine zero scheme into the ambient Grassmannian and glue
its ideal sheaves by their intersection.  This definition involves only
the ambient Grassmannian and the given forms; it does not refer to the
common-isotropic projective scheme or its defining homogeneous ideal.

The exact commuting chart maps prove that this ideal sheaf equals the
closed-image ideal of the original projective scheme.  Consequently the
comparison is an isomorphism over the ambient Grassmannian, retaining the
entire scheme structure.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace PaperVerification.AlternatingForms

variable {K : Type} [Field K] {t n m : ℕ}

/-- The zero ideal of the actual alternating functional on a polynomial
Grassmannian chart, before any isotropy equations have been imposed. -/
def ambientSectionChartIdeal (p : PluckerIndex (t + 2) n)
    (forms : Fin m → StrictPairs n → K) :
    Ideal (MvPolynomial (PluckerChartVariable p) K) :=
  LinearMap.range (isotropicChartSectionFunctional p forms)

/-- The independently defined local zero scheme in the ambient Grassmannian. -/
def ambientSectionChartZeroMap (p : PluckerIndex (t + 2) n)
    (forms : Fin m → StrictPairs n → K) :
    Spec (CommRingCat.of
      (MvPolynomial (PluckerChartVariable p) K ⧸ ambientSectionChartIdeal p forms)) ⟶
      ambientGrassmannian (K := K) t n :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (ambientSectionChartIdeal p forms))) ≫
    ambientAffineChartι p

/-- The ideal sheaf obtained from the actual local section zero schemes. -/
def ambientSectionZeroIdeal (forms : Fin m → StrictPairs n → K) :
    (ambientGrassmannian (K := K) t n).IdealSheafData :=
  ⨅ p : PluckerIndex (t + 2) n, (ambientSectionChartZeroMap p forms).ker

/-- The actual closed subscheme determined by the section's local zero ideals. -/
def ambientSectionZeroScheme (forms : Fin m → StrictPairs n → K) : Scheme :=
  (ambientSectionZeroIdeal (t := t) forms).subscheme

/-- The image ideal of an arbitrary affine-chart quotient.  Keeping the ideal
as an explicit argument makes equality transport independent of the quotient
ring's inferred two-sidedness witness. -/
private def chartQuotientImageIdeal (p : PluckerIndex (t + 2) n)
    (I : Ideal (MvPolynomial (PluckerChartVariable p) K)) :
    (ambientGrassmannian (K := K) t n).IdealSheafData :=
  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ ambientAffineChartι p).ker

private def affineQuotientImageIdeal (p : PluckerIndex (t + 2) n)
    (I : Ideal (MvPolynomial (PluckerChartVariable p) K)) :
    (Spec (CommRingCat.of (MvPolynomial (PluckerChartVariable p) K))).IdealSheafData :=
  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker

/-- The independent section zero ideal agrees with the closed-image ideal
of the paper's original homogeneous quotient. -/
theorem ambientSectionZeroIdeal_eq_kernel (forms : Fin m → StrictPairs n → K) :
    ambientSectionZeroIdeal (t := t) forms = (isotropicAmbientImmersion forms).ker := by
  calc
    ambientSectionZeroIdeal forms =
        ⨅ p : PluckerIndex (t + 2) n,
          (isotropicAffineChartι p forms ≫ isotropicAmbientImmersion forms).ker := by
      apply iInf_congr
      intro p
      change chartQuotientImageIdeal p (isotropicChartSectionFunctional p forms).range = _
      rw [isotropicChartSectionFunctional_range]
      exact congrArg Scheme.Hom.ker (isotropicAffineChart_ambient_commutes p forms).symm
    _ = (isotropicAmbientImmersion forms).ker :=
      (isotropicAmbientImmersion forms).iInf_ker_openCover_map_comp
        (isotropicAffineChartCover forms).openCover

/-- The globally constructed ideal restricts to exactly the functional's
local zero ideal on every ambient chart.  Thus the intersection definition
introduces neither extra equations nor extra points on chart overlaps. -/
theorem ambientSectionZeroIdeal_chart (p : PluckerIndex (t + 2) n)
    (forms : Fin m → StrictPairs n → K) :
    (ambientSectionZeroIdeal forms).comap (ambientAffineChartι p) =
      (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (ambientSectionChartIdeal p forms)))).ker := by
  rw [ambientSectionZeroIdeal_eq_kernel]
  change (isotropicAmbientImmersion forms).ker.comap (ambientAffineChartι p) =
    affineQuotientImageIdeal p (isotropicChartSectionFunctional p forms).range
  rw [isotropicChartSectionFunctional_range]
  ext1
  funext W
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  exact (Scheme.ker_ideal_of_isPullback_of_isOpenImmersion
    (isotropicAmbientImmersion forms)
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (isotropicChartIdeal p forms))))
    (isotropicAffineChartι p forms) (ambientAffineChartι p)
    (isotropicAffineChart_ambient_isPullback p forms) W).symm

/-- The canonical morphism from the original X to the independently
constructed section zero scheme. -/
def isotropicToSectionZero (forms : Fin m → StrictPairs n → K) :
    Proj (isotropicProjectiveGrading (t := t) forms) ⟶
      ambientSectionZeroScheme (t := t) forms :=
  IsClosedImmersion.lift (ambientSectionZeroIdeal forms).subschemeι
    (isotropicAmbientImmersion forms) (by
      rw [Scheme.IdealSheafData.ker_subschemeι, ambientSectionZeroIdeal_eq_kernel])

instance isotropicToSectionZero_isIso (forms : Fin m → StrictPairs n → K) :
    IsIso (isotropicToSectionZero (t := t) forms) :=
  IsClosedImmersion.isIso_lift (ambientSectionZeroIdeal forms).subschemeι
    (isotropicAmbientImmersion forms) (by
      rw [Scheme.IdealSheafData.ker_subschemeι, ambientSectionZeroIdeal_eq_kernel])

/-- A genuine scheme isomorphism from the original homogeneous quotient
to the zero scheme of the independently defined local section functionals. -/
def isotropicSectionZeroIso (forms : Fin m → StrictPairs n → K) :
    Proj (isotropicProjectiveGrading (t := t) forms) ≅ ambientSectionZeroScheme (t := t) forms :=
  asIso (isotropicToSectionZero forms)

/-- The scheme comparison preserves the actual embedding into the Grassmannian. -/
theorem isotropicSectionZeroIso_over_ambient (forms : Fin m → StrictPairs n → K) :
    (isotropicSectionZeroIso (t := t) forms).hom ≫
        (ambientSectionZeroIdeal forms).subschemeι =
      isotropicAmbientImmersion forms :=
  IsClosedImmersion.lift_fac _ _ _

end PaperVerification.AlternatingForms
