module

public import PaperVerification.HomogeneousQuotientCharts
public import PaperVerification.AlternatingFormsChartUniversal
public import PaperVerification.AlternatingFormsPluckerHomogeneity

/-!
# The actual common-isotropic Proj has the original row-isotropy charts

The homogeneous quotient's actual basic open subschemes are the spectra
of the full original row-isotropy ideals.  The previously constructed
universal chart point equivalence therefore describes every affine
chart over every commutative coefficient algebra, including nilpotents.
Together with the explicit normalized-coordinate transition cocycles
this identifies the original common-isotropic atlas with the actual
Proj used in the complete-section comparison.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms

open MvPolynomial AlgebraicGeometry CategoryTheory

variable {K : Type*} [Field K] [CharZero K] {t n m : ℕ}

/-- The actual original quotient grading for arbitrary collections of
alternating forms, without any genericity hypothesis. -/
def isotropicProjectiveGrading (forms : Fin m → StrictPairs n → K) :
    ℕ → Submodule K
      (MvPolynomial (PluckerIndex (t+2) n) K ⧸ isotropicPluckerIdeal forms) :=
  HomogeneousQuotientProjective.grading (isotropicPluckerIdeal forms)
    (isotropicPluckerIdeal_isHomogeneous forms)

instance isotropicProjectiveGradedAlgebra
    (forms : Fin m → StrictPairs n → K) :
    GradedAlgebra (isotropicProjectiveGrading (t := t) forms) :=
  HomogeneousQuotientProjective.quotientGradedAlgebra _ _

/-- The actual degree-zero localization is the original affine
row-isotropy ring, with no reduction of either ideal. -/
def isotropicProjChartRingEquiv (p : PluckerIndex (t+2) n)
    (forms : Fin m → StrictPairs n → K) :
    HomogeneousLocalization.Away (isotropicProjectiveGrading (t := t) forms)
      (Ideal.Quotient.mk (isotropicPluckerIdeal forms) (X p)) ≃+*
      IsotropicChartRing p forms :=
  (HomogeneousQuotientCharts.awayQuotientChartEquiv
    (isotropicPluckerIdeal forms) (isotropicPluckerIdeal_isHomogeneous forms) p).trans
    (isotropicPluckerBigCellEquiv p forms).toRingEquiv

/-- The literal open subscheme of the actual homogeneous quotient's
Proj is the spectrum of the original affine row-restriction equations. -/
def isotropicProjBasicOpenIso (p : PluckerIndex (t+2) n)
    (forms : Fin m → StrictPairs n → K) :
    (Proj.basicOpen (isotropicProjectiveGrading (t := t) forms)
      (Ideal.Quotient.mk (isotropicPluckerIdeal forms) (X p))).toScheme ≅
      Spec (CommRingCat.of (IsotropicChartRing p forms)) :=
  HomogeneousQuotientCharts.projectiveBasicOpenIsoNormalized
      (isotropicPluckerIdeal forms) (isotropicPluckerIdeal_isHomogeneous forms) p ≪≫
    Scheme.Spec.mapIso (isotropicPluckerBigCellEquiv p forms).symm.toRingEquiv.toCommRingCatIso.op

/-- These are actual covering basic opens of the same projective scheme. -/
theorem isotropicProjBasicOpen_cover
    (forms : Fin m → StrictPairs n → K) :
    (⨆ p : PluckerIndex (t+2) n,
      Proj.basicOpen (isotropicProjectiveGrading (t := t) forms)
        (Ideal.Quotient.mk (isotropicPluckerIdeal forms) (X p)))=⊤ :=
  HomogeneousQuotientProjective.presentation_basicOpen_cover
    (isotropicPluckerIdeal forms) (isotropicPluckerIdeal_isHomogeneous forms)
    (Ideal.Quotient.mkₐ K (isotropicPluckerIdeal forms))
    Ideal.Quotient.mk_surjective
    (HomogeneousQuotientProjective.quotient_X_mem_one _ _)

end PaperVerification.AlternatingForms
