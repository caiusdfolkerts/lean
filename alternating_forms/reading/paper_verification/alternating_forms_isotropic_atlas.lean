module

public import PaperVerification.AlternatingFormsProjAtlas
public import PaperVerification.AlternatingFormsOnePlaneSections
public import PaperVerification.HomogeneousIdealChartSystem

/-!
# The original common-isotropic atlas and its genuine Proj transitions

The homogeneous system below generates exactly the original Plucker and
isotropy ideal. Its actual projective scheme is identified with the Proj
used for the complete-section comparison. On every affine chart, the
normalized coordinates represent the original row-isotropic matrices over
every commutative coefficient algebra; each coordinate is proved to be the
corresponding maximal minor. The generic actual-Proj overlap comparison
therefore applies to these literal coordinates, including nilpotents.

The one-plane boundary uses the actual one-row Plucker charts and their
cover. Alternating restrictions on these rows vanish identically.
This source candidate has not yet been compiled.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms

open MvPolynomial Matrix AlgebraicGeometry CategoryTheory

variable {K : Type*} [Field K] [CharZero K] {t n m : ℕ}
  (forms : Fin m → StrictPairs n → K)

/-- Literal homogeneous generators of the entire original isotropy ideal. -/
abbrev isotropicHomogeneousSystem :=
  HomogeneousIdealChartSystem.system
    (isotropicPluckerIdeal (K := K) (t := t) forms)

theorem isotropicHomogeneousSystem_ideal_eq :
    NormalizedHomogeneousProjOverlap.equationIdeal
      (isotropicHomogeneousSystem (t := t) forms)=
      isotropicPluckerIdeal forms :=
  HomogeneousIdealChartSystem.equationIdeal_eq _
    (isotropicPluckerIdeal_isHomogeneous forms)

/-- The system's actual Proj is the original projective scheme; no change
of ideal, radical, saturation, or underlying point set occurs. -/
theorem isotropicHomogeneousSystem_projectiveScheme_eq :
    Proj (NormalizedHomogeneousProjOverlap.grading
      (isotropicHomogeneousSystem (t := t) forms))=
      Proj (isotropicProjectiveGrading (t := t) forms) :=
  HomogeneousIdealChartSystem.projectiveScheme_eq _
    (isotropicPluckerIdeal_isHomogeneous forms)

/-- This equivalence retains the complete original row-isotropy ideal. -/
def normalizedIsotropicChartEquiv (p : PluckerIndex (t+2) n) :
    NormalizedHomogeneousChart.ChartRing (isotropicHomogeneousSystem forms) p ≃ₐ[K]
      IsotropicChartRing p forms :=
  (HomogeneousIdealChartSystem.chartEquiv _
    (isotropicPluckerIdeal_isHomogeneous forms) p).trans
      (isotropicPluckerBigCellEquiv p forms)

@[simp] theorem normalizedIsotropicChartEquiv_class
    (p : PluckerIndex (t+2) n) (a : MvPolynomial (PluckerIndex (t+2) n) K) :
    normalizedIsotropicChartEquiv forms p
      (NormalizedHomogeneousChart.quotientMap (isotropicHomogeneousSystem forms) p a)=
      isotropicChartEvaluation p forms a := by
  have h₀ := HomogeneousIdealChartSystem.chartEquiv_class
    (isotropicPluckerIdeal (K := K) (t := t) forms)
    (isotropicPluckerIdeal_isHomogeneous forms) p a
  have h₁ := Ideal.quotientEquivAlgOfEq_mk K
    (isotropicChartEvaluation_kernel p forms).symm a
  have h₂ := Ideal.quotientKerAlgEquivOfSurjective_mk
    (f := isotropicChartEvaluation p forms)
    (isotropicChartEvaluation_surjective p forms) a
  have hcell : isotropicPluckerBigCellEquiv p forms (Ideal.Quotient.mk _ a)=
      isotropicChartEvaluation p forms a :=
    (congrArg (Ideal.quotientKerAlgEquivOfSurjective
      (f := isotropicChartEvaluation p forms)
      (isotropicChartEvaluation_surjective p forms)) h₁).trans h₂
  exact (congrArg (isotropicPluckerBigCellEquiv p forms) h₀).trans hcell

/-- Universal normalized Plucker points and original isotropic row charts
are equivalent over every commutative test algebra, with no field or
reducedness assumption on that algebra. -/
def normalizedPointEquivIsotropicPoint (p : PluckerIndex (t+2) n)
    (R : Type*) [CommRing R] [Algebra K R] :
    NormalizedHomogeneousChart.ChartPoint (isotropicHomogeneousSystem forms) p R ≃
      IsotropicChartPoint p forms R :=
  (NormalizedHomogeneousChart.chartPointEquiv
    (isotropicHomogeneousSystem forms) p R).trans
    ((AlgEquiv.arrowCongr (normalizedIsotropicChartEquiv forms p)
      (AlgEquiv.refl : R ≃ₐ[K] R)).trans (isotropicChartPointEquiv p forms))

/-- The coordinate interpretation is the actual maximal minor of the
original normalized matrix, not an arbitrary labeling of chart points. -/
theorem normalizedPointEquivIsotropicPoint_minor
    {R : Type*} [CommRing R] [Algebra K R]
    (p I : PluckerIndex (t+2) n) (A : IsotropicChartPoint p forms R) :
    ((normalizedPointEquivIsotropicPoint forms p R).symm A).coordinate I=
      Matrix.det (A.matrix.submatrix id I.val) := by
  change A.toAlgHom (normalizedIsotropicChartEquiv forms p
    (NormalizedHomogeneousChart.quotientMap (isotropicHomogeneousSystem forms) p (X I)))=_
  rw [normalizedIsotropicChartEquiv_class]
  change (A.toAlgHom.comp (Ideal.Quotient.mkₐ K (isotropicChartIdeal p forms)))
    (matrixMinorEvaluation (pluckerChartMatrix p) (X I))=_
  rw [matrixMinorEvaluation,aeval_X,AlgHom.map_det]
  congr 1
  apply Matrix.ext
  intro i j
  change A.toAlgHom (Ideal.Quotient.mk (isotropicChartIdeal p forms)
    (pluckerChartMatrix p i (I.val j)))=A.matrix i (I.val j)
  exact IsotropicChartPoint.toAlgHom_entry A i (I.val j)

/-- The actual restriction of the same Proj scheme is the literal
normalized ratio transition for all coefficient algebras. Combined with
the preceding maximal-minor formula, this is the transition on the original
Plucker coordinates of the common-isotropic row charts. -/
theorem isotropic_actualTransition_on_all_algebra_points
    {R : Type*} [CommRing R] [Algebra K R]
    (p q : PluckerIndex (t+2) n)
    (φ : NormalizedHomogeneousChart.OverlapRing
      (isotropicHomogeneousSystem forms) p q →ₐ[K] R) :
    φ.toRingHom.comp
        (NormalizedHomogeneousProjOverlap.actualTransition
          (isotropicHomogeneousSystem forms) p q)=
      (NormalizedHomogeneousChart.overlapToHom
        (NormalizedHomogeneousChart.homToOverlap φ).transition).toRingHom :=
  NormalizedHomogeneousProjOverlap.actualTransition_on_all_algebra_points
    (isotropicHomogeneousSystem forms) p q φ

/-- The literal one-plane basic open is its original row-coordinate affine
space. This includes ambient dimension one. -/
def onePlaneProjBasicOpenIso (k : ℕ) (p : PluckerIndex 1 (2*k+1)) :
    (Proj.basicOpen (onePlaneProjectiveGrading (K := K) k)
      (Ideal.Quotient.mk matrixPluckerIdeal (X p))).toScheme ≅
      Spec (CommRingCat.of (MvPolynomial (PluckerChartVariable p) K)) :=
  HomogeneousQuotientCharts.projectiveBasicOpenIsoNormalized
      matrixPluckerIdeal (matrixPluckerIdeal_isHomogeneous (by decide : 0<1)) p ≪≫
    Scheme.Spec.mapIso (pluckerBigCellEquiv (K := K) p).symm.toRingEquiv.toCommRingCatIso.op

theorem onePlaneProjBasicOpen_cover (k : ℕ) :
    (⨆ p : PluckerIndex 1 (2*k+1),
      Proj.basicOpen (onePlaneProjectiveGrading (K := K) k)
        (Ideal.Quotient.mk matrixPluckerIdeal (X p)))=⊤ :=
  HomogeneousQuotientProjective.presentation_basicOpen_cover
    matrixPluckerIdeal (matrixPluckerIdeal_isHomogeneous (by decide : 0<1))
    (Ideal.Quotient.mkₐ K matrixPluckerIdeal) Ideal.Quotient.mk_surjective
    (HomogeneousQuotientProjective.quotient_X_mem_one _ _)

end PaperVerification.AlternatingForms
