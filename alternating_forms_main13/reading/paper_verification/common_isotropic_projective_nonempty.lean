module

public import PaperVerification.CommonIsotropicChartPoints
public import PaperVerification.AlternatingFormsProjAtlas

/-!
# Nonemptiness of the actual common-isotropic projective scheme

The point is obtained from the field-valued point of an original affine chart
and transported through the proved isomorphism to an actual basic open of Proj.
-/

@[expose] public section
noncomputable section
open AlgebraicGeometry CategoryTheory

namespace PaperVerification.AlternatingForms
variable {K : Type*} [Field K] [CharZero K] {t n : ℕ}

/-- The actual projective zero scheme is nonempty for every pair in the full
numerically allowed range. This strengthens the nonemptiness part of Theorem1.2. -/
theorem commonIsotropicProj_nonempty
    (forms : Fin 2 → StrictPairs n → K) (hs : t + 2 ≤ (n + 1) / 2) :
    Nonempty (Proj (isotropicProjectiveGrading (t := t) forms)) := by
  obtain ⟨p, ⟨A⟩⟩ := exists_common_isotropic_chartPoint (by exact two_ne_zero) forms hs
  let x : PrimeSpectrum K := ⟨⊥, inferInstance⟩
  let y : PrimeSpectrum (IsotropicChartRing p forms) :=
    PrimeSpectrum.comap A.toAlgHom.toRingHom x
  exact ⟨((isotropicProjBasicOpenIso p forms).inv y).val⟩

/-- The usual numerical nonemptiness range, without a division in its hypothesis. -/
theorem commonIsotropicProj_nonempty_of_dimension
    (forms : Fin 2 → StrictPairs n → K) (hs : 2 * (t + 2) ≤ n + 1) :
    Nonempty (Proj (isotropicProjectiveGrading (t := t) forms)) :=
  commonIsotropicProj_nonempty forms (by omega)

/-- The original one-plane Plücker grading in arbitrary ambient dimension. -/
def onePlaneOriginalGrading (n : ℕ) :=
  HomogeneousQuotientProjective.grading
    (matrixPluckerIdeal (K := K) (s := 1) (n := n))
    (matrixPluckerIdeal_isHomogeneous (by decide : 0 < 1))

instance onePlaneOriginalGradedAlgebra (n : ℕ) :
    GradedAlgebra (onePlaneOriginalGrading (K := K) n) :=
  HomogeneousQuotientProjective.quotientGradedAlgebra _ _

/-- The one-plane boundary is nonempty in every positive ambient dimension. -/
theorem onePlaneOriginalProj_nonempty (n : ℕ) (hn : 0 < n) :
    Nonempty (Proj (onePlaneOriginalGrading (K := K) n)) := by
  let p : PluckerIndex 1 n := ⟨fun _ ↦ ⟨0, hn⟩, by
    intro i j hij
    have h : i = j := Subsingleton.elim _ _
    subst j
    exact ((lt_irrefl i) hij).elim⟩
  let e := HomogeneousQuotientCharts.projectiveBasicOpenIsoNormalized
      (matrixPluckerIdeal (K := K) (s := 1) (n := n))
      (matrixPluckerIdeal_isHomogeneous (by decide : 0 < 1)) p ≪≫
    Scheme.Spec.mapIso (pluckerBigCellEquiv (K := K) p).symm.toRingEquiv.toCommRingCatIso.op
  let φ : MvPolynomial (PluckerChartVariable p) K →ₐ[K] K :=
    MvPolynomial.aeval (fun _ ↦ 0)
  let y : PrimeSpectrum (MvPolynomial (PluckerChartVariable p) K) :=
    PrimeSpectrum.comap φ.toRingHom ⟨⊥, inferInstance⟩
  exact ⟨(e.inv y).val⟩

end PaperVerification.AlternatingForms
