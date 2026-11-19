module

public import PaperVerification.AlternatingFormsChartConverse
public import PaperVerification.AlternatingFormsProjAtlas

/-!
# Characteristic-free common-isotropic chart comparisons

The normalized determinant and row-isotropy identities are integral.  The
older chart wrappers unnecessarily requested `CharZero`.  Here those proofs
are replayed with only a coefficient field, without modifying the accepted
core.  Every quotient retains its original ideal and complete scheme structure.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial Matrix AlgebraicGeometry CategoryTheory

namespace PaperVerification.AlternatingForms

variable {K : Type*} [Field K] {t n m : ℕ}

theorem isotropicPluckerIdeal_map_chart_eq_arbitraryChar
    (p : PluckerIndex (t+2) n) (forms : Fin m → StrictPairs n → K) :
    (isotropicPluckerIdeal forms).map
      (matrixMinorEvaluation (K := K) (pluckerChartMatrix (K := K) p)).toRingHom =
        isotropicChartIdeal p forms := by
  classical
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    intro q hq
    have h := isotropicPluckerIdeal_le_chartKernel p forms hq
    change (Ideal.Quotient.mkₐ K (isotropicChartIdeal p forms))
      (matrixMinorEvaluation (K := K) (pluckerChartMatrix p) q)=0 at h
    change matrixMinorEvaluation (K := K) (pluckerChartMatrix p) q ∈ isotropicChartIdeal p forms
    exact Ideal.Quotient.eq_zero_iff_mem.mp h
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨l,ij⟩,rfl⟩
    obtain ⟨σ,hσ0,hσ1⟩ := exists_chart_row_permutation ij.val.1 ij.val.2
      (ne_of_lt ij.property)
    let J : Fin t → Fin n := fun z ↦ p.val (σ z.succ.succ)
    have hmem :
        matrixMinorEvaluation (K := K) (pluckerChartMatrix (K := K) p)
          (pluckerIsotropyEquation (forms l) J) ∈
          (isotropicPluckerIdeal forms).map
            (matrixMinorEvaluation (K := K) (pluckerChartMatrix p)).toRingHom :=
      Ideal.mem_map_of_mem _
        (Ideal.mem_sup_right (Ideal.subset_span ⟨(l,J),rfl⟩))
    have he := matrixMinorEvaluation_complementary_isotropy (forms l)
      (pluckerChartMatrix (K := K) p) p.val (pluckerChartMatrix_pivot p) σ
    rw [hσ0,hσ1] at he
    change alternatingRowPair (forms l) (pluckerChartMatrix p) ij.val.1 ij.val.2 ∈ _
    rw [←he]
    exact Ideal.mul_mem_left _ _ hmem


theorem isotropicChartEvaluation_kernel_arbitraryChar
    (p : PluckerIndex (t+2) n) (forms : Fin m → StrictPairs n → K) :
    RingHom.ker (isotropicChartEvaluation p forms).toRingHom =
      isotropicPluckerIdeal forms ⊔ Ideal.span {X p-1} := by
  have h := Ideal.comap_map_of_surjective
    (matrixMinorEvaluation (K := K) (pluckerChartMatrix (K := K) p)).toRingHom
    (matrixMinorEvaluation_chart_surjective p) (isotropicPluckerIdeal forms)
  rw [isotropicPluckerIdeal_map_chart_eq_arbitraryChar p forms,
    ←RingHom.ker_eq_comap_bot,matrixMinorEvaluation_chart_kernel] at h
  have hk : RingHom.ker (isotropicChartEvaluation p forms).toRingHom =
      (isotropicChartIdeal p forms).comap
        (matrixMinorEvaluation (K := K) (pluckerChartMatrix p)).toRingHom := by
    ext q
    change (Ideal.Quotient.mkₐ K (isotropicChartIdeal p forms))
      (matrixMinorEvaluation (K := K) (pluckerChartMatrix p) q)=0 ↔ _
    exact Ideal.Quotient.eq_zero_iff_mem
  rw [hk,h,pluckerBigCellIdeal]
  have hle : matrixPluckerIdeal (K := K) (s := t+2) (n := n) ≤
      isotropicPluckerIdeal (t := t) forms := le_sup_left
  rw [←sup_assoc,sup_of_le_left hle]

/-- The actual normalized Plücker quotient is the affine scheme chart cut out
by the pairwise row restrictions. Both quotient ideals are stated literally. -/
def isotropicPluckerBigCellEquiv_arbitraryChar
    (p : PluckerIndex (t+2) n) (forms : Fin m → StrictPairs n → K) :
    (MvPolynomial (PluckerIndex (t+2) n) K ⧸
      (isotropicPluckerIdeal forms ⊔ Ideal.span {X p-1})) ≃ₐ[K]
      (MvPolynomial (PluckerChartVariable p) K ⧸ isotropicChartIdeal p forms) :=
  (Ideal.quotientEquivAlgOfEq K (isotropicChartEvaluation_kernel_arbitraryChar p forms).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (isotropicChartEvaluation_surjective p forms))


def isotropicProjChartRingEquiv_arbitraryChar (p : PluckerIndex (t+2) n)
    (forms : Fin m → StrictPairs n → K) :
    HomogeneousLocalization.Away (isotropicProjectiveGrading (t := t) forms)
      (Ideal.Quotient.mk (isotropicPluckerIdeal forms) (X p)) ≃+*
      IsotropicChartRing p forms :=
  (HomogeneousQuotientCharts.awayQuotientChartEquiv
    (isotropicPluckerIdeal forms) (isotropicPluckerIdeal_isHomogeneous forms) p).trans
    (isotropicPluckerBigCellEquiv_arbitraryChar p forms).toRingEquiv

/-- The literal open subscheme of the actual homogeneous quotient's
Proj is the spectrum of the original affine row-restriction equations. -/
def isotropicProjBasicOpenIso_arbitraryChar (p : PluckerIndex (t+2) n)
    (forms : Fin m → StrictPairs n → K) :
    (Proj.basicOpen (isotropicProjectiveGrading (t := t) forms)
      (Ideal.Quotient.mk (isotropicPluckerIdeal forms) (X p))).toScheme ≅
      Spec (CommRingCat.of (IsotropicChartRing p forms)) :=
  HomogeneousQuotientCharts.projectiveBasicOpenIsoNormalized
      (isotropicPluckerIdeal forms) (isotropicPluckerIdeal_isHomogeneous forms) p ≪≫
    Scheme.Spec.mapIso (isotropicPluckerBigCellEquiv_arbitraryChar p forms).symm.toRingEquiv.toCommRingCatIso.op

/-- The original Plücker charts cover in every characteristic. -/
theorem isotropicProjBasicOpen_cover_arbitraryChar
    (forms : Fin m → StrictPairs n → K) :
    (⨆ p : PluckerIndex (t+2) n,
      Proj.basicOpen (isotropicProjectiveGrading (t := t) forms)
        (Ideal.Quotient.mk (isotropicPluckerIdeal forms) (X p))) = ⊤ :=
  HomogeneousQuotientProjective.presentation_basicOpen_cover
    (isotropicPluckerIdeal forms) (isotropicPluckerIdeal_isHomogeneous forms)
    (Ideal.Quotient.mkₐ K (isotropicPluckerIdeal forms))
    Ideal.Quotient.mk_surjective
    (HomogeneousQuotientProjective.quotient_X_mem_one _ _)


end PaperVerification.AlternatingForms
