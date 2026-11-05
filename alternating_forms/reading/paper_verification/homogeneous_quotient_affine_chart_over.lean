module

public import PaperVerification.AlternatingFormsProjOver
public import Mathlib.AlgebraicGeometry.AffineSpace

/-! A normalized polynomial chart is an affine-space chart over the original field. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.HomogeneousQuotientCharts

open AlgebraicGeometry CategoryTheory MvPolynomial
open scoped AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K ι N : Type} [Field K] [CharZero K]
  (Q : Ideal (MvPolynomial ι K))
  (hQ : Q.IsHomogeneous (homogeneousSubmodule ι K)) (p : ι)
  (e : (MvPolynomial ι K ⧸ (Q ⊔ Ideal.span {X p-1})) ≃ₐ[K] MvPolynomial N K)

def polynomialChartIso :
    (Proj.basicOpen (HomogeneousQuotientProjective.grading Q hQ)
      (Ideal.Quotient.mk Q (X p))).toScheme ≅
      𝔸(N; Spec (CommRingCat.of K)) :=
  projectiveBasicOpenIsoNormalized Q hQ p ≪≫
    Scheme.Spec.mapIso e.symm.toRingEquiv.toCommRingCatIso.op ≪≫
    (AffineSpace.SpecIso N (CommRingCat.of K)).symm

theorem polynomialChartIso_hom_over :
    (polynomialChartIso Q hQ p e).hom ≫
      (𝔸(N; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K)) =
      (Proj.basicOpen (HomogeneousQuotientProjective.grading Q hQ)
        (Ideal.Quotient.mk Q (X p))).ι ≫ structureMap Q hQ := by
  simp only [polynomialChartIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, AffineSpace.SpecIso_inv_over]
  have he := AlternatingForms.specAlgEquiv_hom_over e
  simp only [MvPolynomial.algebraMap_eq] at he
  exact (congrArg (fun f ↦ (projectiveBasicOpenIsoNormalized Q hQ p).hom ≫ f) he).trans
    (projectiveBasicOpenIsoNormalized_hom_over Q hQ p)

end PaperVerification.HomogeneousQuotientCharts
