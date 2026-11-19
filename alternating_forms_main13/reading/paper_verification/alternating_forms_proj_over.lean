module

public import PaperVerification.AlternatingFormsProjAtlas
public import PaperVerification.HomogeneousQuotientChartOver

/-!
# The ground-field structure map of common-isotropic Proj

The chart identifications commute with the genuine structure map to the
original coefficient field. These lemmas are independent of odd-dimensional
rationality and can also be used for smoothness on the complete chart cover.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open AlgebraicGeometry CategoryTheory MvPolynomial
open scoped AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type} [Field K] [CharZero K]

theorem specAlgEquiv_hom_over
    {R S : Type} [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    (e : R ≃ₐ[K] S) :
    (Scheme.Spec.mapIso e.symm.toRingEquiv.toCommRingCatIso.op).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap K S)) =
      Spec.map (CommRingCat.ofHom (algebraMap K R)) := by
  simp only [Functor.mapIso_hom, Iso.op_hom, Scheme.Spec_map, Quiver.Hom.unop_op]
  rw [← Spec.map_comp]
  congr 1
  ext c
  exact e.symm.commutes c

def isotropicStructureMap {t n m : ℕ} (forms : Fin m → StrictPairs n → K) :
    Proj (isotropicProjectiveGrading (t := t) forms) ⟶ Spec (CommRingCat.of K) :=
  HomogeneousQuotientCharts.structureMap (isotropicPluckerIdeal forms)
    (isotropicPluckerIdeal_isHomogeneous forms)

theorem isotropicProjBasicOpenIso_hom_over {t n m : ℕ}
    (p : PluckerIndex (t+2) n) (forms : Fin m → StrictPairs n → K) :
    (isotropicProjBasicOpenIso p forms).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (IsotropicChartRing p forms))) =
      (Proj.basicOpen (isotropicProjectiveGrading (t := t) forms)
        (Ideal.Quotient.mk (isotropicPluckerIdeal forms) (X p))).ι ≫
          isotropicStructureMap forms := by
  let e₁ := HomogeneousQuotientCharts.projectiveBasicOpenIsoNormalized
    (isotropicPluckerIdeal forms) (isotropicPluckerIdeal_isHomogeneous forms) p
  let e₂ := Scheme.Spec.mapIso (isotropicPluckerBigCellEquiv p forms).symm.toRingEquiv.toCommRingCatIso.op
  exact (Category.assoc e₁.hom e₂.hom _).trans
    ((congrArg (fun f ↦ e₁.hom ≫ f)
      (specAlgEquiv_hom_over (isotropicPluckerBigCellEquiv p forms))).trans
      (HomogeneousQuotientCharts.projectiveBasicOpenIsoNormalized_hom_over
        (isotropicPluckerIdeal forms) (isotropicPluckerIdeal_isHomogeneous forms) p))

end PaperVerification.AlternatingForms
