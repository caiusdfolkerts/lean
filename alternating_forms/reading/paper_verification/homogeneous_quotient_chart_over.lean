module

public import PaperVerification.HomogeneousQuotientCharts

/-!
# The homogeneous quotient charts preserve the ground field

The existing chart comparison is a ring equivalence.  Its constant-term
formula proves that the associated scheme chart isomorphism lies over
the canonical map to the spectrum of the ground field.  This keeps the
base field explicit in later birationality statements.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.HomogeneousQuotientCharts

open AlgebraicGeometry CategoryTheory _root_.HomogeneousLocalization MvPolynomial
open PaperVerification.HomogeneousChartDehomogenization

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K ι : Type} [Field K]
  (Q : Ideal (MvPolynomial ι K))
  (hQ : Q.IsHomogeneous (homogeneousSubmodule ι K)) (p : ι)

local notation "P" => MvPolynomial ι K
local notation "𝒜" => HomogeneousQuotientProjective.grading Q hQ

/-- The canonical structure map of the actual homogeneous quotient Proj
to the original coefficient field. -/
def structureMap : Proj 𝒜 ⟶ Spec (CommRingCat.of K) :=
  Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (algebraMap K (𝒜 0)))

include hQ in
theorem awayQuotientChartEquiv_constant (c : K) :
    awayQuotientChartEquiv Q hQ p
      (fromZeroRingHom 𝒜 (Submonoid.powers (Ideal.Quotient.mk Q (X p)))
        (algebraMap K (𝒜 0) c)) =
      algebraMap K (P ⧸ (Q ⊔ Ideal.span {X p-1})) c := by
  let hf := HomogeneousQuotientProjective.quotient_X_mem_one Q hQ p
  have hz : fromZeroRingHom 𝒜 (Submonoid.powers (Ideal.Quotient.mk Q (X p)))
      (algebraMap K (𝒜 0) c) =
      fraction 𝒜 hf 0 (algebraMap K (𝒜 0) c) := by
    apply HomogeneousLocalization.val_injective
    simp only [fromZeroRingHom, HomogeneousLocalization.val_mk,
      fraction_val, pow_zero]
    rfl
  rw [hz, awayQuotientChartEquiv, RingEquiv.trans_apply,
    awayEquivNormalized_fraction]
  change normalizedQuotientEquiv Q p
      (quotientMap (Ideal.Quotient.mk Q (X p)) (Ideal.Quotient.mk Q (C c))) = _
  rw [normalizedQuotientEquiv_class]
  rfl

include hQ in
/-- The normalized chart isomorphism is a morphism over `Spec K`. -/
theorem projectiveBasicOpenIsoNormalized_inv_over :
    (projectiveBasicOpenIsoNormalized Q hQ p).inv ≫
      (Proj.basicOpen 𝒜 (Ideal.Quotient.mk Q (X p))).ι ≫ structureMap Q hQ =
      Spec.map (CommRingCat.ofHom (algebraMap K (P ⧸ (Q ⊔ Ideal.span {X p-1})))) := by
  simp only [projectiveBasicOpenIsoNormalized, structureMap, Iso.trans_inv,
    Functor.mapIso_inv, Iso.op_inv, Scheme.Spec_map, Quiver.Hom.unop_op,
    Category.assoc, Proj.basicOpenIsoSpec_inv_ι_assoc, Proj.awayι_toSpecZero_assoc]
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext c
  exact awayQuotientChartEquiv_constant Q hQ p c

include hQ in
theorem projectiveBasicOpenIsoNormalized_hom_over :
    (projectiveBasicOpenIsoNormalized Q hQ p).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (P ⧸ (Q ⊔ Ideal.span {X p-1})))) =
      (Proj.basicOpen 𝒜 (Ideal.Quotient.mk Q (X p))).ι ≫ structureMap Q hQ := by
  rw [← projectiveBasicOpenIsoNormalized_inv_over Q hQ p,
    Iso.hom_inv_id_assoc]

end PaperVerification.HomogeneousQuotientCharts
