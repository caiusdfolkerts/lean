module

public import PaperVerification.HomogeneousChartDehomogenization
public import PaperVerification.HomogeneousQuotientProjective
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The actual affine charts of a homogeneous polynomial quotient

For every homogeneous ideal Q and every coordinate p, the actual
degree-zero localization of P/Q at the class of X_p is canonically
P/(Q+(X_p-1)).  The comparison uses the existing homogeneous localization,
the proved degree-one dehomogenization isomorphism, and the ordinary
double-quotient theorem.  No radical or saturation is substituted.

Applying the actual Proj basic-open isomorphism gives a scheme
isomorphism, not only equality of field-valued points.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.HomogeneousQuotientCharts

open AlgebraicGeometry MvPolynomial CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra
open PaperVerification.HomogeneousChartDehomogenization

variable {K ι : Type*} [Field K]
  (Q : Ideal (MvPolynomial ι K))
  (hQ : Q.IsHomogeneous (homogeneousSubmodule ι K))
  (p : ι)

local notation "P" => MvPolynomial ι K
local notation "𝒜" => HomogeneousQuotientProjective.grading Q hQ

/-- The normalization ideal in the original quotient is exactly the
image of the literal normalization equation in the polynomial ring. -/
theorem normalizationIdeal_eq_map :
    normalizationIdeal (Ideal.Quotient.mk Q (X p))=
      (Ideal.span ({X p-1} : Set P)).map (Ideal.Quotient.mk Q) := by
  rw [normalizationIdeal,Ideal.map_span,Set.image_singleton,map_sub,map_one]

/-- The two successive literal quotients are the simultaneous quotient. -/
def normalizedQuotientEquiv :
    NormalizedRing (Ideal.Quotient.mk Q (X p)) ≃+*
      (P ⧸ (Q ⊔ Ideal.span {X p-1})) :=
  (Ideal.quotEquivOfEq (normalizationIdeal_eq_map Q p)).trans
    (DoubleQuot.quotQuotEquivQuotSup Q (Ideal.span {X p-1}))

@[simp] theorem normalizedQuotientEquiv_class (f : P) :
    normalizedQuotientEquiv Q p
      (quotientMap (Ideal.Quotient.mk Q (X p)) (Ideal.Quotient.mk Q f))=
      Ideal.Quotient.mk (Q ⊔ Ideal.span {X p-1}) f := by
  change (DoubleQuot.quotQuotEquivQuotSup Q (Ideal.span {X p-1}))
    ((Ideal.quotEquivOfEq (normalizationIdeal_eq_map Q p))
      (Ideal.Quotient.mk _ (Ideal.Quotient.mk Q f)))=_
  rw [Ideal.quotEquivOfEq_mk]
  rfl

/-- The actual affine Proj chart ring is the original normalized
homogeneous quotient, preserving its whole scheme structure. -/
def awayQuotientChartEquiv :
    HomogeneousLocalization.Away 𝒜 (Ideal.Quotient.mk Q (X p)) ≃+*
      (P ⧸ (Q ⊔ Ideal.span {X p-1})) :=
  (awayEquivNormalized 𝒜
    (HomogeneousQuotientProjective.quotient_X_mem_one Q hQ p)).trans
    (normalizedQuotientEquiv Q p)

/-- Its formula on each original homogeneous coordinate is exactly
X_i/X_p mapped to the class of X_i after setting X_p=1. -/
@[simp] theorem awayQuotientChartEquiv_coordinate (i : ι) :
    awayQuotientChartEquiv Q hQ p
      (fraction 𝒜 (HomogeneousQuotientProjective.quotient_X_mem_one Q hQ p) 1
        ⟨Ideal.Quotient.mk Q (X i),
          HomogeneousQuotientProjective.quotient_X_mem_one Q hQ i⟩)=
      Ideal.Quotient.mk (Q ⊔ Ideal.span {X p-1}) (X i) := by
  rw [awayQuotientChartEquiv,RingEquiv.trans_apply,
    awayEquivNormalized_fraction,normalizedQuotientEquiv_class]

/-- The actual open subscheme D_+(X_p) of Proj(P/Q), with its full
structure sheaf, is the spectrum of the literal normalized quotient. -/
def projectiveBasicOpenIsoNormalized :
    (Proj.basicOpen 𝒜 (Ideal.Quotient.mk Q (X p))).toScheme ≅
      Spec (CommRingCat.of (P ⧸ (Q ⊔ Ideal.span {X p-1}))) :=
  Proj.basicOpenIsoSpec 𝒜 (Ideal.Quotient.mk Q (X p))
      (HomogeneousQuotientProjective.quotient_X_mem_one Q hQ p) one_pos ≪≫
    Scheme.Spec.mapIso (awayQuotientChartEquiv Q hQ p).symm.toCommRingCatIso.op

end PaperVerification.HomogeneousQuotientCharts
