module

public import PaperVerification.ExteriorMonomialKoszul
public import PaperVerification.AlternatingFormsExteriorAugmentation
public import PaperVerification.AlternatingFormsExteriorTransport

/-!
# Actual homogeneous Koszul certificates for exterior quotients

A certificate consists of a genuine finite homogeneous augmented basis
of the original quotient, with its original exterior degrees, and
concentration of actual ordinary Tor. It is constructed from the proved
monomial quotient theorem after an equality of the actual generated
ideals. No assertion that the quotient has a normal form is built into
the certificate or into the algebra's definition.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace PaperVerification.AlternatingForms.ExteriorKoszul

open PaperVerification ExteriorAugmented ExteriorMonomialQuotient
  ExteriorMonomialKoszul AugmentedAlgebraBasis QuadraticWordBar

universe u
variable {K M : Type u} [Field K] [AddCommGroup M] [Module K M]

/-- Every field describes actual algebra, grading or derived-functor data.
The diagonal assertion concerns ordinary Tor and the original grading. -/
structure HomogeneousKoszulCertificate (f g : ⋀[K]^2 M) where
  Index : Type u
  finite : Finite Index
  basis : Module.Basis (Option Index) K (ExteriorAugmented.Quotient f g)
  degree : Index→ℕ
  unit : basis none=1
  positive : ∀ i,0<degree i
  homogeneous : ∀ i,basis (some i)∈(ExteriorAugmented.grading f g).piece (degree i)
  augmentation_zero : ∀ i,ExteriorAugmented.augmentation f g (basis (some i))=0
  product_degree : ∀ a b c,productCoefficients basis a b c≠0 →degree c=degree a+degree b
  diagonal : WeightedBar.HasDiagonalTor (ExteriorAugmented.augmentation f g)
    basis unit augmentation_zero degree product_degree

section Transport

variable {A D C : Type u} [Ring A] [Algebra K A] [Ring D] [Algebra K D]
  (e : A≃ₐ[K]D) (B : Module.Basis (Option C) K A)

/-- Actual basis coefficients of products are unchanged by an algebra
isomorphism; no commutativity of either algebra is required. -/
theorem map_productCoefficients (a b : C) :
    productCoefficients (B.map e.toLinearEquiv) a b=productCoefficients B a b := by
  apply Finsupp.ext
  intro c
  change (B.map e.toLinearEquiv).repr
      ((B.map e.toLinearEquiv) (some a)*(B.map e.toLinearEquiv) (some b)) (some c)=
    B.repr (B (some a)*B (some b)) (some c)
  rw [Module.Basis.map_apply,Module.Basis.map_apply]
  change (B.map e.toLinearEquiv).repr (e (B (some a))*e (B (some b))) (some c)=_
  have hm : e (B (some a)*B (some b))=e (B (some a))*e (B (some b)) :=
    map_mul e _ _
  rw [←hm]
  change B.repr (e.symm (e (B (some a)*B (some b)))) (some c)=_
  rw [e.symm_apply_apply]

end Transport

section Monomial

variable {I : Type u} [LinearOrder I] [Fintype I]
  (b : Module.Basis I K M) (F : Set (Finset I)) (hF : ∀ S∈F,S.Nonempty)
  (R : I→I→Prop) [IsTrans I R] (hlt : ∀ i j,R i j→i<j)
  (hchain : ∀ S : Finset I,¬Bad F S↔S.sort.IsChain R)
  (f g : ⋀[K]^2 M) (he : monomialIdeal b F=exteriorRelationIdeal f g)

def actualBasis : Module.Basis (Option (PositiveIndex F)) K
    (ExteriorAugmented.Quotient f g) :=
  (augmentedBasis b F hF).map (Ideal.quotientEquivAlgOfEq K he).toLinearEquiv

@[simp] theorem actualBasis_none : actualBasis b F hF f g he none=1 := by
  rw [actualBasis,Module.Basis.map_apply,augmentedBasis_none]
  change Ideal.quotientEquivAlgOfEq K he (1 : ExteriorAlgebra K M⧸monomialIdeal b F)=1
  exact map_one (Ideal.quotientEquivAlgOfEq K he)

@[simp] theorem actualBasis_some (S : PositiveIndex F) :
    actualBasis b F hF f g he (some S)=
      Ideal.Quotient.mk (exteriorRelationIdeal f g) (b.ExteriorAlgebra S.val.val) := by
  rw [actualBasis,Module.Basis.map_apply,augmentedBasis_some]
  rfl

theorem actualBasis_homogeneous (S : PositiveIndex F) :
    actualBasis b F hF f g he (some S)∈(ExteriorAugmented.grading f g).piece
      (QuadraticWordPBW.wordDegree (normalWordEquiv F R hlt hchain) S) := by
  rw [normalWordEquiv_degree,actualBasis_some,ExteriorAugmented.grading_piece]
  refine ⟨b.ExteriorAlgebra S.val.val,?_,rfl⟩
  have h := ExteriorAlgebra.basis_eq_coe_basis b
    (⟨S.val.val,rfl⟩ : Set.powersetCard I S.val.val.card)
  rw [h]
  exact (b.exteriorPower S.val.val.card
    (⟨S.val.val,rfl⟩ : Set.powersetCard I S.val.val.card)).property

theorem actualBasis_augmentation (S : PositiveIndex F) :
    ExteriorAugmented.augmentation f g (actualBasis b F hF f g he (some S))=0 := by
  rw [actualBasis_some,ExteriorAugmented.augmentation_mk]
  exact algebraMapInv_basis b S.val.val S.property

theorem actualBasis_productCoefficients (S T : PositiveIndex F) :
    productCoefficients (actualBasis b F hF f g he) S T=
      productCoefficients (augmentedBasis b F hF) S T :=
  map_productCoefficients (Ideal.quotientEquivAlgOfEq K he) (augmentedBasis b F hF) S T

theorem actualBasis_normal_product (S T : PositiveIndex F)
    (h : ((normalWordEquiv F R hlt hchain S).val++
      (normalWordEquiv F R hlt hchain T).val).IsChain R) :
    productCoefficients (actualBasis b F hF f g he) S T=
      Finsupp.single (concatenateNormal (normalWordEquiv F R hlt hchain) S T h) 1 := by
  rw [actualBasis_productCoefficients]
  exact normal_product b F hF R hlt hchain S T h

theorem actualBasis_product_perm (S T U : PositiveIndex F)
    (h : productCoefficients (actualBasis b F hF f g he) S T U≠0) :
    (normalWordEquiv F R hlt hchain U).val.Perm
      ((normalWordEquiv F R hlt hchain S).val++
        (normalWordEquiv F R hlt hchain T).val) := by
  rw [actualBasis_productCoefficients] at h
  exact product_perm b F hF R hlt hchain S T U h

/-- The positive ordinary-Tor theorem is obtained on the actual quotient
and the actual exterior grading. The preceding ideal equality is proved
from the concrete generic normal forms in the small-dimensional cases. -/
def certificateOfMonomialIdeal : HomogeneousKoszulCertificate f g where
  Index := PositiveIndex F
  finite := inferInstance
  basis := actualBasis b F hF f g he
  degree := QuadraticWordPBW.wordDegree (normalWordEquiv F R hlt hchain)
  unit := actualBasis_none b F hF f g he
  positive i := by rw [normalWordEquiv_degree]; exact i.property.card_pos
  homogeneous := actualBasis_homogeneous b F hF R hlt hchain f g he
  augmentation_zero := actualBasis_augmentation b F hF f g he
  product_degree := QuadraticWordPBW.product_degree (actualBasis b F hF f g he)
    (normalWordEquiv F R hlt hchain)
    (actualBasis_product_perm b F hF R hlt hchain f g he)
  diagonal := QuadraticWordPBW.hasDiagonalTor (ExteriorAugmented.augmentation f g)
    (actualBasis b F hF f g he) (actualBasis_none b F hF f g he)
    (actualBasis_augmentation b F hF f g he) (normalWordEquiv F R hlt hchain)
    (actualBasis_normal_product b F hF R hlt hchain f g he)
    (actualBasis_product_perm b F hF R hlt hchain f g he)

end Monomial
end PaperVerification.AlternatingForms.ExteriorKoszul
