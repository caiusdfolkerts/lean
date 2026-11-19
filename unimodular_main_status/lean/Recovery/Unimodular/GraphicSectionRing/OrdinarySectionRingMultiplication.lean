module

public import Recovery.Unimodular.GraphicSectionRing.CanonicalTensorCoherence
public import Recovery.Unimodular.GraphicSectionRing.InvertibleSectionRingTensorProducts

/-!
# The section ring has canonical ordinary tensor-power multiplication

The original invertible sheaf is unchanged. Its homogeneous products are
induced by the canonical recursive tensor-power multiplication of the
ordinary monoidal category of sheaves of modules. The equality is an
equality of complete linear maps on the ordinary tensor products of global
sections, for every pair of natural degrees.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

universe u
open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricSchemes
open scoped TensorProduct BaseSections

namespace Unimodular.GraphicSectionRing.CanonicalPowers

variable {X : Scheme.{u}} (k : Type u) [Field k]
  [X.Over (Spec (CommRingCat.of k))]

/-- Multiplication of ordinary tensor-power sections using only the canonical
monoidal associator, unitor, and the usual sheaf tensor section map. -/
def sectionMultiplication (M : X.Modules) (i j : ℕ) :
    Γ(tensorSheafPower M i, ⊤) ⊗[k] Γ(tensorSheafPower M j, ⊤) →ₗ[k]
      Γ(tensorSheafPower M (i + j), ⊤) :=
  (BaseSections.globalSectionsIso k (multiplyIso M i j)).toLinearMap.comp
    (moduleSectionMultiplicationOver k (tensorSheafPower M i) (tensorSheafPower M j))

end Unimodular.GraphicSectionRing.CanonicalPowers

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open Unimodular.GraphicSectionRing

variable {n : ℕ} (F : SmoothCompleteFan n) (k : Type u) [Field k]
  (M : (F.fanScheme k).Modules) (hM : IsInvertibleModule M)

/-- The previously displayed genuine Cartier transport is exactly the
independently constructed canonical ordinary tensor-power isomorphism. -/
theorem invertibleTensorProductIso_eq_canonical (i j : ℕ) :
    F.invertibleTensorProductIso k M hM i j = CanonicalPowers.multiplyIso M i j := by
  symm
  simpa only [invertibleTensorProductIso, invertibleTensorPowerIso,
    CanonicalPowers.sourceCartierIso, Iso.trans_assoc,
    invertibleFractionalPresentation_sheaf] using
    CanonicalPowers.multiplyIso_eq_cartierTransport (invertibleFractionalPresentation M hM) i j

/-- The entire tensor section multiplication agrees with the independent
ordinary canonical definition. -/
theorem invertibleTensorSectionMultiplication_eq_canonical (i j : ℕ) :
    F.invertibleTensorSectionMultiplication k M hM i j =
      CanonicalPowers.sectionMultiplication k M i j := by
  unfold invertibleTensorSectionMultiplication CanonicalPowers.sectionMultiplication
  rw [F.invertibleTensorProductIso_eq_canonical k M hM i j]

/-- The ordinary degree-zero structure-sheaf section one is exactly the
unit of the constructed section ring. -/
theorem invertibleHomogeneousSection_zero_one :
    F.invertibleHomogeneousSection k M hM 0
      (1 : Γ(F.fanScheme k, ⊤)) = 1 := by
  let D := invertibleFractionalPresentation M hM
  have h := CanonicalPowers.cartierPowerIso_purePower_value D ⊤
    (0 : Γ(D.sheaf, ⊤)) 0
  simp only [CanonicalPowers.purePower, pow_zero] at h
  apply Subtype.ext
  change AddMonoidAlgebra.single 0
    ((D.localCocycle.pow 0).toCartierData.sectionValue ⊤
      ((D.tensorSheafNsmulIso 0).hom.app ⊤
        (1 : Γ(F.fanScheme k, ⊤)))) =
      (1 : AddMonoidAlgebra (F.fanScheme k).functionField ℕ)
  rw [h]
  rfl

/-- The actual constructed section ring realizes canonical multiplication
on every ordinary tensor-power section of the original arbitrary line bundle. -/
theorem invertibleHomogeneousSection_comp_canonicalMultiplication (i j : ℕ) :
    (F.invertibleHomogeneousSection k M hM (i + j)).comp
        (CanonicalPowers.sectionMultiplication k M i j) =
      (LinearMap.mul' k (F.invertibleSectionRing k M hM)).comp
        (TensorProduct.map (F.invertibleHomogeneousSection k M hM i)
          (F.invertibleHomogeneousSection k M hM j)) := by
  rw [← F.invertibleTensorSectionMultiplication_eq_canonical k M hM i j]
  exact F.invertibleHomogeneousSection_comp_tensorMultiplication k M hM i j

#print axioms invertibleTensorProductIso_eq_canonical
#print axioms invertibleTensorSectionMultiplication_eq_canonical
#print axioms invertibleHomogeneousSection_zero_one
#print axioms invertibleHomogeneousSection_comp_canonicalMultiplication

end PaperVerification.ToricGeometry.SmoothCompleteFan

#check PaperVerification.ToricGeometry.SmoothCompleteFan.invertibleHomogeneousSection_comp_canonicalMultiplication
