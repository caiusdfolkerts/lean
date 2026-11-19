module

public import Recovery.Unimodular.GraphicSectionRing.OrdinarySectionRingMultiplication

/-!
# Ordinary Cartier section values, multiplication and the degree-zero unit

UNCOMPILED SOURCE CANDIDATE.

These generic declarations are extracted verbatim from the independently
reviewed SchemeIsoSectionAlgebra source. They concern every actual Cartier
sheaf on every integral scheme over the field, all natural tensor degrees,
and the independently constructed canonical tensor multiplication. The
module uses only the checked ordinary-multiplication dependency and does
not depend on fan classification, curve geometry or projectivity.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace Unimodular.GraphicSectionRing.ActualSections

open AlgebraicGeometry CategoryTheory Opposite
open PaperVerification.ToricSchemes
open scoped TensorProduct BaseSections

variable (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of k))]

/-- The actual ordinary tensor-power sections are identified with their
actual rational values through the already proved Cartier power comparison. -/
def ordinaryPowerValueEquiv (D : CartierData X) (d : ℕ) :
    Γ(tensorSheafPower D.sheaf d, ⊤) ≃ₗ[k] powerValues k D.localCocycle d :=
  (BaseSections.globalSectionsIso k (D.tensorSheafNsmulIso d)).trans
    (powerValueEquiv k D.localCocycle d)

/-- The actual homogeneous inclusion for an arbitrary Cartier sheaf. -/
def ordinaryHomogeneousSection (D : CartierData X) (d : ℕ) :
    Γ(tensorSheafPower D.sheaf d, ⊤) →ₗ[k] sectionRing k D.localCocycle :=
  (homogeneousSection k D.localCocycle d).comp
    (BaseSections.globalSectionsIso k (D.tensorSheafNsmulIso d)).toLinearMap

@[simp] theorem ordinaryHomogeneousSection_value (D : CartierData X) (d : ℕ)
    (s : Γ(tensorSheafPower D.sheaf d, ⊤)) :
    (ordinaryHomogeneousSection k D d s).val =
      AddMonoidAlgebra.single d (ordinaryPowerValueEquiv k D d s).val := rfl

/-- The independently constructed canonical ordinary tensor map multiplies
precisely the actual rational values, for every pair of natural degrees. -/
theorem ordinaryPowerValueEquiv_canonicalMultiplication (D : CartierData X)
    (i j : ℕ) (s : Γ(tensorSheafPower D.sheaf i, ⊤))
    (t : Γ(tensorSheafPower D.sheaf j, ⊤)) :
    (ordinaryPowerValueEquiv k D (i + j)
      (CanonicalPowers.sectionMultiplication k D.sheaf i j (s ⊗ₜ[k] t))).val =
        (ordinaryPowerValueEquiv k D i s).val *
          (ordinaryPowerValueEquiv k D j t).val := by
  let C := D.localCocycle
  have h := congrArg
    (fun α : tensorSheaf (tensorSheafPower D.sheaf i) (tensorSheafPower D.sheaf j) ⟶
      (C.pow (i + j)).sheaf =>
        α.app ⊤ ((tensorSheafUnit (tensorSheafPower D.sheaf i)
          (tensorSheafPower D.sheaf j)).app (op ⊤)
            (s ⊗ₜ[Γ(X, ⊤)] t)))
    (CanonicalPowers.multiplyIso_comp_cartierPowerIso D i j)
  change (D.tensorSheafNsmulIso (i + j)).hom.app ⊤
      ((CanonicalPowers.multiplyIso D.sheaf i j).hom.app ⊤
        ((tensorSheafUnit (tensorSheafPower D.sheaf i)
          (tensorSheafPower D.sheaf j)).app (op ⊤) (s ⊗ₜ[Γ(X, ⊤)] t))) =
    (CanonicalPowers.sourceCartierIso D i j).hom.app ⊤
      ((tensorSheafUnit (tensorSheafPower D.sheaf i)
        (tensorSheafPower D.sheaf j)).app (op ⊤) (s ⊗ₜ[Γ(X, ⊤)] t)) at h
  change (C.pow (i + j)).toCartierData.sectionValue ⊤
      ((D.tensorSheafNsmulIso (i + j)).hom.app ⊤
        ((CanonicalPowers.multiplyIso D.sheaf i j).hom.app ⊤
          ((tensorSheafUnit (tensorSheafPower D.sheaf i)
            (tensorSheafPower D.sheaf j)).app (op ⊤) (s ⊗ₜ[Γ(X, ⊤)] t)))) = _
  rw [h]
  change (C.pow (i + j)).toCartierData.sectionValue ⊤
      ((powerTensorSheafIso C i j).hom.app ⊤
        ((tensorSheafIso (D.tensorSheafNsmulIso i) (D.tensorSheafNsmulIso j)).hom.app ⊤
          ((tensorSheafUnit (tensorSheafPower D.sheaf i)
            (tensorSheafPower D.sheaf j)).app (op ⊤) (s ⊗ₜ[Γ(X, ⊤)] t)))) = _
  rw [tensorSheafIso_pure_sections]
  exact powerTensorSheafIso_pure_value C i j ⊤
    ((D.tensorSheafNsmulIso i).hom.app ⊤ s)
    ((D.tensorSheafNsmulIso j).hom.app ⊤ t)

/-- The original Cartier sheaf's genuine tensor sections give the ordinary
section-ring product. This is derived from canonical tensor coherence. -/
theorem ordinaryHomogeneousSection_canonicalMultiplication (D : CartierData X)
    (i j : ℕ) (s : Γ(tensorSheafPower D.sheaf i, ⊤))
    (t : Γ(tensorSheafPower D.sheaf j, ⊤)) :
    ordinaryHomogeneousSection k D (i + j)
      (CanonicalPowers.sectionMultiplication k D.sheaf i j (s ⊗ₜ[k] t)) =
        ordinaryHomogeneousSection k D i s * ordinaryHomogeneousSection k D j t := by
  apply Subtype.ext
  change AddMonoidAlgebra.single (i + j)
      (ordinaryPowerValueEquiv k D (i + j)
        (CanonicalPowers.sectionMultiplication k D.sheaf i j (s ⊗ₜ[k] t))).val =
    AddMonoidAlgebra.single i (ordinaryPowerValueEquiv k D i s).val *
      AddMonoidAlgebra.single j (ordinaryPowerValueEquiv k D j t).val
  rw [ordinaryPowerValueEquiv_canonicalMultiplication,
    AddMonoidAlgebra.single_mul_single]

/-- The full ordinary tensor-product multiplication map, rather than a
restricted collection of decomposable sections. -/
theorem ordinaryHomogeneousSection_comp_canonicalMultiplication
    (D : CartierData X) (i j : ℕ) :
    (ordinaryHomogeneousSection k D (i + j)).comp
      (CanonicalPowers.sectionMultiplication k D.sheaf i j) =
        (LinearMap.mul' k (sectionRing k D.localCocycle)).comp
          (TensorProduct.map (ordinaryHomogeneousSection k D i)
            (ordinaryHomogeneousSection k D j)) := by
  apply TensorProduct.ext'
  intro s t
  exact ordinaryHomogeneousSection_canonicalMultiplication k D i j s t

/-- The degree-zero element is the actual structure-sheaf section one. -/
@[simp] theorem ordinaryHomogeneousSection_zero_one (D : CartierData X) :
    ordinaryHomogeneousSection k D 0 (1 : Γ(X, ⊤)) = 1 := by
  have h := CanonicalPowers.cartierPowerIso_purePower_value D ⊤
    (0 : Γ(D.sheaf, ⊤)) 0
  simp only [CanonicalPowers.purePower, pow_zero] at h
  apply Subtype.ext
  change AddMonoidAlgebra.single 0
    ((D.localCocycle.pow 0).toCartierData.sectionValue ⊤
      ((D.tensorSheafNsmulIso 0).hom.app ⊤ (1 : Γ(X, ⊤)))) =
        (1 : AddMonoidAlgebra X.functionField ℕ)
  rw [h]
  rfl

theorem ordinaryHomogeneousSection_injective (D : CartierData X) (d : ℕ) :
    Function.Injective (ordinaryHomogeneousSection k D d) :=
  (homogeneousSection_injective k D.localCocycle d).comp
    (BaseSections.globalSectionsIso k (D.tensorSheafNsmulIso d)).injective

#print axioms ordinaryPowerValueEquiv
#print axioms ordinaryHomogeneousSection
#print axioms ordinaryPowerValueEquiv_canonicalMultiplication
#print axioms ordinaryHomogeneousSection_comp_canonicalMultiplication
#print axioms ordinaryHomogeneousSection_zero_one
#print axioms ordinaryHomogeneousSection_injective

end Unimodular.GraphicSectionRing.ActualSections

#check Unimodular.GraphicSectionRing.ActualSections.ordinaryHomogeneousSection_comp_canonicalMultiplication
