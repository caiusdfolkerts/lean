module

public import Recovery.Unimodular.GraphicSectionRing.ArbitrarySectionRing
public import Recovery.Unimodular.GraphicSectionRing.SectionRingTensorProducts

/-!
# Multiplication for the original ordinary invertible sheaf

The comparison from the tensor product of two actual powers of the original
sheaf to the sum power is displayed as a composite of genuine sheaf
isomorphisms. Its ordinary global-section tensor map induces exactly the
multiplication of the constructed section ring. No equality or coherence
property of tensor-power objects is assumed.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

universe u
namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricSchemes
open Unimodular.GraphicSectionRing
open scoped TensorProduct BaseSections

variable {n : ℕ} (F : SmoothCompleteFan n) (k : Type u) [Field k]
  (M : (F.fanScheme k).Modules) (hM : IsInvertibleModule M)

/-- This is the explicit composite of the two source power comparisons,
the actual Cartier tensor multiplication, and the inverse target comparison. -/
def invertibleTensorProductIso (i j : ℕ) :
    tensorSheaf (tensorSheafPower M i) (tensorSheafPower M j) ≅
      tensorSheafPower M (i + j) :=
  tensorSheafIso (F.invertibleTensorPowerIso k M hM i)
      (F.invertibleTensorPowerIso k M hM j) ≪≫
    ActualSections.powerTensorSheafIso (invertibleFractionalPresentation M hM).localCocycle i j ≪≫
    (F.invertibleTensorPowerIso k M hM (i + j)).symm

/-- The ordinary tensor product of global sections of powers of the given M,
followed by the displayed genuine target sheaf isomorphism. -/
def invertibleTensorSectionMultiplication (i j : ℕ) :
    Γ(tensorSheafPower M i, ⊤) ⊗[k] Γ(tensorSheafPower M j, ⊤) →ₗ[k]
      Γ(tensorSheafPower M (i + j), ⊤) :=
  (BaseSections.globalSectionsIso k (F.invertibleTensorProductIso k M hM i j)).toLinearMap.comp
    (moduleSectionMultiplicationOver k (tensorSheafPower M i) (tensorSheafPower M j))

/-- The comparison intertwines the actual tensor section maps in all degrees. -/
theorem invertibleTensorSectionMultiplication_transport (i j : ℕ) :
    (BaseSections.globalSectionsIso k
      (F.invertibleTensorPowerIso k M hM (i + j))).toLinearMap.comp
        (F.invertibleTensorSectionMultiplication k M hM i j) =
      (ActualSections.powerTensorSectionMultiplication
        (invertibleFractionalPresentation M hM).localCocycle k i j).comp
        (TensorProduct.map
          (BaseSections.globalSectionsIso k (F.invertibleTensorPowerIso k M hM i)).toLinearMap
          (BaseSections.globalSectionsIso k (F.invertibleTensorPowerIso k M hM j)).toLinearMap) := by
  apply TensorProduct.ext'
  intro s t
  let ei := BaseSections.globalSectionsIso k (F.invertibleTensorPowerIso k M hM i)
  let ej := BaseSections.globalSectionsIso k (F.invertibleTensorPowerIso k M hM j)
  let eij := BaseSections.globalSectionsIso k (F.invertibleTensorPowerIso k M hM (i + j))
  change eij (eij.symm
    ((ActualSections.powerTensorSheafIso
      (invertibleFractionalPresentation M hM).localCocycle i j).hom.app ⊤
      ((tensorSheafIso (F.invertibleTensorPowerIso k M hM i)
        (F.invertibleTensorPowerIso k M hM j)).hom.app ⊤
        ((tensorSheafUnit (tensorSheafPower M i) (tensorSheafPower M j)).app (Opposite.op ⊤)
          (s ⊗ₜ[Γ(F.fanScheme k, ⊤)] t))))) =
    (ActualSections.powerTensorSheafIso
      (invertibleFractionalPresentation M hM).localCocycle i j).hom.app ⊤
      ((tensorSheafUnit
        ((invertibleFractionalPresentation M hM).localCocycle.pow i).sheaf
        ((invertibleFractionalPresentation M hM).localCocycle.pow j).sheaf).app (Opposite.op ⊤)
        (ei s ⊗ₜ[Γ(F.fanScheme k, ⊤)] ej t))
  rw [LinearEquiv.apply_symm_apply, tensorSheafIso_pure_sections]
  rfl

/-- Equality of the complete multiplication maps on the ordinary tensor
product of global sections of powers of the original invertible sheaf. -/
theorem invertibleHomogeneousSection_comp_tensorMultiplication (i j : ℕ) :
    (F.invertibleHomogeneousSection k M hM (i + j)).comp
        (F.invertibleTensorSectionMultiplication k M hM i j) =
      (LinearMap.mul' k (F.invertibleSectionRing k M hM)).comp
        (TensorProduct.map (F.invertibleHomogeneousSection k M hM i)
          (F.invertibleHomogeneousSection k M hM j)) := by
  apply TensorProduct.ext'
  intro s t
  let C := (invertibleFractionalPresentation M hM).localCocycle
  let ei := BaseSections.globalSectionsIso k (F.invertibleTensorPowerIso k M hM i)
  let ej := BaseSections.globalSectionsIso k (F.invertibleTensorPowerIso k M hM j)
  have ht := LinearMap.congr_fun
    (F.invertibleTensorSectionMultiplication_transport k M hM i j) (s ⊗ₜ[k] t)
  change (BaseSections.globalSectionsIso k (F.invertibleTensorPowerIso k M hM (i + j)))
      (F.invertibleTensorSectionMultiplication k M hM i j (s ⊗ₜ[k] t)) =
    ActualSections.powerTensorSectionMultiplication C k i j (ei s ⊗ₜ[k] ej t) at ht
  change ActualSections.homogeneousSection k C (i + j)
      ((BaseSections.globalSectionsIso k (F.invertibleTensorPowerIso k M hM (i + j)))
        (F.invertibleTensorSectionMultiplication k M hM i j (s ⊗ₜ[k] t))) =
    ActualSections.homogeneousSection k C i (ei s) *
      ActualSections.homogeneousSection k C j (ej t)
  rw [ht]
  exact (ActualSections.homogeneousSection_mul_tensor C k i j (ei s) (ej t)).symm

#print axioms invertibleTensorProductIso
#print axioms invertibleTensorSectionMultiplication_transport
#print axioms invertibleHomogeneousSection_comp_tensorMultiplication

end PaperVerification.ToricGeometry.SmoothCompleteFan

#check PaperVerification.ToricGeometry.SmoothCompleteFan.invertibleHomogeneousSection_comp_tensorMultiplication
