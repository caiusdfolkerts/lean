module

public import ToricPower.InversePairingFrameEvaluation
public import ToricPower.CartierPairingValues
public import ToricPower.DiagonalAugmentationCoefficients
public import ToricPower.SchemeInternalDual

/-!
# The actual inverse frame on an open chart

Restriction carries the specified Cartier pairing to its literal
sectionwise product. The canonical inverse frame therefore has the
reciprocal rational character of the specified original frame. This is
a value calculation for the actual map, with its normalization retained.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory TopologicalSpace
open TauCeti.AlgebraicGeometry.Scheme

namespace ToricPower

universe u
variable {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]

/-- The specified evaluation pairing transported by actual open
restriction, including its canonical tensor and unit maps. -/
def restrictedPairingIso {L D : Y.Modules} (evaluation : L ⊗ D ≅ 𝟙_ Y.Modules) :
    L.restrict j ⊗ D.restrict j ≅ 𝟙_ X.Modules :=
  asIso (Functor.LaxMonoidal.μ (Scheme.Modules.restrictFunctor j) L D) ≪≫
    (Scheme.Modules.restrictFunctor j).mapIso evaluation ≪≫
      Scheme.Modules.restrictUnitIso j

/-- On actual inserted sections the transported pairing is the
original pairing followed by the actual structure-sheaf map. -/
theorem restrictedPairingIso_tmul {L D : Y.Modules}
    (evaluation : L ⊗ D ≅ 𝟙_ Y.Modules) (U : X.Opens)
    (s : Γ(L,j ''ᵁ U)) (t : Γ(D,j ''ᵁ U)) :
    Scheme.Modules.Hom.app (restrictedPairingIso j evaluation).hom U
      (schemeTensorSection (L.restrict j) (D.restrict j) U s t) =
    (j.appIso U).hom
      (Scheme.Modules.Hom.app evaluation.hom (j ''ᵁ U)
        (schemeTensorSection L D (j ''ᵁ U) s t)) := by
  change (j.appIso U).hom
      (Scheme.Modules.Hom.app evaluation.hom (j ''ᵁ U)
        (Scheme.Modules.Hom.app
          (Functor.LaxMonoidal.μ (Scheme.Modules.restrictFunctor j) L D) U
          (schemeTensorSection (L.restrict j) (D.restrict j) U s t))) = _
  exact congrArg (fun z => (j.appIso U).hom
    (Scheme.Modules.Hom.app evaluation.hom (j ''ᵁ U) z))
    (restriction_tensor_section j L D U s t)

variable [IsIntegral Y] (D : CartierDivisor Y)
  (frame : 𝟙_ X.Modules ≅ D.sheaf.restrict j)

/-- The actual canonically normalized inverse frame on the same open. -/
def restrictedCartierInverseFrame : (-D).sheaf.restrict j ≅ 𝟙_ X.Modules :=
  inversePairingFrame
    (restrictedPairingIso j (cartierNegTensorIsoUnit D))
    (restrictedPairingIso j (cartierTensorNegIsoUnit D)) frame

/-- The product of the two original rational frame values is exactly
one. The conclusion concerns the actual inverse frame's value. -/
theorem restrictedCartierInverseFrame_product
    [Nonempty (j ''ᵁ (⊤ : X.Opens))] :
    rationalFunctionsEquiv (j ''ᵁ (⊤ : X.Opens))
        (Scheme.Modules.Hom.app D.sheafι (j ''ᵁ (⊤ : X.Opens))
          (Scheme.Modules.Hom.app frame.hom ⊤ (1 : Γ(X,⊤)))) *
      rationalFunctionsEquiv (j ''ᵁ (⊤ : X.Opens))
        (Scheme.Modules.Hom.app (-D).sheafι (j ''ᵁ (⊤ : X.Opens))
          (Scheme.Modules.Hom.app (restrictedCartierInverseFrame j D frame).inv
            ⊤ (1 : Γ(X,⊤)))) = 1 := by
  have paired := inversePairingFrame_inv_pairing
    (restrictedPairingIso j (cartierNegTensorIsoUnit D))
    (restrictedPairingIso j (cartierTensorNegIsoUnit D)) frame
  have normalized :
      (λ_ (𝟙_ X.Modules)).inv ≫
        (frame.hom ⊗ₘ (restrictedCartierInverseFrame j D frame).inv) ≫
          (restrictedPairingIso j (cartierTensorNegIsoUnit D)).hom = 𝟙 _ := by
    exact (congrArg (fun h => (λ_ (𝟙_ X.Modules)).inv ≫ h) paired).trans
      (Iso.inv_hom_id _)
  have value := congrArg
    (fun f : (𝟙_ X.Modules) ⟶ (𝟙_ X.Modules) =>
      (Scheme.Modules.Hom.app f ⊤ (1 : Γ(X,⊤)) : Γ(X,⊤))) normalized
  change Scheme.Modules.Hom.app (restrictedPairingIso j (cartierTensorNegIsoUnit D)).hom ⊤
      (Scheme.Modules.Hom.app
        ((λ_ (𝟙_ X.Modules)).inv ≫
          (frame.hom ⊗ₘ (restrictedCartierInverseFrame j D frame).inv))
        ⊤ (1 : Γ(X,⊤))) = (1 : Γ(X,⊤)) at value
  erw [unitSheaf_tensor_frame_one frame.hom
    (restrictedCartierInverseFrame j D frame).inv ⊤] at value
  erw [restrictedPairingIso_tmul] at value
  have original :
      Scheme.Modules.Hom.app (cartierTensorNegIsoUnit D).hom (j ''ᵁ (⊤ : X.Opens))
        (schemeTensorSection _ _ _
          (Scheme.Modules.Hom.app frame.hom ⊤ (1 : Γ(X,⊤)))
          (Scheme.Modules.Hom.app (restrictedCartierInverseFrame j D frame).inv
            ⊤ (1 : Γ(X,⊤)))) = (1 : Γ(Y,j ''ᵁ (⊤ : X.Opens))) := by
    apply (j.appIso ⊤).commRingCatIsoToRingEquiv.injective
    change (j.appIso ⊤).hom _ = (j.appIso ⊤).hom (1 : Γ(Y,j ''ᵁ (⊤ : X.Opens)))
    rw [(j.appIso ⊤).hom.hom.map_one]
    exact value
  have rational := congrArg (Y.germToFunctionField (j ''ᵁ (⊤ : X.Opens))) original
  rw [cartierTensorNegIsoUnit_value] at rational
  rw [(Y.germToFunctionField (j ''ᵁ (⊤ : X.Opens))).hom.map_one] at rational
  exact rational

/-- If the given frame has character `r⁻¹`, its actual canonical dual
frame has character `r`, including the scalar normalization. -/
theorem restrictedCartierInverseFrame_value
    [Nonempty (j ''ᵁ (⊤ : X.Opens))] (r : Y.functionFieldˣ)
    (original : rationalFunctionsEquiv (j ''ᵁ (⊤ : X.Opens))
      (Scheme.Modules.Hom.app D.sheafι (j ''ᵁ (⊤ : X.Opens))
        (Scheme.Modules.Hom.app frame.hom ⊤ (1 : Γ(X,⊤)))) = (r⁻¹ : Y.functionField)) :
    rationalFunctionsEquiv (j ''ᵁ (⊤ : X.Opens))
      (Scheme.Modules.Hom.app (-D).sheafι (j ''ᵁ (⊤ : X.Opens))
        (Scheme.Modules.Hom.app (restrictedCartierInverseFrame j D frame).inv
          ⊤ (1 : Γ(X,⊤)))) = (r : Y.functionField) := by
  have product := restrictedCartierInverseFrame_product j D frame
  rw [original] at product
  have multiplied := congrArg (fun z => (r : Y.functionField) * z) product
  simpa only [← mul_assoc, mul_inv_cancel₀ (Units.ne_zero r), one_mul, mul_one]
    using multiplied

end ToricPower

end
