module

public import ToricPower.InternalDualComplex
public import ToricPower.TensorInverseMates

/-!
# Actual internal duals of inverse tensor factors

Two specified inverse tensor isomorphisms identify the internal dual
with the inverse factor. The forward morphism is exactly the transpose
of the specified evaluation pairing. Compatibility of those pairings
therefore proves compatibility with every original morphism.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MonoidalCategory MonoidalClosed Opposite

namespace ToricPower

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
  (L D : C) (eDL : D ⊗ L ≅ 𝟙_ C) (eLD : L ⊗ D ≅ 𝟙_ C)

/-- Uniqueness of the actual right adjoint gives the inverse-factor
identification; no duality or evaluation axiom is added. -/
def inverseTensorInternalDualIso : D ≅ (internalDual C).obj (op L) :=
  (ρ_ D).symm ≪≫
    (Adjunction.rightAdjointUniq
      (tensorEquivalenceOfInverse L D eDL eLD).toAdjunction
      (ihom.adjunction L)).app (𝟙_ C)

/-- The chosen isomorphism is the actual transpose of the original
evaluation into the unit. -/
theorem inverseTensorInternalDualIso_hom :
    (inverseTensorInternalDualIso L D eDL eLD).hom = curry eLD.hom := by
  apply uncurry_injective
  rw [uncurry_curry]
  change uncurry ((ρ_ D).inv ≫
    (Adjunction.rightAdjointUniq
      (tensorEquivalenceOfInverse L D eDL eLD).toAdjunction
      (ihom.adjunction L)).hom.app (𝟙_ C)) = _
  rw [uncurry_natural_left]
  have mate := Adjunction.homEquiv_symm_rightAdjointUniq_hom_app
    (tensorEquivalenceOfInverse L D eDL eLD).toAdjunction
    (ihom.adjunction L) (𝟙_ C)
  change uncurry ((Adjunction.rightAdjointUniq
      (tensorEquivalenceOfInverse L D eDL eLD).toAdjunction
      (ihom.adjunction L)).hom.app (𝟙_ C)) = _ at mate
  rw [mate, tensorEquivalenceOfInverse_counit_app,
    whiskerLeft_rightUnitor_inv, Category.assoc, Iso.hom_inv_id_assoc,
    ← rightUnitor_inv_naturality_assoc, unitors_equal, Iso.inv_hom_id, Category.comp_id]

variable {L D}
  {L' D' : C} (eD'L' : D' ⊗ L' ≅ 𝟙_ C) (eL'D' : L' ⊗ D' ≅ 𝟙_ C)

/-- An equality of actual evaluation pairings is precisely the
contravariant naturality equation for the inverse-factor dual maps. -/
theorem inverseTensorInternalDualIso_naturality
    (f : L ⟶ L') (g : D' ⟶ D)
    (pairing : L ◁ g ≫ eLD.hom = f ▷ D' ≫ eL'D'.hom) :
    (inverseTensorInternalDualIso L' D' eD'L' eL'D').hom ≫
        (internalDual C).map f.op =
      g ≫ (inverseTensorInternalDualIso L D eDL eLD).hom := by
  rw [inverseTensorInternalDualIso_hom, inverseTensorInternalDualIso_hom]
  change curry eL'D'.hom ≫ (pre f).app (𝟙_ C) = g ≫ curry eLD.hom
  apply uncurry_injective
  rw [uncurry_pre_app, uncurry_natural_left, uncurry_curry, uncurry_curry]
  exact pairing.symm

end ToricPower

end
