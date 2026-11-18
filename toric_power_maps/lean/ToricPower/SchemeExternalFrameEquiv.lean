module

public import ToricPower.SchemeExternalFramedSections

/-! # Transport of the canonical exterior-section isomorphism through frames -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct

namespace ToricPower

universe u
variable (k : Type u) [Field k]
  {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
  (f : Z ⟶ X) (g : Z ⟶ Y)
  [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
  {L : X.Modules} {M : Y.Modules}
  (left : 𝟙_ X.Modules ≅ L) (right : 𝟙_ Y.Modules ≅ M)
  (unit : (FiniteCover.schemeBaseSections k X ⊤).obj (𝟙_ X.Modules) ⊗[k]
      (FiniteCover.schemeBaseSections k Y ⊤).obj (𝟙_ Y.Modules) ≃ₗ[k]
        (FiniteCover.schemeBaseSections k Z ⊤).obj
          (schemeExteriorSheaf f g (𝟙_ X.Modules) (𝟙_ Y.Modules)))

/-- Transfer the unit isomorphism through the specified frames. -/
def schemeExternalSectionsLinearEquivOfFrames :
    (FiniteCover.schemeBaseSections k X ⊤).obj L ⊗[k]
      (FiniteCover.schemeBaseSections k Y ⊤).obj M ≃ₗ[k]
        (FiniteCover.schemeBaseSections k Z ⊤).obj (schemeExteriorSheaf f g L M) :=
  (TensorProduct.congr
    (((FiniteCover.schemeBaseSections k X ⊤).mapIso left).toLinearEquiv.symm)
    (((FiniteCover.schemeBaseSections k Y ⊤).mapIso right).toLinearEquiv.symm)).trans
      (unit.trans
        (((FiniteCover.schemeBaseSections k Z ⊤).mapIso
          (tensorIso ((Scheme.Modules.pullback f).mapIso left)
            ((Scheme.Modules.pullback g).mapIso right))).toLinearEquiv))

/-- When the unit isomorphism is the canonical exterior map, the
transported isomorphism remains precisely that canonical map. -/
theorem schemeExternalSectionsLinearEquivOfFrames_eq
    (unitFormula : ∀ r s, unit (r ⊗ₜ[k] s) =
      schemeExternalSection k f g (𝟙_ X.Modules) (𝟙_ Y.Modules) r s) :
    (schemeExternalSectionsLinearEquivOfFrames k f g left right unit).toLinearMap =
      schemeExternalSectionsLinearMap k f g L M := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro s
  apply LinearMap.ext
  intro t
  change schemeExternalSectionsLinearEquivOfFrames k f g left right unit (s ⊗ₜ[k] t) =
    schemeExternalSectionsLinearMap k f g L M (s ⊗ₜ[k] t)
  obtain ⟨r, rfl⟩ := ((FiniteCover.schemeBaseSections k X ⊤).mapIso left).toLinearEquiv.surjective s
  obtain ⟨q, rfl⟩ := ((FiniteCover.schemeBaseSections k Y ⊤).mapIso right).toLinearEquiv.surjective t
  simp only [LinearEquiv.toLinearMap_eq_coe, LinearEquiv.coe_coe,
    schemeExternalSectionsLinearEquivOfFrames, LinearEquiv.trans_apply,
    TensorProduct.congr_tmul, LinearEquiv.symm_apply_apply, unitFormula,
    schemeExternalSectionsLinearMap_tmul]
  exact (schemeExternalSection_naturality k f g (𝟙_ X.Modules) (𝟙_ Y.Modules)
    left.hom right.hom r q).symm

end ToricPower

end
