module

public import ToricPower.SchemeExternalSections

/-!
# Exterior sections in specified rank-one frames

The unit calculation records the product of the two actual pulled-back
functions. A naturality square then transfers the unit calculation to
any two specified frames, preserving the canonical exterior-section map.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct

namespace ToricPower

universe u
variable (k : Type u) [Field k]

section Unit

variable (X : Scheme.{u}) [X.Over (Spec (.of k))]

/-- Unit-source coordinates of an actual function are its ordinary
multiplication endomorphism of the structure sheaf. -/
theorem moduleUnitActualSectionsLinearEquiv_symm_unit
    (r : (FiniteCover.schemeBaseSections k X ⊤).obj (𝟙_ X.Modules)) :
    (moduleUnitActualSectionsLinearEquiv k X (𝟙_ X.Modules)).symm r =
      Scheme.Modules.globalSectionsSmul (𝟙_ X.Modules) r := by
  apply (moduleUnitActualSectionsLinearEquiv k X (𝟙_ X.Modules)).injective
  rw [LinearEquiv.apply_symm_apply]
  change r = (Scheme.Modules.globalSectionsSmul (𝟙_ X.Modules) r).app ⊤ (1 : Γ(X, ⊤))
  rw [Scheme.Modules.globalSectionsSmul_app]
  change r = X.presheaf.map (𝟙 (⊤ : X.Opens)).op r * 1
  simp

/-- Evaluating scalar multiplication followed by a frame returns the
actual image of that scalar under the frame. -/
theorem moduleUnitActualSectionsLinearEquiv_scalar_frame (L : X.Modules)
    (frame : 𝟙_ X.Modules ≅ L) (r : Γ(X, ⊤)) :
    moduleUnitActualSectionsLinearEquiv k X L
      (Scheme.Modules.globalSectionsSmul (𝟙_ X.Modules) r ≫ frame.hom) =
        frame.hom.app ⊤ r := by
  change frame.hom.app ⊤
    ((Scheme.Modules.globalSectionsSmul (𝟙_ X.Modules) r).app ⊤ (1 : Γ(X, ⊤))) = _
  rw [Scheme.Modules.globalSectionsSmul_app]
  change frame.hom.app ⊤ (X.presheaf.map (𝟙 (⊤ : X.Opens)).op r * 1) = _
  simp

end Unit

section Exterior

variable {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
  (f : Z ⟶ X) (g : Z ⟶ Y)
  [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]

/-- The specified product frame for the two pulled-back unit sheaves. -/
def schemeExternalUnitFrame :
    𝟙_ Z.Modules ≅ schemeExteriorSheaf f g (𝟙_ X.Modules) (𝟙_ Y.Modules) :=
  (λ_ (𝟙_ Z.Modules)).symm ≪≫
    tensorIso (Scheme.Modules.pullbackObjUnitIso f).symm
      (Scheme.Modules.pullbackObjUnitIso g).symm

omit g in
theorem schemePullbackUnitHomLinearMap_unit_scalar (r : Γ(X, ⊤)) :
    schemePullbackUnitHomLinearMap k f (𝟙_ X.Modules)
      (Scheme.Modules.globalSectionsSmul (𝟙_ X.Modules) r) =
    Scheme.Modules.globalSectionsSmul (𝟙_ Z.Modules) (f.appTop r) ≫
      (Scheme.Modules.pullbackObjUnitIso f).inv := by
  change (Scheme.Modules.pullbackObjUnitIso f).inv ≫
      (Scheme.Modules.pullback f).map (Scheme.Modules.globalSectionsSmul (𝟙_ X.Modules) r) = _
  erw [Scheme.Modules.pullback_map_globalSectionsSmul]
  exact (Scheme.Modules.globalSectionsSmul_naturality
    (Scheme.Modules.pullbackObjUnitIso f).inv (f.appTop r)).symm

/-- In the original product frame, the exterior product is the product
of the two original pullbacks of global functions. -/
theorem schemeExternalSection_unit
    (r : (FiniteCover.schemeBaseSections k X ⊤).obj (𝟙_ X.Modules))
    (s : (FiniteCover.schemeBaseSections k Y ⊤).obj (𝟙_ Y.Modules)) :
    schemeExternalSection k f g (𝟙_ X.Modules) (𝟙_ Y.Modules) r s =
      (schemeExternalUnitFrame f g).hom.app ⊤ (f.appTop r * g.appTop s) := by
  unfold schemeExternalSection
  rw [moduleUnitActualSectionsLinearEquiv_symm_unit,
    moduleUnitActualSectionsLinearEquiv_symm_unit,
    schemePullbackUnitHomLinearMap_unit_scalar,
    schemePullbackUnitHomLinearMap_unit_scalar]
  change moduleUnitActualSectionsLinearEquiv k Z _
    ((λ_ (𝟙_ Z.Modules)).inv ≫
      ((Scheme.Modules.globalSectionsSmul (𝟙_ Z.Modules) (f.appTop r) ≫
          (Scheme.Modules.pullbackObjUnitIso f).inv) ⊗ₘ
        (Scheme.Modules.globalSectionsSmul (𝟙_ Z.Modules) (g.appTop s) ≫
          (Scheme.Modules.pullbackObjUnitIso g).inv))) = _
  rw [← tensorHom_comp_tensorHom, ← Category.assoc]
  have scalarTensor := unitSheafTensorSmul Z (f.appTop r) (g.appTop s)
  have equality := congrArg
    (fun h => moduleUnitActualSectionsLinearEquiv k Z _
      (h ≫ ((Scheme.Modules.pullbackObjUnitIso f).inv ⊗ₘ
        (Scheme.Modules.pullbackObjUnitIso g).inv))) scalarTensor
  refine equality.trans ?_
  rw [Category.assoc]
  exact moduleUnitActualSectionsLinearEquiv_scalar_frame k Z _
    (schemeExternalUnitFrame f g) _

/-- A frame in each factor gives the corresponding literal exterior
frame by pullback and tensor product. -/
def schemeExternalFrame {L : X.Modules} {M : Y.Modules}
    (left : 𝟙_ X.Modules ≅ L) (right : 𝟙_ Y.Modules ≅ M) :
    𝟙_ Z.Modules ≅ schemeExteriorSheaf f g L M :=
  schemeExternalUnitFrame f g ≪≫
    tensorIso ((Scheme.Modules.pullback f).mapIso left)
      ((Scheme.Modules.pullback g).mapIso right)

/-- The naturality formula in the original two frames. -/
theorem schemeExternalSection_framed {L : X.Modules} {M : Y.Modules}
    (left : 𝟙_ X.Modules ≅ L) (right : 𝟙_ Y.Modules ≅ M)
    (r : (FiniteCover.schemeBaseSections k X ⊤).obj (𝟙_ X.Modules))
    (s : (FiniteCover.schemeBaseSections k Y ⊤).obj (𝟙_ Y.Modules)) :
    schemeExternalSection k f g L M (left.hom.app ⊤ r) (right.hom.app ⊤ s) =
      (schemeExternalFrame f g left right).hom.app ⊤ (f.appTop r * g.appTop s) := by
  exact (schemeExternalSection_naturality k f g (𝟙_ X.Modules) (𝟙_ Y.Modules)
    left.hom right.hom r s).trans
      (congrArg
        ((FiniteCover.schemeBaseSections k Z ⊤).map
          ((Scheme.Modules.pullback f).map left.hom ⊗ₘ (Scheme.Modules.pullback g).map right.hom))
        (schemeExternalSection_unit k f g r s))

end Exterior

end ToricPower

end
