module

public import ToricPower.ModuleUnitSections
public import ToricPower.CartierHomSectionsDiagram
public import ToricPower.SchemeAffineLinear
public import ToricPower.SheafTensorBaseLinear
public import ToricPower.DiagonalCartierFrames
public import ToricPower.SchemeInternalDual
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# The canonical exterior product of actual sections

A section is its actual morphism from the structure sheaf. Pulling back
these morphisms and tensoring them defines the exterior section. All maps
are linear for the scheme's specified base field, and the comparison is
natural in both sheaf factors.
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

section Tensor

variable (Z : Scheme.{u}) [Z.Over (Spec (.of k))]

local instance externalSectionsMonoidalLinear : MonoidalLinear k Z.Modules where
  whiskerLeft_smul := by
    intro P Q R a f
    exact (tensorLeft P).map_smul a f
  smul_whiskerRight := by
    intro a P Q f R
    exact (tensorRight R).map_smul a f

/-- Tensoring two unit-source morphisms is bilinear. -/
def moduleTensorUnitHomBilinear (P Q : Z.Modules) :
    (𝟙_ Z.Modules ⟶ P) →ₗ[k] (𝟙_ Z.Modules ⟶ Q) →ₗ[k]
      (𝟙_ Z.Modules ⟶ P ⊗ Q) where
  toFun f :=
    { toFun := fun g => (λ_ (𝟙_ Z.Modules)).inv ≫ (f ⊗ₘ g)
      map_add' := fun g h => by
        rw [MonoidalPreadditive.tensor_add, Preadditive.comp_add]
      map_smul' := fun a g => by
        simp only [tensorHom_def, MonoidalLinear.whiskerLeft_smul, Linear.comp_smul, RingHom.id_apply] }
  map_add' f g := by
    apply LinearMap.ext
    intro h
    change (λ_ (𝟙_ Z.Modules)).inv ≫ ((f+g) ⊗ₘ h) =
      (λ_ (𝟙_ Z.Modules)).inv ≫ (f ⊗ₘ h) + (λ_ (𝟙_ Z.Modules)).inv ≫ (g ⊗ₘ h)
    rw [MonoidalPreadditive.add_tensor, Preadditive.comp_add]
  map_smul' a f := by
    apply LinearMap.ext
    intro g
    change (λ_ (𝟙_ Z.Modules)).inv ≫ ((a • f) ⊗ₘ g) =
      a • ((λ_ (𝟙_ Z.Modules)).inv ≫ (f ⊗ₘ g))
    simp only [tensorHom_def, MonoidalLinear.smul_whiskerRight, Linear.smul_comp, Linear.comp_smul]

end Tensor

section Pullback

variable {Z X : Scheme.{u}} [Z.Over (Spec (.of k))] [X.Over (Spec (.of k))]
  (f : Z ⟶ X) [f.IsOver (Spec (.of k))]

/-- Pullback of a unit-source morphism uses the actual structure-sheaf
comparison, rather than a chosen identification of objects. -/
def schemePullbackUnitHomLinearMap (L : X.Modules) :
    (𝟙_ X.Modules ⟶ L) →ₗ[k] (𝟙_ Z.Modules ⟶ (Scheme.Modules.pullback f).obj L) :=
  (Linear.leftComp k ((Scheme.Modules.pullback f).obj L)
    (Scheme.Modules.pullbackObjUnitIso f).inv).comp
      ((Scheme.Modules.pullback f).mapLinearMap k)

theorem schemePullbackUnitHomLinearMap_naturality {L L' : X.Modules}
    (a : L ⟶ L') (s : 𝟙_ X.Modules ⟶ L) :
    schemePullbackUnitHomLinearMap k f L' (s ≫ a) =
      schemePullbackUnitHomLinearMap k f L s ≫ (Scheme.Modules.pullback f).map a := by
  change (Scheme.Modules.pullbackObjUnitIso f).inv ≫
      (Scheme.Modules.pullback f).map (s ≫ a) = _
  rw [Functor.map_comp]
  exact (Category.assoc _ _ _).symm

end Pullback

section Sections

variable {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
  (f : Z ⟶ X) (g : Z ⟶ Y)
  [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
  (L : X.Modules) (M : Y.Modules)

/-- The literal exterior sheaf along the two specified maps. -/
abbrev schemeExteriorSheaf : Z.Modules :=
  (Scheme.Modules.pullback f).obj L ⊗ (Scheme.Modules.pullback g).obj M

/-- The canonical exterior product of two actual sections. -/
def schemeExternalSection
    (s : (FiniteCover.schemeBaseSections k X ⊤).obj L)
    (t : (FiniteCover.schemeBaseSections k Y ⊤).obj M) :
    (FiniteCover.schemeBaseSections k Z ⊤).obj (schemeExteriorSheaf f g L M) :=
  moduleUnitActualSectionsLinearEquiv k Z _
    (moduleTensorUnitHomBilinear k Z _ _
      (schemePullbackUnitHomLinearMap k f L
        ((moduleUnitActualSectionsLinearEquiv k X L).symm s))
      (schemePullbackUnitHomLinearMap k g M
        ((moduleUnitActualSectionsLinearEquiv k Y M).symm t)))

/-- The canonical map from the tensor product of section spaces. -/
def schemeExternalSectionsLinearMap :
    (FiniteCover.schemeBaseSections k X ⊤).obj L ⊗[k]
      (FiniteCover.schemeBaseSections k Y ⊤).obj M →ₗ[k]
        (FiniteCover.schemeBaseSections k Z ⊤).obj (schemeExteriorSheaf f g L M) :=
  (moduleUnitActualSectionsLinearEquiv k Z _).toLinearMap.comp
    (TensorProduct.lift
      ((moduleTensorUnitHomBilinear k Z _ _).compl₁₂
        ((schemePullbackUnitHomLinearMap k f L).comp
          (moduleUnitActualSectionsLinearEquiv k X L).symm.toLinearMap)
        ((schemePullbackUnitHomLinearMap k g M).comp
          (moduleUnitActualSectionsLinearEquiv k Y M).symm.toLinearMap)))

@[simp]
theorem schemeExternalSectionsLinearMap_tmul
    (s : (FiniteCover.schemeBaseSections k X ⊤).obj L)
    (t : (FiniteCover.schemeBaseSections k Y ⊤).obj M) :
    schemeExternalSectionsLinearMap k f g L M (s ⊗ₜ[k] t) =
      schemeExternalSection k f g L M s t := rfl

omit f g L M in
/-- Unit-source coordinates retain every actual target morphism. -/
theorem moduleUnitActualSectionsLinearEquiv_symm_naturality
    {L L' : X.Modules} (a : L ⟶ L')
    (s : (FiniteCover.schemeBaseSections k X ⊤).obj L) :
    (moduleUnitActualSectionsLinearEquiv k X L').symm
        ((FiniteCover.schemeBaseSections k X ⊤).map a s) =
      (moduleUnitActualSectionsLinearEquiv k X L).symm s ≫ a := by
  apply (moduleUnitActualSectionsLinearEquiv k X L').injective
  rw [LinearEquiv.apply_symm_apply]
  change a.app ⊤ s = a.app ⊤
    (moduleUnitActualSectionsLinearEquiv k X L
      ((moduleUnitActualSectionsLinearEquiv k X L).symm s))
  rw [LinearEquiv.apply_symm_apply]

/-- Exterior sections commute with maps in both factors simultaneously. -/
theorem schemeExternalSection_naturality {L' : X.Modules} {M' : Y.Modules}
    (a : L ⟶ L') (b : M ⟶ M')
    (s : (FiniteCover.schemeBaseSections k X ⊤).obj L)
    (t : (FiniteCover.schemeBaseSections k Y ⊤).obj M) :
    schemeExternalSection k f g L' M'
      ((FiniteCover.schemeBaseSections k X ⊤).map a s)
      ((FiniteCover.schemeBaseSections k Y ⊤).map b t) =
    (FiniteCover.schemeBaseSections k Z ⊤).map
      ((Scheme.Modules.pullback f).map a ⊗ₘ (Scheme.Modules.pullback g).map b)
      (schemeExternalSection k f g L M s t) := by
  unfold schemeExternalSection
  rw [moduleUnitActualSectionsLinearEquiv_symm_naturality,
    moduleUnitActualSectionsLinearEquiv_symm_naturality,
    schemePullbackUnitHomLinearMap_naturality,
    schemePullbackUnitHomLinearMap_naturality]
  change moduleUnitActualSectionsLinearEquiv k Z _
      ((λ_ (𝟙_ Z.Modules)).inv ≫
        ((schemePullbackUnitHomLinearMap k f L _ ≫ (Scheme.Modules.pullback f).map a) ⊗ₘ
          (schemePullbackUnitHomLinearMap k g M _ ≫ (Scheme.Modules.pullback g).map b))) = _
  rw [← tensorHom_comp_tensorHom, ← Category.assoc]
  rfl

end Sections

end ToricPower

end
