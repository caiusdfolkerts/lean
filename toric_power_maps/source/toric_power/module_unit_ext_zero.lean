module

public import ToricPower.ModuleUnitSections
public import ToricPower.Cohomology.ModuleBase
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

/-! The degree-zero module Ext / sheaf-cohomology comparison and its
naturality in the actual coefficient sheaf. -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
  CategoryTheory.Abelian MonoidalCategory Opposite TopologicalSpace

namespace ToricPower

universe u

variable (k : Type u) [CommRing k] (X : Scheme.{u}) [X.Over (Spec (.of k))]

local instance moduleZeroHasExt : HasExt.{u} X.Modules :=
  hasExt_of_enoughInjectives X.Modules

/-- Degree zero is the actual identification with global sections on
both sides, not an independently specified vector-space isomorphism. -/
def moduleUnitExtZeroCohomology (M : X.Modules) :
    Ext.{u} (𝟙_ X.Modules) M 0 ≃ₗ[k] TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology M 0 :=
  (Ext.linearEquiv₀ (R := k)).trans
    ((moduleUnitSectionsLinearEquiv k X M).trans
      (Scheme.Modules.cohomologyZeroBaseLinearEquiv k X M).symm)

@[simp]
theorem moduleExtLinearEquivZero_mk {M N : X.Modules} (f : M ⟶ N) :
    Ext.linearEquiv₀ (R := k) (Ext.mk₀ f) = f :=
  (Ext.mk₀_bijective M N).1 (Ext.mk₀_linearEquiv₀_apply _)

theorem moduleUnitExtZeroCohomology_naturality {M N : X.Modules}
    (f : M ⟶ N) (x : Ext.{u} (𝟙_ X.Modules) M 0) :
    moduleUnitExtZeroCohomology k X N (x.comp (Ext.mk₀ f) (add_zero 0)) =
      Scheme.Modules.cohomologyMapBaseLinear k X f 0
        (moduleUnitExtZeroCohomology k X M x) := by
  apply (Scheme.Modules.cohomologyZeroBaseLinearEquiv k X N).injective
  rw [Scheme.Modules.cohomologyZeroBaseLinearEquiv_naturality]
  obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective (𝟙_ X.Modules) M).2 x
  simp only [Ext.mk₀_comp_mk₀, moduleUnitExtZeroCohomology,
    LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    moduleExtLinearEquivZero_mk, moduleUnitSectionsLinearEquiv_apply,
    Scheme.Modules.Hom.comp_app, ModuleCat.comp_apply]
  rfl


end ToricPower

end
