module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Naturality of exact Ext adjunction in the adjoint pair

Changing a left adjoint changes its Ext source. The corresponding map
on the right is the actual conjugate natural transformation between the
right adjoints. This statement supplies the source-variable naturality
needed when Cartier tensor adjunctions are compared along actual sheaf
morphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace ToricPower

universe w₁ w₂ v₁ v₂ u₁ u₂

section Mates

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]
  {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

/-- An actual transformation of right adjoints is the conjugate of a
given transformation of left adjoints precisely when the counit square
commutes. Only the implication needed for concrete identifications is
recorded here. -/
theorem conjugateEquiv_eq_of_counit (α : L₂ ⟶ L₁) (β : R₁ ⟶ R₂)
    (compatible : ∀ Y, L₂.map (β.app Y) ≫ adj₂.counit.app Y =
      α.app (R₁.obj Y) ≫ adj₁.counit.app Y) :
    conjugateEquiv adj₁ adj₂ α = β := by
  ext Y
  apply (adj₂.homEquiv (R₁.obj Y) Y).symm.injective
  rw [adj₂.homEquiv_counit, adj₂.homEquiv_counit,
    conjugateEquiv_counit, compatible]

end Mates

section Ext

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D] [Abelian C] [Abelian D]
  [HasExt.{w₁} C] [HasExt.{w₂} D]
  {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
  [L₁.Additive] [L₂.Additive] [R₁.Additive] [R₂.Additive]
  [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
  [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
  [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
  [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

/-- Exact Ext adjunction intertwines a change of left adjoint with the
actual conjugate map of right adjoints, in every degree. -/
theorem extEquiv_conjugate (α : L₂ ⟶ L₁) {X : C} {Y : D} {n : ℕ}
    (e : Ext (L₁.obj X) Y n) :
    adj₂.extEquiv ((Ext.mk₀ (α.app X)).comp e (zero_add n)) =
      (adj₁.extEquiv e).comp
        (Ext.mk₀ ((conjugateEquiv adj₁ adj₂ α).app Y)) (add_zero n) := by
  rw [Adjunction.extEquiv_apply, Adjunction.extEquiv_apply,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.mk₀_comp_mk₀_assoc, ← unit_conjugateEquiv adj₁ adj₂ α X,
    ← Ext.mk₀_comp_mk₀_assoc, Ext.comp_assoc_of_third_deg_zero,
    Ext.mapExactFunctor_comp_mk₀_natTransApp]

end Ext

end ToricPower
