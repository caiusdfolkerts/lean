module

public import ToricPower.SchemeModulesBaseLinear
public import TauCeti.AlgebraicGeometry.Modules.TensorProduct

/-! The actual scalar-linear identification between maps from the structure
sheaf and global sections, with the unit-section evaluation formula. -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
  CategoryTheory.Abelian MonoidalCategory Opposite TopologicalSpace

namespace ToricPower

universe u

variable (k : Type u) [CommRing k] (X : Scheme.{u}) [X.Over (Spec (.of k))]

/-- A literal global section gives the compatible family of all its
restrictions used by the ordinary unit-Hom equivalence. -/
def moduleSectionFamily (M : X.Modules) (s : Γ(M, ⊤)) : M.sections :=
  ⟨fun U => M.val.map U.unop.leTop.op s, by
    intro U V f
    change M.val.map f (M.val.map U.unop.leTop.op s) =
      M.val.map V.unop.leTop.op s
    rw [← PresheafOfModules.map_comp_apply]
    congr 1⟩

/-- The ordinary unit-source Hom equivalence, with its actual base-ring
linear structure and its value at the unit section. -/
def moduleUnitSectionsLinearEquiv (M : X.Modules) :
    (𝟙_ X.Modules ⟶ M) ≃ₗ[k] Γ(M, ⊤) where
  toFun f := f.app ⊤ (1 : Γ(X, ⊤))
  invFun s := M.unitHomEquiv.symm (moduleSectionFamily X M s)
  left_inv f := by
    apply M.unitHomEquiv.injective
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    funext U
    change M.val.map U.unop.leTop.op (f.app ⊤ (1 : Γ(X, ⊤))) =
      f.app U.unop (1 : Γ(X, U.unop))
    have h := PresheafOfModules.naturality_apply f.val U.unop.leTop.op (1 : Γ(X, ⊤))
    exact h.symm.trans (congrArg (fun z => f.app U.unop z)
      (PresheafOfModules.unit_map_one (R := X.ringCatSheaf.obj) U.unop.leTop.op))
  right_inv s := by
    change (M.unitHomEquiv (M.unitHomEquiv.symm (moduleSectionFamily X M s))).val
      (op ⊤) = s
    rw [Equiv.apply_symm_apply]
    change M.val.map (𝟙 (op ⊤)) s = s
    exact ConcreteCategory.congr_hom (M.presheaf.map_id (op ⊤)) s
  map_add' f g := rfl
  map_smul' r f := by
    rw [Scheme.Modules.base_smul_app, Scheme.Modules.base_smul_globalSections]
    change X.presheaf.map (𝟙 (op ⊤))
      (Scheme.Modules.baseRingToGlobalSections k X r) • f.app ⊤ (1 : Γ(X, ⊤)) = _
    simp

@[simp]
theorem moduleUnitSectionsLinearEquiv_apply (M : X.Modules)
    (f : 𝟙_ X.Modules ⟶ M) :
    moduleUnitSectionsLinearEquiv k X M f = f.app ⊤ (1 : Γ(X, ⊤)) := rfl


end ToricPower

end
