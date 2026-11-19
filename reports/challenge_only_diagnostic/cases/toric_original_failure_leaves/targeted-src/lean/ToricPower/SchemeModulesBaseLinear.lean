module

public import ToricPower.CartierCore
public import Mathlib.CategoryTheory.Linear.Basic

/-!
# The actual base-ring linearity of scheme module sheaves

For a scheme over `Spec R`, the scalar action on a sheaf morphism is
postcomposition with multiplication by the corresponding global function.
The two composition laws follow from naturality of that multiplication.
Thus signed or scalar-weighted matrices of actual sheaf morphisms can be
formed in Mathlib's ordinary linear-category interface.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable (R : Type u) [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))]

/-- The usual base-ring module structure on actual sheaf morphisms. -/
def baseHomModule (M N : X.Modules) : Module R (M ⟶ N) where
  smul r f := f ≫ globalSectionsSmul N (baseRingToGlobalSections R X r)
  one_smul f := by
    change f ≫ globalSectionsSmul N (baseRingToGlobalSections R X 1) = f
    rw [map_one, globalSectionsSmul_one, Category.comp_id]
  mul_smul r s f := by
    change f ≫ globalSectionsSmul N (baseRingToGlobalSections R X (r * s)) =
      (f ≫ globalSectionsSmul N (baseRingToGlobalSections R X s)) ≫
        globalSectionsSmul N (baseRingToGlobalSections R X r)
    rw [map_mul, globalSectionsSmul_mul, Category.assoc]
  smul_zero r := by
    change (0 : M ⟶ N) ≫ globalSectionsSmul N (baseRingToGlobalSections R X r) = 0
    simp only [zero_comp]
  smul_add r f g := by
    change (f + g) ≫ globalSectionsSmul N (baseRingToGlobalSections R X r) = _
    exact Preadditive.add_comp _ _ _ _ _ _
  add_smul r s f := by
    change f ≫ globalSectionsSmul N (baseRingToGlobalSections R X (r + s)) =
      f ≫ globalSectionsSmul N (baseRingToGlobalSections R X r) +
        f ≫ globalSectionsSmul N (baseRingToGlobalSections R X s)
    rw [map_add, globalSectionsSmul_add, Preadditive.comp_add]
  zero_smul f := by
    change f ≫ globalSectionsSmul N (baseRingToGlobalSections R X 0) = 0
    rw [map_zero, globalSectionsSmul_zero, comp_zero]

/-- The category of genuine module sheaves is linear over the actual base
ring of the scheme. -/
instance baseLinear : Linear R X.Modules where
  homModule := baseHomModule R X
  smul_comp M N P r f g := by
    change (f ≫ globalSectionsSmul N (baseRingToGlobalSections R X r)) ≫ g =
      (f ≫ g) ≫ globalSectionsSmul P (baseRingToGlobalSections R X r)
    simp only [Category.assoc, globalSectionsSmul_naturality]
  comp_smul M N P f r g := by
    change f ≫ (g ≫ globalSectionsSmul P (baseRingToGlobalSections R X r)) =
      (f ≫ g) ≫ globalSectionsSmul P (baseRingToGlobalSections R X r)
    simp only [Category.assoc]

/-- This scalar action is the ordinary multiplication action on the target
sheaf, rather than an independently postulated enrichment. -/
theorem base_smul_eq {M N : X.Modules} (r : R) (f : M ⟶ N) :
    r • f = f ≫ globalSectionsSmul N (baseRingToGlobalSections R X r) := rfl

@[simp]
theorem base_smul_app {M N : X.Modules} (r : R) (f : M ⟶ N)
    (U : X.Opens) (s : Γ(M, U)) :
    (r • f).app U s =
      X.presheaf.map U.leTop.op (baseRingToGlobalSections R X r) • f.app U s := by
  rw [base_smul_eq]
  change (globalSectionsSmul N (baseRingToGlobalSections R X r)).app U (f.app U s) = _
  rw [globalSectionsSmul_app]
  rfl

@[simp]
theorem base_smul_id (M : X.Modules) (r : R) :
    r • 𝟙 M = globalSectionsSmul M (baseRingToGlobalSections R X r) := by
  rw [base_smul_eq, Category.id_comp]

end AlgebraicGeometry.Scheme.Modules

end
