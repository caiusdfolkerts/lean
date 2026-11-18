module

public import ToricPower.Cohomology.ModuleAction

/-! The maps on actual sheaf cohomology, read directly as additive maps.
These lemmas keep the categorical wrapper out of scalar-linearity proofs. -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory Opposite
open TauCeti.AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X : Scheme.{u}} {M N P : X.Modules}

/-- The genuine cohomology map as an additive homomorphism. -/
abbrev cohomologyMapAddHom (f : M ⟶ N) (i : ℕ) : Cohomology M i →+ Cohomology N i :=
  ((cohomologyFunctor X i).map f).hom

@[simp]
theorem cohomologyMapAddHom_apply (f : M ⟶ N) (i : ℕ) (x : Cohomology M i) :
    cohomologyMapAddHom f i x = (cohomologyFunctor X i).map f x := rfl

@[simp]
theorem cohomologyMapAddHom_comp (f : M ⟶ N) (g : N ⟶ P) (i : ℕ) :
    cohomologyMapAddHom (f ≫ g) i =
      (cohomologyMapAddHom g i).comp (cohomologyMapAddHom f i) := by
  ext x
  exact (cohomologyFunctor X i).map_comp_apply f g x

/-- Commuting scalar endomorphisms induce commuting actual cohomology maps. -/
theorem cohomologyMapAddHom_commutes (f : M ⟶ N) (i : ℕ) (r : Γ(X, ⊤)) :
    (cohomologyMapAddHom f i).comp (cohomologyMapAddHom (globalSectionsSmul M r) i) =
      (cohomologyMapAddHom (globalSectionsSmul N r) i).comp (cohomologyMapAddHom f i) := by
  rw [← cohomologyMapAddHom_comp, ← cohomologyMapAddHom_comp, globalSectionsSmul_naturality]

/-- Canonical scalars on actual cohomology are induced by scalar sheaf maps. -/
theorem cohomologyMapAddHom_scalar (M : X.Modules) (i : ℕ) (r : Γ(X, ⊤))
    (x : Cohomology M i) : r • x = cohomologyMapAddHom (globalSectionsSmul M r) i x :=
  cohomology_smul M i r x

end AlgebraicGeometry.Scheme.Modules
