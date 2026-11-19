module

public import ToricPower.Cohomology.SchemeExact
public import ToricPower.Cohomology.SheafFunctorNaturality

/-! The connecting homomorphism in genuine sheaf cohomology respects the
canonical scalar action, by naturality for scalar sheaf endomorphisms. -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Scheme.Modules

namespace TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

variable {X : Scheme.{u}} {S : ShortComplex X.Modules} (hS : S.ShortExact)
include hS

omit hS in
/-- Multiplication by a global function on cohomology is the map induced by multiplication by
that function on the coefficient sheaf. -/
@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyMap_globalSectionsSmul_apply (M : X.Modules)
    (i : ℕ) (r : Γ(X, ⊤)) (x : Cohomology M i) :
    cohomologyMap (globalSectionsSmul M r) i x = r • x :=
  (cohomology_smul M i r x).symm

omit hS in
/-- The connecting map is natural in the short exact sequence: a morphism `φ : S₁ ⟶ S₂` of short
exact sequences of sheaves of modules makes the square formed by the two connecting maps and the
maps induced by `φ.τ₃` and `φ.τ₁` commute. -/
theorem cohomologyδ_naturality {S₁ S₂ : ShortComplex X.Modules} (h₁ : S₁.ShortExact)
    (h₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (x : Cohomology S₁.X₃ n₀) :
    cohomologyMap φ.τ₁ n₁ (cohomologyδ h₁ n₀ n₁ h x) =
      cohomologyδ h₂ n₀ n₁ h (cohomologyMap φ.τ₃ n₀ x) :=
  ToricPower.SheafCohomology.functorConnectingMap_naturality.{u, u, u, u + 1, u}
    (toSheaf X) (S₁ := S₁) (S₂ := S₂) (shortExact_map_toSheaf h₁)
    (shortExact_map_toSheaf h₂) φ n₀ n₁ h x

/-- The connecting map of the long exact cohomology sequence is linear over the ring of global
functions. -/
def cohomologyδLinear (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Cohomology S.X₃ n₀ →ₗ[Γ(X, ⊤)] Cohomology S.X₁ n₁ where
  toFun := cohomologyδ hS n₀ n₁ h
  map_add' := map_add _
  map_smul' r x := by
    -- `Module.compHom` exposes its action definitionally, so the goal is the naturality of the
    -- connecting map for multiplication by `r` on all three terms.
    change cohomologyδ hS n₀ n₁ h (r • x) = r • cohomologyδ hS n₀ n₁ h x
    rw [← cohomologyMap_globalSectionsSmul_apply, ← cohomologyMap_globalSectionsSmul_apply]
    -- Multiplication by `r` on all three terms is an endomorphism of the short complex.
    exact (cohomologyδ_naturality hS hS
      { τ₁ := globalSectionsSmul S.X₁ r
        τ₂ := globalSectionsSmul S.X₂ r
        τ₃ := globalSectionsSmul S.X₃ r
        comm₁₂ := globalSectionsSmul_naturality S.f r
        comm₂₃ := globalSectionsSmul_naturality S.g r } n₀ n₁ h x).symm

@[simp]
lemma cohomologyδLinear_apply (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (x : Cohomology S.X₃ n₀) :
    cohomologyδLinear hS n₀ n₁ h x = cohomologyδ hS n₀ n₁ h x :=
  (rfl)

end TauCeti.AlgebraicGeometry.Scheme.Modules

end
