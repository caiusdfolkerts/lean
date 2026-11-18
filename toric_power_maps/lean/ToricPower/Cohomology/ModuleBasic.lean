module

public import ToricPower.Cohomology.ModuleMaps

/-! Linearity of actual sheaf cohomology maps and of the degree-zero
identification with global sections. -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Scheme.Modules Opposite

namespace TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

variable {X : Scheme.{u}} {M N : X.Modules}

/-- The map on cohomology induced by a morphism of coefficient sheaves is linear over global
functions. -/
def _root_.AlgebraicGeometry.Scheme.Modules.cohomologyMapLinear
    (f : M ⟶ N) (i : ℕ) :
    Cohomology M i →ₗ[Γ(X, ⊤)] Cohomology N i :=
  ToricPower.linearMapOfAddHomScalar (R := Γ(X, ⊤))
    (A := Cohomology M i) (B := Cohomology N i) (cohomologyMapAddHom f i)
    (fun r => cohomologyMapAddHom (globalSectionsSmul M r) i)
    (fun r => cohomologyMapAddHom (globalSectionsSmul N r) i)
    (cohomologyMapAddHom_scalar M i) (cohomologyMapAddHom_scalar N i)
    (fun r x => DFunLike.congr_fun (cohomologyMapAddHom_commutes f i r) x)

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyMapLinear_apply
    (f : M ⟶ N) (i : ℕ) (x : Cohomology M i) :
    cohomologyMapLinear f i x = (cohomologyFunctor X i).map f x :=
  by rfl

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyMapLinear_id
    (M : X.Modules) (i : ℕ) :
    cohomologyMapLinear (𝟙 M) i = LinearMap.id := by
  apply LinearMap.ext
  exact (cohomologyFunctor X i).map_id_apply M

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyMapLinear_comp
    {P : X.Modules} (f : M ⟶ N) (g : N ⟶ P) (i : ℕ) :
    cohomologyMapLinear (f ≫ g) i =
      (cohomologyMapLinear g i).comp (cohomologyMapLinear f i) := by
  apply LinearMap.ext
  exact (cohomologyFunctor X i).map_comp_apply f g

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyMapLinear_zero
    (M N : X.Modules) (i : ℕ) :
    cohomologyMapLinear (0 : M ⟶ N) i = 0 := by
  apply LinearMap.ext
  intro x
  simp only [cohomologyMapLinear_apply, LinearMap.zero_apply]
  rw [CategoryTheory.Functor.map_zero]
  rfl

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyMapLinear_add
    (f g : M ⟶ N) (i : ℕ) :
    cohomologyMapLinear (f + g) i = cohomologyMapLinear f i + cohomologyMapLinear g i := by
  apply LinearMap.ext
  intro x
  simp only [cohomologyMapLinear_apply, LinearMap.add_apply]
  rw [CategoryTheory.Functor.map_add]
  rfl


/-- The canonical identification of zeroth cohomology with global sections is linear over global
functions. -/
def _root_.AlgebraicGeometry.Scheme.Modules.cohomologyZeroLinearEquiv
    (M : X.Modules) :
    Cohomology M 0 ≃ₗ[Γ(X, ⊤)] Γ(M, ⊤) where
  __ := cohomologyZeroEquiv M
  map_smul' r x := by
    -- The inherited linear-equivalence fields have no accessor lemmas for their actions;
    -- normalize them to the named cohomology and section operations.
    change cohomologyZeroEquiv M (r • x) = r • cohomologyZeroEquiv M x
    rw [cohomology_smul, cohomologyZeroEquiv_naturality]
    rw [globalSectionsSmul_app]
    have h : X.presheaf.map (⊤ : X.Opens).leTop.op r = r := by
      have hf : (⊤ : X.Opens).leTop.op = 𝟙 (Opposite.op (⊤ : X.Opens)) :=
        Subsingleton.elim _ _
      rw [hf]
      exact ConcreteCategory.congr_hom (X.presheaf.map_id _) r
    rw [h]
    exact M.smul_apply r (cohomologyZeroEquiv M x)


@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyZeroLinearEquiv_apply
    (M : X.Modules) (x : Cohomology M 0) :
    cohomologyZeroLinearEquiv M x = cohomologyZeroEquiv M x :=
  by rfl

end TauCeti.AlgebraicGeometry.Scheme.Modules

end
