module

public import ToricPower.Cohomology.SchemeLongExactSequence
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Finite-dimensionality for actual base-linear sheaf cohomology

The canonical scalar action is kept throughout finite direct sums and
the long exact sequence. In particular, additive-group isomorphisms are
never used to transfer a dimension statement.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open TauCeti.AlgebraicGeometry.Scheme.Modules

namespace ToricPower

universe u v w

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]

/-- Ordinary sheaf cohomology with its proved canonical base-linear maps. -/
def cohomologyBaseFunctor (degree : ℕ) : X.Modules ⥤ ModuleCat.{u} k where
  obj M := ModuleCat.of k (Cohomology M degree)
  map f := ModuleCat.ofHom (Scheme.Modules.cohomologyMapBaseLinear k X f degree)
  map_id M := by
    apply ModuleCat.hom_ext
    exact Scheme.Modules.cohomologyMapBaseLinear_id k X M degree
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact Scheme.Modules.cohomologyMapBaseLinear_comp k X f g degree

instance (degree : ℕ) : (cohomologyBaseFunctor k X degree).Additive where
  map_add := by
    intro M P f g
    apply ModuleCat.hom_ext
    exact Scheme.Modules.cohomologyMapBaseLinear_add k X f g degree

omit X in
/-- A finite categorical module biproduct is finite-dimensional whenever
its summands are, even if its finite index lies in a larger universe. -/
theorem finiteDimensional_module_biproduct {J : Type v} [Finite J]
    (family : J → ModuleCat.{u} k) (finite : ∀ j, FiniteDimensional k (family j)) :
    FiniteDimensional k (⨁ family : ModuleCat.{u} k) := by
  classical
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  let reindexed : Fin n → ModuleCat.{u} k := fun a => family (e.symm a)
  letI (a : Fin n) : FiniteDimensional k (reindexed a) := finite (e.symm a)
  let comparison : (⨁ family) ≅ ⨁ reindexed :=
    biproduct.whiskerEquiv e (fun a => eqToIso (by simp [reindexed]))
  letI : FiniteDimensional k (⨁ reindexed : ModuleCat.{u} k) :=
    Module.Finite.equiv (ModuleCat.biproductIsoPi reindexed).toLinearEquiv.symm
  exact Module.Finite.equiv comparison.toLinearEquiv.symm

/-- Finite-dimensionality of actual cohomology is preserved by finite
direct sums through an actual base-linear biproduct comparison. -/
theorem finiteDimensional_cohomology_biproduct {J : Type v} [Finite J]
    (family : J → X.Modules) (degree : ℕ)
    (finite : ∀ j, FiniteDimensional k (Cohomology (family j) degree)) :
    FiniteDimensional k (Cohomology (⨁ family) degree) := by
  classical
  letI : Fintype J := Fintype.ofFinite J
  let F := cohomologyBaseFunctor k X degree
  letI : PreservesBiproduct family F := by
    constructor
    intro b hb
    refine ⟨isBilimitOfTotal _ ?_⟩
    change (∑ j : J, F.map (b.π j) ≫ F.map (b.ι j)) = 𝟙 (F.obj b.pt)
    simp_rw [← F.map_comp]
    erw [← F.map_sum, ← F.map_id, IsBilimit.total hb]
  letI : FiniteDimensional k (⨁ F.obj ∘ family : ModuleCat.{u} k) :=
    finiteDimensional_module_biproduct k (F.obj ∘ family) finite
  exact Module.Finite.equiv (F.mapBiproduct family).toLinearEquiv.symm

/-- In a short exact sequence, the quotient's degree-`n` cohomology is
squeezed between the middle term's degree `n` and the kernel's degree
`n+1`. Both connecting and coefficient maps are the actual linear maps. -/
theorem finiteDimensional_cohomology_quotient {S : ShortComplex X.Modules}
    (exactSequence : S.ShortExact) (degree : ℕ)
    [FiniteDimensional k (Cohomology S.X₂ degree)]
    [FiniteDimensional k (Cohomology S.X₁ (degree + 1))] :
    FiniteDimensional k (Cohomology S.X₃ degree) := by
  apply TauCeti.finiteDimensional_of_exact
    (f := Scheme.Modules.cohomologyMapBaseLinear k X S.g degree)
    (g := cohomologyδBaseLinear k X exactSequence degree (degree + 1) rfl)
  have coefficientMap : ⇑(Scheme.Modules.cohomologyMapBaseLinear k X S.g degree) =
      ⇑(cohomologyMap S.g degree) := by
    funext x
    rw [Scheme.Modules.cohomologyMapBaseLinear_apply, cohomologyFunctor_map]
    rfl
  rw [coefficientMap]
  exact exact_cohomologyMap_cohomologyδ exactSequence degree (degree + 1) rfl

end ToricPower

end
