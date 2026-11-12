module

public import ToricPower.ModuleUnitExtCohomology

/-!
# Actual connecting-map naturality for module Ext

Chosen injective embeddings need not be functorial. Every actual coefficient
map nevertheless extends to a morphism of their short exact cokernel
sequences, by injectivity. This suffices to compare dimension shifts without
assuming that choices of injective objects form a functor.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
  CategoryTheory.Abelian MonoidalCategory Opposite TopologicalSpace

namespace ToricPower

universe u

variable (k : Type u) [CommRing k] (X : Scheme.{u}) [X.Over (Spec (.of k))]

local instance moduleNaturalHasExt : HasExt.{u} X.Modules :=
  hasExt_of_enoughInjectives X.Modules

/-- Naturality of the literal Ext connecting map follows from naturality
of the extension class of the actual short exact sequence. -/
theorem moduleExtConnecting_naturality
    {S T : ShortComplex X.Modules} (hS : S.ShortExact) (hT : T.ShortExact)
    (f : S ⟶ T) (P : X.Modules) (n : ℕ) (x : Ext.{u} P S.X₃ n) :
    (moduleExtConnecting k X hS P n x).comp (Ext.mk₀ f.τ₁) (add_zero _) =
      moduleExtConnecting k X hT P n (x.comp (Ext.mk₀ f.τ₃) (add_zero _)) := by
  change (x.comp hS.extClass rfl).comp (Ext.mk₀ f.τ₁) (add_zero _) =
    (x.comp (Ext.mk₀ f.τ₃) (add_zero _)).comp hT.extClass rfl
  rw [Ext.comp_assoc_of_third_deg_zero, hS.extClass_naturality hT f,
    Ext.comp_assoc_of_second_deg_zero]

/-- Extend a coefficient map to the two chosen injective cokernel sequences.
This is a comparison morphism, not an assertion of functorial choices. -/
def moduleInjectiveCokernelComparison {M N : X.Modules} (f : M ⟶ N) :
    TauCeti.injectiveCokernelSequence M ⟶ TauCeti.injectiveCokernelSequence N := by
  let g := Injective.factorThru (f ≫ Injective.ι N) (Injective.ι M)
  have hg : Injective.ι M ≫ g = f ≫ Injective.ι N :=
    Injective.comp_factorThru (f ≫ Injective.ι N) (Injective.ι M)
  exact
    { τ₁ := f
      τ₂ := g
      τ₃ := cokernel.map (Injective.ι M) (Injective.ι N) f g hg
      comm₁₂ := hg.symm
      comm₂₃ := (cokernel.π_desc _ _ _).symm }

@[simp]
theorem moduleInjectiveCokernelComparison_τ₁ {M N : X.Modules} (f : M ⟶ N) :
    (moduleInjectiveCokernelComparison X f).τ₁ = f := rfl

/-- The explicit degree-one comparison carries the actual Ext boundary
to the actual sheaf-cohomology boundary. -/
theorem moduleUnitExtOneCohomologyOfShortExact_connecting
    {S : ShortComplex X.Modules} (hS : S.ShortExact) [Injective S.X₂]
    (x : Ext.{u} (𝟙_ X.Modules) S.X₃ 0) :
    moduleUnitExtOneCohomologyOfShortExact k X hS
        (moduleExtConnecting k X hS (𝟙_ X.Modules) 0 x) =
      TauCeti.AlgebraicGeometry.Scheme.Modules.cohomologyδ hS 0 1 rfl
        (moduleUnitExtZeroCohomology k X S.X₃ x) := by
  simp only [moduleUnitExtOneCohomologyOfShortExact, LinearEquiv.trans_apply,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk, LinearMap.comp_apply,
    LinearEquiv.coe_coe,
    TauCeti.AlgebraicGeometry.Scheme.Modules.cohomologyδBaseLinear_apply]

/-- The positive-degree comparison also carries the literal boundaries
to one another, for any given lower-degree comparison. -/
theorem moduleUnitExtHigherStep_connecting
    {S : ShortComplex X.Modules} (hS : S.ShortExact) [Injective S.X₂] (n : ℕ)
    (e : Ext.{u} (𝟙_ X.Modules) S.X₃ (n+1) ≃ₗ[k]
      TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology S.X₃ (n+1))
    (x : Ext.{u} (𝟙_ X.Modules) S.X₃ (n+1)) :
    moduleUnitExtHigherStep k X hS n e
        (moduleExtConnecting k X hS (𝟙_ X.Modules) (n+1) x) =
      TauCeti.AlgebraicGeometry.Scheme.Modules.cohomologyδ hS (n+1) (n+2) rfl (e x) := by
  change (TauCeti.AlgebraicGeometry.Scheme.Modules.cohomologySuccLinearEquivOfIsFlasque
    k hS n) (e ((moduleExtConnectingIso k X hS (𝟙_ X.Modules) n).symm
      ((moduleExtConnectingIso k X hS (𝟙_ X.Modules) n) x))) = _
  rw [LinearEquiv.symm_apply_apply]
  exact TauCeti.AlgebraicGeometry.Scheme.Modules.cohomologySuccLinearEquivOfIsFlasque_apply
    k hS n (e x)

end ToricPower

end
