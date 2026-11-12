module

public import ToricPower.ModuleExtNaturality

/-!
# Naturality of the actual module Ext / cohomology comparison

The all-degree isomorphisms respect every actual map of coefficient sheaves.
The proof compares the two chosen injective embeddings using an actual
morphism of short exact sequences and then uses naturality of their
connecting maps. No functorial choice of injective objects is assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
  CategoryTheory.Abelian MonoidalCategory Opposite TopologicalSpace
open TauCeti.AlgebraicGeometry.Scheme.Modules

namespace ToricPower

universe u

variable (k : Type u) [CommRing k] (X : Scheme.{u}) [X.Over (Spec (.of k))]

local instance moduleUnitNaturalHasExt : HasExt.{u} X.Modules :=
  hasExt_of_enoughInjectives X.Modules

/-- Degree-one comparison is natural along every morphism between actual
short exact sequences whose middle terms are injective. -/
theorem moduleUnitExtOneCohomologyOfShortExact_naturality
    {S T : ShortComplex X.Modules} (hS : S.ShortExact) (hT : T.ShortExact)
    [Injective S.X₂] [Injective T.X₂] (f : S ⟶ T)
    (x : Ext.{u} (𝟙_ X.Modules) S.X₁ 1) :
    moduleUnitExtOneCohomologyOfShortExact k X hT
        (x.comp (Ext.mk₀ f.τ₁) (add_zero _)) =
      cohomologyMap f.τ₁ 1 (moduleUnitExtOneCohomologyOfShortExact k X hS x) := by
  obtain ⟨y, rfl⟩ := moduleExtConnecting_surjective k X hS (𝟙_ X.Modules) 0 x
  rw [moduleExtConnecting_naturality k X hS hT f, moduleUnitExtOneCohomologyOfShortExact_connecting,
    moduleUnitExtOneCohomologyOfShortExact_connecting,
    moduleUnitExtZeroCohomology_naturality,
    Scheme.Modules.cohomologyMapBaseLinear_apply, cohomologyFunctor_map]
  exact (cohomologyδ_naturality hS hT f 0 1 rfl
    (moduleUnitExtZeroCohomology k X S.X₃ y)).symm

/-- The higher comparison step preserves naturality of the lower-degree
comparison along the given actual short exact sequence morphism. -/
theorem moduleUnitExtHigherStep_naturality
    {S T : ShortComplex X.Modules} (hS : S.ShortExact) (hT : T.ShortExact)
    [Injective S.X₂] [Injective T.X₂] (f : S ⟶ T) (n : ℕ)
    (eS : Ext.{u} (𝟙_ X.Modules) S.X₃ (n+1) ≃ₗ[k] Cohomology S.X₃ (n+1))
    (eT : Ext.{u} (𝟙_ X.Modules) T.X₃ (n+1) ≃ₗ[k] Cohomology T.X₃ (n+1))
    (he : ∀ y, eT (y.comp (Ext.mk₀ f.τ₃) (add_zero _)) =
      cohomologyMap f.τ₃ (n+1) (eS y))
    (x : Ext.{u} (𝟙_ X.Modules) S.X₁ (n+2)) :
    moduleUnitExtHigherStep k X hT n eT
        (x.comp (Ext.mk₀ f.τ₁) (add_zero _)) =
      cohomologyMap f.τ₁ (n+2) (moduleUnitExtHigherStep k X hS n eS x) := by
  obtain ⟨y, rfl⟩ := moduleExtConnecting_surjective k X hS (𝟙_ X.Modules) (n+1) x
  rw [moduleExtConnecting_naturality k X hS hT f, moduleUnitExtHigherStep_connecting,
    moduleUnitExtHigherStep_connecting, he]
  exact (cohomologyδ_naturality hS hT f (n+1) (n+2) rfl (eS y)).symm

theorem moduleUnitExtOneCohomology_eq (M : X.Modules) :
    moduleUnitExtOneCohomology k X M = moduleUnitExtOneCohomologyOfShortExact k X
      (TauCeti.injectiveCokernelSequence_shortExact M) := rfl

/-- The chosen degree-one isomorphism is natural in every coefficient map. -/
theorem moduleUnitExtOneCohomology_naturality {M N : X.Modules}
    (f : M ⟶ N) (x : Ext.{u} (𝟙_ X.Modules) M 1) :
    moduleUnitExtOneCohomology k X N (x.comp (Ext.mk₀ f) (add_zero _)) =
      cohomologyMap f 1 (moduleUnitExtOneCohomology k X M x) := by
  rw [moduleUnitExtOneCohomology_eq, moduleUnitExtOneCohomology_eq]
  have h := moduleUnitExtOneCohomologyOfShortExact_naturality k X
    (TauCeti.injectiveCokernelSequence_shortExact M)
    (TauCeti.injectiveCokernelSequence_shortExact N)
    (moduleInjectiveCokernelComparison X f) x
  rw [moduleInjectiveCokernelComparison_τ₁] at h
  exact h

@[simp]
theorem moduleUnitExtCohomology_zero (M : X.Modules) :
    moduleUnitExtCohomology k X M 0 = moduleUnitExtZeroCohomology k X M := rfl

@[simp]
theorem moduleUnitExtCohomology_one (M : X.Modules) :
    moduleUnitExtCohomology k X M 1 = moduleUnitExtOneCohomology k X M := rfl

theorem moduleUnitExtCohomology_succ_succ (M : X.Modules) (n : ℕ) :
    moduleUnitExtCohomology k X M (n+2) =
      moduleUnitExtHigherStep k X (TauCeti.injectiveCokernelSequence_shortExact M) n
        (moduleUnitExtCohomology k X (TauCeti.injectiveCokernelSequence M).X₃ (n+1)) := by
  exact congrFun (Nat.twoStepInduction.eq_3
    (motive := fun n => ∀ M : X.Modules,
      Ext.{u} (𝟙_ X.Modules) M n ≃ₗ[k] Cohomology M n)
    (fun M => moduleUnitExtZeroCohomology k X M)
    (fun M => moduleUnitExtOneCohomology k X M)
    (fun n _ ih M => moduleUnitExtHigherStep k X
      (TauCeti.injectiveCokernelSequence_shortExact M) n
      (ih (TauCeti.injectiveCokernelSequence M).X₃)) n) M

/-- Every coefficient map commutes with the actual Ext / ordinary sheaf
cohomology isomorphisms in every nonnegative degree. -/
theorem moduleUnitExtCohomology_naturality (n : ℕ) {M N : X.Modules}
    (f : M ⟶ N) (x : Ext.{u} (𝟙_ X.Modules) M n) :
    moduleUnitExtCohomology k X N n (x.comp (Ext.mk₀ f) (add_zero _)) =
      cohomologyMap f n (moduleUnitExtCohomology k X M n x) := by
  induction n using Nat.twoStepInduction generalizing M N with
  | zero =>
    rw [moduleUnitExtCohomology_zero, moduleUnitExtCohomology_zero]
    have h := moduleUnitExtZeroCohomology_naturality k X f x
    rw [Scheme.Modules.cohomologyMapBaseLinear_apply, cohomologyFunctor_map] at h
    exact h
  | one => exact moduleUnitExtOneCohomology_naturality k X f x
  | more n _ ih =>
    rw [moduleUnitExtCohomology_succ_succ, moduleUnitExtCohomology_succ_succ]
    exact moduleUnitExtHigherStep_naturality k X
      (TauCeti.injectiveCokernelSequence_shortExact M)
      (TauCeti.injectiveCokernelSequence_shortExact N)
      (moduleInjectiveCokernelComparison X f) n _ _
      (fun y => ih (moduleInjectiveCokernelComparison X f).τ₃ y) x

end ToricPower

end
