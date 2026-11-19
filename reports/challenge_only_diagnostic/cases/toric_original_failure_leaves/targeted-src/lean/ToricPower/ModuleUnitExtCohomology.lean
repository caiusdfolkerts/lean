module

public import ToricPower.ModuleUnitExtOne

/-! Ext from the structure sheaf equals ordinary sheaf cohomology in every degree, by dimension shifting through actual injective module sheaves. -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
  CategoryTheory.Abelian MonoidalCategory Opposite TopologicalSpace

namespace ToricPower

universe u

variable (k : Type u) [CommRing k] (X : Scheme.{u}) [X.Over (Spec (.of k))]

local instance moduleUnitHigherHasExt : HasExt.{u} X.Modules :=
  hasExt_of_enoughInjectives X.Modules

/-- The two actual positive-degree connecting isomorphisms transport
an already constructed comparison across any injective middle term. -/
def moduleUnitExtHigherStep {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [Injective S.X₂] (n : ℕ)
    (e : Ext.{u} (𝟙_ X.Modules) S.X₃ (n+1) ≃ₗ[k]
      TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology S.X₃ (n+1)) :
    Ext.{u} (𝟙_ X.Modules) S.X₁ (n+2) ≃ₗ[k]
      TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology S.X₁ (n+2) :=
  (moduleExtConnectingIso k X hS (𝟙_ X.Modules) n).symm.trans
    (e.trans
      (TauCeti.AlgebraicGeometry.Scheme.Modules.cohomologySuccLinearEquivOfIsFlasque k hS n))

/-- In every degree, Ext from the actual structure sheaf equals the
ordinary cohomology of the underlying abelian sheaf. The construction
uses actual dimension shifts and imposes no quasicoherence hypothesis. -/
def moduleUnitExtCohomology (M : X.Modules) (n : ℕ) :
    Ext.{u} (𝟙_ X.Modules) M n ≃ₗ[k]
      TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology M n := by
  induction n using Nat.twoStepInduction generalizing M with
  | zero => exact moduleUnitExtZeroCohomology k X M
  | one => exact moduleUnitExtOneCohomology k X M
  | more n _ ih =>
    exact moduleUnitExtHigherStep k X
      (TauCeti.injectiveCokernelSequence_shortExact M) n
      (ih (TauCeti.injectiveCokernelSequence M).X₃)

end ToricPower

end
