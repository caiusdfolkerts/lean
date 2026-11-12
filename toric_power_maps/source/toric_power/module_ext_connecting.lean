module

public import ToricPower.ModuleUnitExtZero
public import ToricPower.Cohomology.ExtBasic

/-! The actual Ext connecting maps for module sheaves, and their isomorphism in positive degrees when the middle term is injective. -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
  CategoryTheory.Abelian MonoidalCategory Opposite TopologicalSpace

namespace ToricPower

universe u

variable (k : Type u) [CommRing k] (X : Scheme.{u}) [X.Over (Spec (.of k))]

local instance moduleConnectingHasExt : HasExt.{u} X.Modules :=
  hasExt_of_enoughInjectives X.Modules

/-- The actual connecting map on module Ext. -/
abbrev moduleExtConnecting {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (P : X.Modules) (n : ℕ) :
    Ext.{u} P S.X₃ n →ₗ[k] Ext.{u} P S.X₁ (n+1) :=
  Ext.postcompOfLinear hS.extClass k P rfl

theorem moduleExtConnecting_surjective {S : ShortComplex X.Modules}
    (hS : S.ShortExact) [Injective S.X₂] (P : X.Modules) (n : ℕ) :
    Function.Surjective (moduleExtConnecting k X hS P n) := by
  intro x
  exact Ext.covariant_sequence_exact₁ P hS x (Ext.eq_zero_of_injective _) rfl

/-- In positive degrees both adjacent Ext groups of the actual
injective middle term vanish, giving the actual connecting isomorphism. -/
def moduleExtConnectingIso {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [Injective S.X₂] (P : X.Modules) (n : ℕ) :
    Ext.{u} P S.X₃ (n+1) ≃ₗ[k] Ext.{u} P S.X₁ (n+2) :=
  LinearEquiv.ofBijective (moduleExtConnecting k X hS P (n+1))
    ⟨by
      rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨y, rfl⟩ := Ext.covariant_sequence_exact₃ P hS x rfl hx
      rw [Ext.eq_zero_of_injective y, Ext.zero_comp],
      moduleExtConnecting_surjective k X hS P (n+1)⟩


end ToricPower

end
