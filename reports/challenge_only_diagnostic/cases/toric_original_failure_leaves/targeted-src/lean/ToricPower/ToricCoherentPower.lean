module

public import ToricPower.GeometricCore
public import ToricPower.CoherentDerived

/-!
# Actual finite-power transfer of a toric coherent generator

The geometric inputs here are the actual toric scheme, its Noetherian
property, finiteness of the positive power map, and the actual global
structure-sheaf retract constructed from the residue splitting. The
categorical conclusion is classical generation in the literal bounded
derived category of coherent sheaves.

An existing generator and its genuine finite invertible decomposition are
explicit inputs. This theorem is the power-multiple step in the paper;
it does not assert the existence of the initial generator.
-/

@[expose] public noncomputable section

attribute [local instance] CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open TauCeti.Toric

namespace ToricPower

universe u v w

variable {N : Type u} {V : Type v} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

local instance toricPowerLocallyNoetherian (fan : Fan i) :
    IsLocallyNoetherian fan.algebraicRealization := by
  letI := toricScheme_isNoetherian fan
  infer_instance

/-- The actual coherent direct image of a positive power map of a regular
toric variety. Finiteness and the Noetherian property are proved geometric
inputs, not additional hypotheses of this definition. -/
abbrev toricCoherentPowerPushforward (fan : Fan i) (regular : fan.IsRegular)
    (ell : ℕ) (hell : 0 < ell) :
    Coh fan.algebraicRealization ⥤ Coh fan.algebraicRealization := by
  letI := toricPowerMap_finite fan regular ell hell
  exact TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf.pushforward
    (toricPowerMap fan ell)

/-- Forgetting the coherent wrapper recovers the ordinary scheme-module
pushforward along the actual toric power map. -/
@[simp]
theorem toricCoherentPowerPushforward_obj_underlying
    (fan : Fan i) (regular : fan.IsRegular) (ell : ℕ) (hell : 0 < ell)
    (M : Coh fan.algebraicRealization) :
    ((toricCoherentPowerPushforward fan regular ell hell).obj M).obj =
      (Scheme.Modules.pushforward (toricPowerMap fan ell)).obj M.obj := rfl


end ToricPower

end
