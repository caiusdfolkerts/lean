module

public import ToricPower.ArrangementNormalizedPowerComparison
public import ToricPower.DetectionAdjunctionTransfer

/-!
# Diagram detection returns to the genuine toric power pushforward

The fully faithful input is the precise reconstruction theorem needed
here. Once supplied, the actual power comparison and the proved finite
flat pullback/pushforward adjunction return a nonzero map on the original
unbounded quasicoherent derived category.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  [nonempty : Nonempty fan.cones] (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local instance powerSheafDetectionDerivedQCoh :
    HasDerivedCategory.{1} (QCoh fan.algebraicRealization) := HasDerivedCategory.standard _
local instance powerSheafDetectionDerivedCells :
    HasDerivedCategory.{1}
      (IncidenceObject (fanArrangementMatrix fan basis rays) ⥤ ModuleCat.{0} ℂ) :=
  HasDerivedCategory.standard _

/-- This uses the actual toric map, every positive integer exponent,
and arbitrary unbounded source and target objects. -/
theorem exists_nonzero_toric_power_pushforward_of_diagram
    (fullyFaithful : (arrangementNormalizedDerivedHom fan regular basis rays).FullyFaithful)
    (ell : ℕ) (positive : 0 < ell)
    (M L : DerivedCategory (QCoh fan.algebraicRealization)) (q : ℤ)
    (f : (powerDerivedPushdown (fanArrangementMatrix fan basis rays) ell positive ℂ).obj
      ((arrangementNormalizedDerivedHom fan regular basis rays).obj M) ⟶
        ((arrangementNormalizedDerivedHom fan regular basis rays).obj L)⟦q⟧)
    (nonzeroMap : f ≠ 0) :
    letI := toricPowerMap_finite fan regular ell positive
    ∃ g : M ⟶ (((quasicoherentAffinePushforward (toricPowerMap fan ell)).mapDerivedCategory).obj L)⟦q⟧, g ≠ 0 := by
  letI := toricPowerMap_finite fan regular ell positive
  letI := toricPowerPullback_preservesFiniteLimits fan regular ell positive
  exact exists_nonzero_rightAdjoint_of_diagram
    (arrangementNormalizedDerivedHom fan regular basis rays)
    (quasicoherentPullback (toricPowerMap fan ell)).mapDerivedCategory
    (quasicoherentAffinePushforward (toricPowerMap fan ell)).mapDerivedCategory
    (powerDerivedPushdown (fanArrangementMatrix fan basis rays) ell positive ℂ)
    (toricPowerDerivedAdjunction fan regular ell positive) fullyFaithful
    (arrangementNormalizedPowerComparison fan nonempty regular basis rays ell positive)
    M L q f nonzeroMap

end ToricPower

end
