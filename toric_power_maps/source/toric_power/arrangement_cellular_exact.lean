module

public import ToricPower.CellularRealizationExact
public import ToricPower.ArrangementCellularAffineSections

/-!
# Exactness and the actual length bound for quasicoherent cellular realization

The functor here is the original finite complex of actual Cartier
sheaves and arbitrary vector copowers. Its exactness and length bound
are the literal hypotheses required by the unbounded finite-total
construction.
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
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "X" => fan.algebraicRealization
local notation "Φ" => arrangementQuasicoherentCellularRealization fan nonempty regular basis rays

local instance cellularExactBiproducts : HasFiniteBiproducts (QCoh X) :=
  HasFiniteBiproducts.of_hasFiniteProducts

instance arrangementQuasicoherentCellularRealization_additive : (Φ).Additive := by
  unfold arrangementQuasicoherentCellularRealization
  infer_instance

instance arrangementQuasicoherentCellularRealization_linear : (Φ).Linear ℂ := by
  unfold arrangementQuasicoherentCellularRealization
  infer_instance

instance arrangementQuasicoherentCellularRealization_preservesColimits :
    PreservesColimitsOfSize.{0,0} Φ := by
  unfold arrangementQuasicoherentCellularRealization
  infer_instance

instance arrangementQuasicoherentCellularRealization_preservesFiniteLimits :
    PreservesFiniteLimits Φ := by
  unfold arrangementQuasicoherentCellularRealization
  infer_instance

/-- Every coefficient degree is exact in the original quasicoherent
category, including unrestricted diagram coefficients. -/
instance arrangementQuasicoherentCellularDegree_preservesFiniteLimits (q : ℕ) :
    PreservesFiniteLimits (Φ ⋙ HomologicalComplex.eval (QCoh X) (.up ℕ) q) := inferInstance

instance arrangementQuasicoherentCellularDegree_preservesFiniteColimits (q : ℕ) :
    PreservesFiniteColimits (Φ ⋙ HomologicalComplex.eval (QCoh X) (.up ℕ) q) := inferInstance

/-- The literal term vanishes strictly above the full lattice rank. -/
theorem arrangementQuasicoherentCellularRealization_isZero_X_above
    (F : IncidenceObject A ⥤ ModuleCat ℂ) (q : ℕ) (above : n < q) :
    IsZero (((Φ).obj F).X q) :=
  arrangementCellularRealization_isZero_X_above A ℂ
    (arrangementDualLeftQuasicoherentDiagram fan nonempty regular basis rays) F q above

/-- The actual top differential is zero, as its literal target vanishes. -/
theorem arrangementQuasicoherentCellularRealization_outgoing
    (F : IncidenceObject A ⥤ ModuleCat ℂ) :
    ((Φ).obj F).d n (n + 1) = 0 :=
  (arrangementQuasicoherentCellularRealization_isZero_X_above fan nonempty regular basis rays
    F (n + 1) (Nat.lt_succ_self n)).eq_of_tgt _ _

end ToricPower

end
