module

public import ToricPower.ArrangementDualPowerDiagram
public import ToricPower.ArrangementPowerPushdown
public import ToricPower.ElementPushdownFamilies
public import ToricPower.ElementPushdownExact
public import ToricPower.QuasicoherentExactCoproducts
public import ToricPower.ToricPowerProjectionCoefficient

/-!
# The power comparison with arbitrary quasicoherent coefficients

The normalized dual diagram consists of genuine Cartier lines. The
residue decomposition is lifted through the actual fully faithful
quasicoherent inclusion, and the projection formula is applied naturally
in every coefficient. Thus the comparison retains all differentials
when coefficients are subsequently replaced by complexes.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "C" => IncidenceObject A
local notation "Q" => QCoh fan.algebraicRealization

/-- Every actual normalized dual Cartier label is quasicoherent. -/
def normalizedDualQuasicoherentDiagram : C ⥤ Q :=
  ObjectProperty.lift _ (normalizedDualCartierDiagram fan nonempty regular basis rays)
    (fun c => by
      letI := toricSchemeIntegral fan nonempty
      letI := (invariantCartierDivisor fan nonempty regular
        (normalizedDualCartierCoefficients fan basis rays c)).isInvertible_sheaf
      change (invariantCartierDivisor fan nonempty regular
        (normalizedDualCartierCoefficients fan basis rays c)).sheaf.IsQuasicoherent
      infer_instance)

local notation "P" => normalizedDualQuasicoherentDiagram fan nonempty regular basis rays

variable (ell : ℕ) (positive : 0 < ell)

local notation "B" => powerResidueFunctor A ell positive
local notation "p" => powerBranchFunctor A ell positive

/-- The literal global power decomposition in the actual QCoh category. -/
def normalizedDualQuasicoherentPowerDiagramIso :
    letI := toricPowerMap_finite fan regular ell positive
    ElementPushdown.obj B (p ⋙ P) ≅
      P ⋙ quasicoherentAffinePushforward (toricPowerMap fan ell) := by
  letI := toricPowerMap_finite fan regular ell positive
  exact Functor.fullyFaithfulCancelRight (quasicoherentInclusion fan.algebraicRealization)
    (ElementPushdown.postcomposeIso B (quasicoherentInclusion fan.algebraicRealization)
        (p ⋙ P) ≪≫
      normalizedDualCartierPowerDiagramIso fan nonempty regular basis rays ell positive)

instance powerDiagramPushdown_quasicoherent_preservesFiniteLimits :
    PreservesFiniteLimits (powerDiagramPushdown A ell positive Q) := by
  unfold powerDiagramPushdown
  infer_instance

instance powerDiagramPushdown_quasicoherent_preservesFiniteColimits :
    PreservesFiniteColimits (powerDiagramPushdown A ell positive Q) := by
  unfold powerDiagramPushdown
  infer_instance

instance powerDiagramPushdown_quasicoherent_additive :
    (powerDiagramPushdown A ell positive Q).Additive :=
  (powerDiagramPushdown A ell positive Q).additive_of_preserves_binary_products

/-- Tensor with an arbitrary actual coefficient, naturally in that coefficient. -/
def normalizedDualQuasicoherentTensorDiagram : Q ⥤ C ⥤ Q :=
  (curriedTensor Q).flip ⋙ (Functor.whiskeringLeft C Q Q).obj P

/-- The full power/tensor comparison is a natural isomorphism of
functors, not only a list of objectwise decompositions. -/
def normalizedDualPowerTensorDiagramIso :
    letI := toricPowerMap_finite fan regular ell positive
    normalizedDualQuasicoherentTensorDiagram fan nonempty regular basis rays ⋙
        powerDiagramPushdown A ell positive Q ≅
      quasicoherentPullback (toricPowerMap fan ell) ⋙
        normalizedDualQuasicoherentTensorDiagram fan nonempty regular basis rays ⋙
        (Functor.whiskeringRight C Q Q).obj
          (quasicoherentAffinePushforward (toricPowerMap fan ell)) := by
  letI := toricPowerMap_finite fan regular ell positive
  exact (ElementPushdown.postcomposeFamilyIso B (curriedTensor Q).flip (p ⋙ P)).symm ≪≫
    Functor.isoWhiskerLeft (curriedTensor Q).flip
      ((Functor.whiskeringLeft C Q Q).mapIso
        (normalizedDualQuasicoherentPowerDiagramIso fan nonempty regular basis rays ell positive)) ≪≫
    Functor.isoWhiskerRight (toricPowerProjectionCurriedRightIso fan regular ell positive)
      ((Functor.whiskeringLeft C Q Q).obj P)

end ToricPower

end
