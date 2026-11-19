module

public import ToricPower.ToricClosedSubtorusSupport
public import ToricPower.ToricSliceComponentCharacters
public import ToricPower.ArrangementCochainLabels
public import ToricPower.RestrictedFanIncidence

/-! # Integral characters of the actual closed-row labels

A supported cell determines a genuine integral character on the
saturated subspace lattice. An arbitrary ambient lift is chosen only
for notation: its restriction is canonical. Every actual translated
incidence adds exactly its original integral character.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open TauCeti.Toric CategoryTheory
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)
  (σ : fan.cones) (W : Submodule ℝ V)
  (spans : Submodule.span ℝ (σ.val : Set V) = W)

def toricClosedRowLift
    (c : IncidenceObject (fanArrangementMatrix fan basis rays))
    (supported : closedIntegralRowsSupport (fanArrangementMatrix fan basis rays)
      (fanConeSliceRows fan rays σ) c) : Fin n → ℤ :=
  ((closedIntegralRowsSupport_iff_toricSubtorus fan basis rays regular σ W spans c).mp
    supported).choose

theorem toricClosedRowLift_sub_mem
    (c : IncidenceObject (fanArrangementMatrix fan basis rays))
    (supported : closedIntegralRowsSupport (fanArrangementMatrix fan basis rays)
      (fanConeSliceRows fan rays σ) c) :
    cellCenter (augmentedForms (fanArrangementMatrix fan basis rays)) c.2.val -
        latticeLift (toricClosedRowLift fan regular basis rays σ W spans c supported) ∈
      fanCharacterAnnihilator fan basis W :=
  ((closedIntegralRowsSupport_iff_toricSubtorus fan basis rays regular σ W spans c).mp
    supported).choose_spec

def toricClosedRowCharacter
    (c : IncidenceObject (fanArrangementMatrix fan basis rays))
    (supported : closedIntegralRowsSupport (fanArrangementMatrix fan basis rays)
      (fanConeSliceRows fan rays σ) c) : N →+ ℤ :=
  basis.equivFun.symm (toricClosedRowLift fan regular basis rays σ W spans c supported)

theorem toricClosedRowCharacter_value
    (c : IncidenceObject (fanArrangementMatrix fan basis rays))
    (supported : closedIntegralRowsSupport (fanArrangementMatrix fan basis rays)
      (fanConeSliceRows fan rays σ) c) (z : latticeTrace i W) :
    ((toricClosedRowCharacter fan regular basis rays σ W spans c supported z.val : ℤ) : ℝ) =
      characterCoordinateEquiv fan.lattice basis
        (cellCenter (augmentedForms (fanArrangementMatrix fan basis rays)) c.2.val) (i z.val) := by
  have ann := toricClosedRowLift_sub_mem fan regular basis rays σ W spans c supported
  change characterCoordinateEquiv fan.lattice basis
    (cellCenter (augmentedForms (fanArrangementMatrix fan basis rays)) c.2.val -
      latticeLift (toricClosedRowLift fan regular basis rays σ W spans c supported)) ∈
        W.dualAnnihilator at ann
  have zero := (Submodule.mem_dualAnnihilator _).mp ann (i z.val) z.property
  rw [map_sub,characterCoordinateEquiv_latticeLift fan basis,LinearMap.sub_apply,
    fan.lattice.realCharacter_apply] at zero
  exact (sub_eq_zero.mp zero).symm

theorem toricClosedRowLift_selected
    (c : IncidenceObject (fanArrangementMatrix fan basis rays))
    (supported : closedIntegralRowsSupport (fanArrangementMatrix fan basis rays)
      (fanConeSliceRows fan rays σ) c)
    (j : fanConeSliceRows fan rays σ) :
    augmentedLatticePairing (fanArrangementMatrix fan basis rays)
      (toricClosedRowLift fan regular basis rays σ W spans c supported) j.val =
        c.2.val.val.1 j.val := by
  have ann := toricClosedRowLift_sub_mem fan regular basis rays σ W spans c supported
  rw [fanCharacterAnnihilator_eq_zeroSlice fan basis rays σ W spans] at ann
  have zero := (mem_arrangementZeroSlice _ _ _).mp ann j.val j.property
  have original := cellCenter_mem (augmentedForms (fanArrangementMatrix fan basis rays)) c.2.val j.val
  rw [if_pos (supported j.property)] at original
  rw [map_sub,augmentedForms_latticeLift,original] at zero
  exact_mod_cast (sub_eq_zero.mp zero).symm

/-- On every retained ray, the original reflected Cartier coefficient
is the negative of the genuine restricted integral character. -/
theorem toricClosedRowCharacter_restrictedCoefficient
    (rational : IsRationalSubspace i W)
    (c : IncidenceObject (fanArrangementMatrix fan basis rays))
    (supported : closedIntegralRowsSupport (fanArrangementMatrix fan basis rays)
      (fanConeSliceRows fan rays σ) c)
    (ρ : (restrictedFan fan W rational).Ray) :
    restrictedFanRayCoefficients fan W rational
      (arrangementDualLeftCoefficients fan basis rays c) ρ =
    -(toricClosedRowCharacter fan regular basis rays σ W spans c supported)
      (fanRayPrimitiveGenerator (restrictedFan fan W rational) ρ).val := by
  rw [restrictedFanRayCoefficients,arrangementDualLeftCoefficients_apply,
    reflectedCeiling_eq_ceil _ _ (cellCenter_mem _ _)]
  have value := toricClosedRowCharacter_value fan regular basis rays σ W spans c supported
    (fanRayPrimitiveGenerator (restrictedFan fan W rational) ρ)
  rw [restrictedFan_primitive_value fan W rational,
    characterCoordinateEquiv_primitive fan basis rays] at value
  change ⌈-augmentedForms (fanArrangementMatrix fan basis rays)
      (.inl (rays.symm (restrictedFanRayEquiv fan W rational ρ).val))
        (cellCenter (augmentedForms (fanArrangementMatrix fan basis rays)) c.2.val)⌉ = _
  rw [← value,← Int.cast_neg,Int.ceil_intCast]
  rw [restrictedFan_primitive_value fan W rational]

/-- The canonical restricted character retains every translated
incidence, regardless of which ambient integral lifts were chosen. -/
theorem toricClosedRowCharacter_incidence
    {c d : IncidenceObject (fanArrangementMatrix fan basis rays)} (f : c ⟶ d)
    (supportedD : closedIntegralRowsSupport (fanArrangementMatrix fan basis rays)
      (fanConeSliceRows fan rays σ) d)
    (supportedC : closedIntegralRowsSupport (fanArrangementMatrix fan basis rays)
      (fanConeSliceRows fan rays σ) c) :
    (toricClosedRowCharacter fan regular basis rays σ W spans d supportedD).comp
        (latticeTrace i W).subtype.toAddMonoidHom =
      (toricClosedRowCharacter fan regular basis rays σ W spans c supportedC +
        basis.equivFun.symm f.val).comp (latticeTrace i W).subtype.toAddMonoidHom := by
  have rows : integralSliceRowMap (fanArrangementMatrix fan basis rays)
      (fanConeSliceRows fan rays σ)
      (toricClosedRowLift fan regular basis rays σ W spans d supportedD) =
    integralSliceRowMap (fanArrangementMatrix fan basis rays)
      (fanConeSliceRows fan rays σ)
      (toricClosedRowLift fan regular basis rays σ W spans c supportedC + f.val) := by
    funext j
    change augmentedLatticePairing _ _ j.val = augmentedLatticePairing _ _ j.val
    rw [augmentedLatticePairing_add,Pi.add_apply,toricClosedRowLift_selected,
      toricClosedRowLift_selected]
    have source := cellCenter_mem (augmentedForms (fanArrangementMatrix fan basis rays)) c.2.val j.val
    have target := f.property
      (cellCenter (augmentedForms (fanArrangementMatrix fan basis rays)) c.2.val)
      (cell_subset_closedCell _ _ _ (cellCenter_mem _ c.2.val)) j.val
    rw [if_pos (supportedC j.property)] at source
    rw [if_pos (supportedD j.property),map_add,augmentedForms_latticeLift,source] at target
    exact_mod_cast target.symm
  have equal := (fanConeSliceRowMap_eq_iff fan basis rays σ W spans _ _).mp rows
  simpa only [toricClosedRowCharacter,map_add] using equal

end ToricPower

end
