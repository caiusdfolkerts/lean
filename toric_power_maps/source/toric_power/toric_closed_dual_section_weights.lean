module

public import ToricPower.ToricClosedDualAllowedCharacters
public import ToricPower.LinearSubspaceChartPreimage
public import ToricPower.CechDivisorSections

/-! # The exact section weights of every closed dual component

The component character is compared with the actual divisor inequalities
on the saturated restricted fan. The comparison uses the unchanged
primitive vectors, so it preserves every integral character.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)
  (σ : fan.cones) (W : LinearSubspace fan)
  (spans : Submodule.span ℝ (σ.val : Set V) = W.space)
  (b : fan.Ray → ℤ) (τ : fan.cones)

local notation "Yfan" => restrictedFan fan W.space W.rational
local notation "coeff" => restrictedFanRayCoefficients fan W.space W.rational b
local notation "chart" => linearSubspaceChart fan W τ

theorem restrictedConeEquation_ray
    (ρ : ToricRay (linearSubspaceChart fan W τ).val) :
    (coneDivisorCharacter fan regular b τ).comp
        (latticeTrace i W.space).subtype.toAddMonoidHom
        (primitiveGenerator (Yfan).lattice ((Yfan).isToricCone (chart).property) ρ) =
      coneDivisorCoefficients (Yfan) coeff chart ρ := by
  change coneDivisorCharacter fan regular b τ
    (primitiveGenerator (Yfan).lattice ((Yfan).isToricCone (chart).property) ρ).val = _
  rw [← fanRayPrimitiveGenerator_ofToricRay (Yfan) chart ρ,
    restrictedFan_primitive_value]
  apply coneDivisorCharacter_fanRay fan regular b τ
  change (Fan.Ray.ofToricRay (Yfan) chart ρ).toCone.val.map W.space.subtype ≤ τ.val
  rintro v ⟨w,member,rfl⟩
  exact (Fan.Ray.toCone_ofToricRay_le (Yfan) chart ρ) member

theorem restrictedConeCharacterAllowed_iff (m : latticeTrace i W.space →+ ℤ) :
    m + (coneDivisorCharacter fan regular b τ).comp
        (latticeTrace i W.space).subtype.toAddMonoidHom ∈
      dualSemigroup (Yfan).lattice (τ.val.comap W.space.subtype) ↔
    ∀ ρ : ToricRay (linearSubspaceChart fan W τ).val,
      0 ≤ coneDivisorCoefficients (Yfan) coeff chart ρ +
        m (primitiveGenerator (Yfan).lattice ((Yfan).isToricCone (chart).property) ρ) := by
  change m + (coneDivisorCharacter fan regular b τ).comp
      (latticeTrace i W.space).subtype.toAddMonoidHom ∈
    dualSemigroup (Yfan).lattice (chart).val ↔ _
  rw [mem_dualSemigroup_iff_primitiveGenerator (Yfan).lattice
    ((Yfan).isToricCone (chart).property)]
  apply forall_congr'
  intro ρ
  rw [AddMonoidHom.add_apply,restrictedConeEquation_ray fan regular W b τ ρ,add_comm]

include regular spans in
theorem toricClosedDualComponentAllowed_weight_iff
    (value : IntegralSliceValue (fanArrangementMatrix fan basis rays)
      (fanConeSliceRows fan rays σ)) :
    (closedDualComponentRegion (fanArrangementMatrix fan basis rays)
      (fanConeSliceRows fan rays σ) (fanConeRaySet fan rays τ)
      (fun r => b (rays r)) value).Nonempty ↔
      ∀ ρ : ToricRay (linearSubspaceChart fan W τ).val,
        0 ≤ coneDivisorCoefficients (Yfan) coeff chart ρ +
          toricClosedDualComponentCharacter fan basis rays σ W.space value
            (primitiveGenerator (Yfan).lattice ((Yfan).isToricCone (chart).property) ρ) :=
  (toricClosedDualComponentAllowed_iff fan regular basis rays σ W spans b τ value).trans
    (restrictedConeCharacterAllowed_iff fan regular W b τ _)

/-- All nonempty components, with no truncation, are exactly the actual
admissible characters of the restricted Cartier sheaf. -/
def toricClosedDualSectionWeightEquiv :
    {value : IntegralSliceValue (fanArrangementMatrix fan basis rays)
      (fanConeSliceRows fan rays σ) //
        (closedDualComponentRegion (fanArrangementMatrix fan basis rays)
          (fanConeSliceRows fan rays σ) (fanConeRaySet fan rays τ)
          (fun r => b (rays r)) value).Nonempty} ≃
      ToricChartDivisorWeight (Yfan) coeff chart :=
  Equiv.subtypeEquiv (toricClosedDualComponentCharacterEquiv fan basis rays σ W.space spans).toEquiv
    (fun value => by
      have same : (toricClosedDualComponentCharacterEquiv fan basis rays σ W.space spans).toEquiv
          value = toricClosedDualComponentCharacter fan basis rays σ W.space value :=
        toricClosedDualComponentCharacterEquiv_apply fan basis rays σ W.space spans value
      rw [same]
      exact toricClosedDualComponentAllowed_weight_iff fan regular basis rays σ W spans b τ value)

end ToricPower

end
