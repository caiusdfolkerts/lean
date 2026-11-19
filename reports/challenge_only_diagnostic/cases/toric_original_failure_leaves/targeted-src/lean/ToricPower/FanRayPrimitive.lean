module

public import ToricPower.FanRayIndex
public import TauCeti.Geometry.Toric.Algebraic.Ray.Primitive

/-! Canonical primitive lattice vectors for the actual rays of a fan. -/
@[expose] public noncomputable section
open TauCeti.Toric
namespace ToricPower
variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

def fanRayPrimitiveGenerator (fan : Fan i) (ρ : fan.Ray) : N :=
  primitiveGenerator fan.lattice (fan.isToricCone ρ.val.property)
    (Fan.Ray.toToricRay fan ρ ρ.val le_rfl)

theorem fanRayPrimitiveGenerator_ofToricRay (fan : Fan i) (cone : fan.cones)
    (ρ : ToricRay cone.val) :
    fanRayPrimitiveGenerator fan (Fan.Ray.ofToricRay fan cone ρ) =
      primitiveGenerator fan.lattice (fan.isToricCone cone.property) ρ := by
  have h := isPrimitiveGenerator_primitiveGenerator fan.lattice
    (fan.isToricCone (Fan.Ray.ofToricRay fan cone ρ).val.property)
    (Fan.Ray.toToricRay fan (Fan.Ray.ofToricRay fan cone ρ)
      (Fan.Ray.ofToricRay fan cone ρ).val le_rfl)
  apply IsPrimitiveGenerator.eq_primitiveGenerator _ fan.lattice (fan.isToricCone cone.property)
  apply (isPrimitiveGenerator_iff).mpr
  exact ⟨h.mem, h.isPrimitive⟩

end ToricPower
