module

public import ToricPower.FanRayQuotient
public import ToricPower.LatticeRayQuotient
public import ToricPower.RegularConeRayQuotient

/-!
# The canonical lower-rank regular quotient star

This is the actual quotient construction used in dimension induction:
the lattice is `N / ℤv`, the real space is `V / ℝv`, and the cones are
the projected original ray star. Regularity and strict rank decrease
are proved for the original arbitrary regular fan.
-/

@[expose] public noncomputable section
open TauCeti TauCeti.Toric
namespace ToricPower.FanSubdivision

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (fan : Fan i) (ray : fan.Ray)

theorem selectedRay_isPrimitive : IsPrimitive (fanRayPrimitiveGenerator fan ray) :=
  primitiveGenerator_isPrimitive fan.lattice (fan.isToricCone ray.toCone.property)
    (ray.toToricRay fan ray.toCone le_rfl)

theorem selectedRay_isPrimitiveGenerator (cone : fan.cones) (contains : ray.toCone ≤ cone) :
    IsPrimitiveGenerator i (ray.toToricRay fan cone contains)
      (fanRayPrimitiveGenerator fan ray) := by
  apply isPrimitiveGenerator_iff.mpr
  exact ⟨fanRayRealVector_mem fan ray,selectedRay_isPrimitive fan ray⟩

local notation "a" => fanRayPrimitiveGenerator fan ray
local notation "qZ" => Submodule.mkQ (Submodule.span ℤ {a})
local notation "qR" => Submodule.mkQ (Submodule.span ℝ {i a})
local notation "j" => rayQuotientLatticeMap i a

/-- The canonical quotient star uses actual module quotients and the
proved quotient lattice, with no chosen abstract substitute fan. -/
def canonicalRayStar : Fan j :=
  rayStarQuotient fan ray (qZ).toAddMonoidHom qR
    (rayQuotient_maps_compatible i a)
    (rayQuotient_real_kernel i a)
    (rayQuotient_isIntegralLattice i a fan.lattice (selectedRay_isPrimitive fan ray))

theorem mem_canonicalRayStar_iff (δ : PointedCone ℝ (RayQuotientSpace i a)) :
    δ ∈ (canonicalRayStar fan ray).cones ↔
      ∃ σ ∈ fan.cones, ray.toCone.val ≤ σ ∧ δ.IsFaceOf (PointedCone.map qR σ) :=
  mem_rayStarQuotient_iff fan ray (qZ).toAddMonoidHom qR
    (rayQuotient_maps_compatible i a) (rayQuotient_real_kernel i a)
    (rayQuotient_isIntegralLattice i a fan.lattice (selectedRay_isPrimitive fan ray)) δ

instance : Nonempty (canonicalRayStar fan ray).cones := by
  refine ⟨⟨PointedCone.map qR ray.toCone.val, ?_⟩⟩
  exact (mem_canonicalRayStar_iff fan ray _).mpr
    ⟨ray.toCone.val,ray.toCone.property,le_rfl,PointedCone.IsFaceOf.refl _⟩

/-- Smoothness descends to the actual quotient star, including cones
of every dimension and all faces introduced by the fan constructor. -/
theorem canonicalRayStar_regular (regular : fan.IsRegular) :
    (canonicalRayStar fan ray).IsRegular := by
  rw [Fan.isRegular_iff]
  intro δ member
  obtain ⟨σ,hσ,contains,face⟩ := (mem_canonicalRayStar_iff fan ray δ).mp member
  let cone : fan.cones := ⟨σ,hσ⟩
  have imageRegular := regularCone_quotientRay_isRegular fan.lattice
    (rayQuotient_isIntegralLattice i a fan.lattice (selectedRay_isPrimitive fan ray))
    ((Fan.isRegular_iff.mp regular) σ hσ) (ray.toToricRay fan cone contains) a
    (selectedRay_isPrimitiveGenerator fan ray cone contains) qZ qR
    (rayQuotient_maps_compatible i a) (Submodule.ker_mkQ _) (Submodule.mkQ_surjective _)
  exact imageRegular.of_isFaceOf face

/-- The induction parameter is the actual integral rank. -/
theorem canonicalRayStar_rank_lt :
    Module.finrank ℤ (RayQuotientLattice a) < Module.finrank ℤ N :=
  rayQuotient_finrank_lt i a fan.lattice (selectedRay_isPrimitive fan ray)

end ToricPower.FanSubdivision
end
