module

public import ToricPower.CanonicalRayStarOrder

/-!
# Primitive ray vectors in a regular ray quotient

Every ray of a regular cone other than the quotient ray has a primitive
image in the quotient lattice. This is an integral assertion: it follows
from the actual quotient basis, rather than from real nonvanishing.
-/

@[expose] public noncomputable section
open TauCeti TauCeti.Toric
namespace ToricPower.FanSubdivision

variable {N P V : Type*} [AddCommGroup N] [AddCommGroup P]
  [AddCommGroup V] [Module ℝ V] {i : N →+ V}

theorem regularCone_quotient_rayPrimitive (lattice : IsIntegralLattice i)
    {σ : PointedCone ℝ V} (regular : IsRegularCone i σ)
    (selected other : ToricRay σ) (different : other ≠ selected)
    (a : N) (selectedPrimitive : IsPrimitiveGenerator i selected a)
    (projection : N →ₗ[ℤ] P)
    (kernel : projection.ker = Submodule.span ℤ {a})
    (surjective : Function.Surjective projection) :
    IsPrimitive (projection (primitiveGenerator lattice regular.toIsToricCone other)) := by
  obtain ⟨m,basis,rayIndex,basisExtends⟩ := regular.exists_basis
  have values (ρ : ToricRay σ) :
      basis (rayIndex ρ) = primitiveGenerator lattice regular.toIsToricCone ρ :=
    (basisExtends.isPrimitiveGenerator_apply ρ).eq_primitiveGenerator lattice regular.toIsToricCone
  have pivotValue : basis (rayIndex selected) = a :=
    (values selected).trans
      (selectedPrimitive.eq_primitiveGenerator lattice regular.toIsToricCone).symm
  have kernel' : projection.ker = Submodule.span ℤ {basis (rayIndex selected)} := by
    rw [kernel,pivotValue]
  let quotientBasis := projectedBasis basis (rayIndex selected) projection kernel' surjective
  have differentIndex : rayIndex other ≠ rayIndex selected :=
    fun same => different (rayIndex.injective same)
  have eq : quotientBasis ⟨rayIndex other,differentIndex⟩ =
      projection (primitiveGenerator lattice regular.toIsToricCone other) := by
    rw [projectedBasis_apply,values]
  rw [← eq]
  exact quotientBasis.isPrimitive _

variable (fan : Fan i) (regular : fan.IsRegular) (ray : fan.Ray)

include regular in
/-- The global ray-indexed version retains the literal quotient map
and the original fan's primitive vector. -/
theorem canonicalRayStar_otherRay_primitive (σ : OriginalRayStarCone fan ray)
    (other : fan.Ray) (below : other.toCone ≤ σ.val) (different : other ≠ ray) :
    IsPrimitive ((Submodule.span ℤ {fanRayPrimitiveGenerator fan ray}).mkQ
      (fanRayPrimitiveGenerator fan other)) := by
  let selectedLocal := ray.toToricRay fan σ.val σ.property
  let otherLocal := other.toToricRay fan σ.val below
  have localDifferent : otherLocal ≠ selectedLocal := by
    intro same
    exact different (congrArg (Fan.Ray.ofToricRay fan σ.val) same)
  have coneRegular := Fan.isRegular_iff.mp regular σ.val.val σ.val.property
  have generatorEq : primitiveGenerator fan.lattice coneRegular.toIsToricCone otherLocal =
      fanRayPrimitiveGenerator fan other := by
    exact (selectedRay_isPrimitiveGenerator fan other σ.val below).eq_primitiveGenerator
      fan.lattice coneRegular.toIsToricCone |>.symm
  rw [← generatorEq]
  exact regularCone_quotient_rayPrimitive fan.lattice coneRegular selectedLocal otherLocal
    localDifferent (fanRayPrimitiveGenerator fan ray)
    (selectedRay_isPrimitiveGenerator fan ray σ.val σ.property)
    (Submodule.span ℤ {fanRayPrimitiveGenerator fan ray}).mkQ
    (Submodule.ker_mkQ _) (Submodule.mkQ_surjective _)

end ToricPower.FanSubdivision
end
