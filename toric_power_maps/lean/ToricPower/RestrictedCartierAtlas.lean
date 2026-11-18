module

public import ToricPower.ToricCharacterAtlasPullback
public import ToricPower.RestrictedFanIncidence
public import ToricPower.RestrictedFanRegular

/-!
# Exact Cartier coefficients under a saturated subspace restriction

Pulling back the equation characters along the literal saturated lattice
inclusion produces the canonical restricted invariant Cartier divisor.
Equality is proved in the actual Cartier-divisor sheaf by checking every
primitive ray, whose integral vector is unchanged by restriction.

This identifies the Cartier data. The accompanying module-sheaf pullback
comparison still uses the separate local-frame gluing construction.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory TauCeti.Toric

namespace ToricPower

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

/-- The local equation has the prescribed coefficient on any fan ray
contained in its chart, independently of the chosen containing cone. -/
theorem coneDivisorCharacter_fanRay (fan : Fan i) (regular : fan.IsRegular)
    (b : fan.Ray → ℤ) (cone : fan.cones) (ray : fan.Ray) (included : ray.toCone ≤ cone) :
    coneDivisorCharacter fan regular b cone (fanRayPrimitiveGenerator fan ray) = b ray := by
  have value := coneDivisorCharacter_face_ray fan regular b
    (fan.isFaceOf_of_le cone.property ray.toCone.property included)
    (ray.toToricRay fan ray.toCone le_rfl)
  change coneDivisorCharacter fan regular b cone (fanRayPrimitiveGenerator fan ray) =
    b (Fan.Ray.ofToricRay fan ray.toCone (ray.toToricRay fan ray.toCone le_rfl)) at value
  refine value.trans (congrArg b ?_)
  apply Subtype.ext
  apply Subtype.ext
  rw [Fan.Ray.toCone_ofToricRay, Fan.Ray.toPointedCone_toToricRay]

#check coneDivisorCharacter_fanRay

/-- The actual Cartier divisor defined by pulled-back local equation
characters has precisely the original coefficients on the retained rays. -/
theorem restrictedInvariantCartierAtlas_eq (fan : Fan i) (regular : fan.IsRegular)
    (W : Submodule ℝ V) (hW : IsRationalSubspace i W)
    (nonempty : Nonempty (restrictedFan fan W hW).cones) (b : fan.Ray → ℤ) :
    ((invariantDivisorCharacterAtlas fan regular b).pullback
      (restrictedFanInclusion fan W hW)).cartierDivisor nonempty =
    invariantCartierDivisor (restrictedFan fan W hW) nonempty
      (restrictedFan_isRegular fan regular W hW) (restrictedFanRayCoefficients fan W hW b) := by
  apply ToricCharacterAtlas.cartierDivisor_eq_of_ray_values
    ((invariantDivisorCharacterAtlas fan regular b).pullback (restrictedFanInclusion fan W hW))
    (invariantDivisorCharacterAtlas (restrictedFan fan W hW)
      (restrictedFan_isRegular fan regular W hW) (restrictedFanRayCoefficients fan W hW b))
    nonempty
  intro cone ray
  change coneDivisorCharacter fan regular b
      (fanMapTargetCone (restrictedFanInclusion fan W hW) cone)
      (primitiveGenerator (restrictedFan fan W hW).lattice
        ((restrictedFan fan W hW).isToricCone cone.property) ray).val =
    coneDivisorCharacter (restrictedFan fan W hW)
      (restrictedFan_isRegular fan regular W hW) (restrictedFanRayCoefficients fan W hW b)
      cone (primitiveGenerator (restrictedFan fan W hW).lattice
        ((restrictedFan fan W hW).isToricCone cone.property) ray)
  rw [coneDivisorCharacter_ray,
    ← fanRayPrimitiveGenerator_ofToricRay (restrictedFan fan W hW) cone ray,
    restrictedFan_primitive_value]
  apply coneDivisorCharacter_fanRay fan regular b
    (fanMapTargetCone (restrictedFanInclusion fan W hW) cone)
    ((restrictedFanRayEquiv fan W hW
      (Fan.Ray.ofToricRay (restrictedFan fan W hW) cone ray)).val)
  change (restrictedFanRayEquiv fan W hW
      (Fan.Ray.ofToricRay (restrictedFan fan W hW) cone ray)).val.toCone.val ≤
    (restrictedFanInclusion fan W hW).leastCone cone.property
  rw [restrictedFanInclusion_leastCone]
  change (Fan.Ray.ofToricRay (restrictedFan fan W hW) cone ray).toCone.val.map W.subtype ≤
    cone.val.map W.subtype
  exact Submodule.map_mono
    (Fan.Ray.toCone_ofToricRay_le (restrictedFan fan W hW) cone ray)

#check restrictedInvariantCartierAtlas_eq

end ToricPower
