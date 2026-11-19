module

public import ToricPower.DivisorWeightStructureRetract
public import ToricPower.DivisorWeightMonomialMaps
public import ToricPower.CartierTensorProduct

/-!
# Additivity of the actual invariant Cartier divisor

The selected equation character on a cone is chosen by an existence
theorem. Such choices need not be additive as characters. The actual
Cartier divisor is nevertheless additive: the difference between the
chosen sum equation and the sum of the two chosen equations vanishes on
every ray, hence defines an actual regular unit on the chart. Equality
in the Cartier quotient and uniqueness of gluing give literal equality
of the global Cartier divisors.

Development source, pending the pinned compiler.
-/

@[expose] public noncomputable section

set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
open TauCeti.Toric

namespace ToricPower

universe u v

variable {N : Type u} {V : Type v} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

/-- Characters with the same pairings on a cone's rays determine the
same actual Cartier class over that chart. Their quotient is constructed
as an actual regular monomial unit. -/
theorem rationalCharacterUnit_class_eq_of_ray_eq (fan : Fan i)
    (nonempty : Nonempty fan.cones) (cone : fan.cones) (first second : N →+ ℤ)
    (same : ∀ ρ : ToricRay cone.val,
      first (primitiveGenerator fan.lattice (fan.isToricCone cone.property) ρ) =
        second (primitiveGenerator fan.lattice (fan.isToricCone cone.property) ρ)) :
    letI := toricSchemeIntegral fan nonempty
    letI := chartOpen_nonempty fan cone
    TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass fan.algebraicRealization
      (fan.affineToricChartι cone).opensRange
      (Additive.ofMul (rationalCharacterUnit fan nonempty first)) =
    TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass fan.algebraicRealization
      (fan.affineToricChartι cone).opensRange
      (Additive.ofMul (rationalCharacterUnit fan nonempty second)) := by
  letI := toricSchemeIntegral fan nonempty
  letI := chartOpen_nonempty fan cone
  have vanishes : ∀ ρ : ToricRay cone.val,
      (first - second) (primitiveGenerator fan.lattice (fan.isToricCone cone.property) ρ) = 0 := by
    intro ρ
    rw [AddMonoidHom.sub_apply, same ρ, sub_self]
  have positive : first - second ∈ dualSemigroup fan.lattice cone.val := by
    rw [mem_dualSemigroup_iff_primitiveGenerator fan.lattice (fan.isToricCone cone.property)]
    intro ρ
    rw [vanishes]
  have negative : -(first - second) ∈ dualSemigroup fan.lattice cone.val := by
    rw [mem_dualSemigroup_iff_primitiveGenerator fan.lattice (fan.isToricCone cone.property)]
    intro ρ
    rw [AddMonoidHom.neg_apply, vanishes, neg_zero]
  let unit := toricMonomialUnit fan.lattice cone.val (first - second) positive negative
  apply (TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass_eq_rationalUnitClass_iff
    fan.algebraicRealization (fan.affineToricChartι cone).opensRange
    (rationalCharacterUnit fan nonempty first) (rationalCharacterUnit fan nonempty second)).mpr
  refine ⟨Units.map (chartCoordinateSectionsEquiv fan cone).toMonoidHom unit, ?_⟩
  rw [chartCoordinateGerm_regularUnit, chartCoordinateGerm_monomialUnit,
    rationalCharacterUnit_sub_mul]

/-- Addition of coefficient vectors is literal addition of the actual
Cartier divisors. No additivity of the independently chosen equation
characters is asserted or required. -/
theorem invariantCartierDivisor_add (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (b c : fan.Ray → ℤ) :
    letI := toricSchemeIntegral fan nonempty
    invariantCartierDivisor fan nonempty regular (b + c) =
      invariantCartierDivisor fan nonempty regular b +
        invariantCartierDivisor fan nonempty regular c := by
  letI := toricSchemeIntegral fan nonempty
  let atlas := (invariantDivisorCharacterAtlas fan regular (b + c)).cartierEquationAtlas nonempty
  apply atlas.existsUnique_cartierDivisor.unique
  · exact atlas.cartierDivisor_restrict
  · intro cone
    letI := chartOpen_nonempty fan cone
    let U := (fan.affineToricChartι cone).opensRange
    let classMap := TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass fan.algebraicRealization U
    have equation := rationalCharacterUnit_class_eq_of_ray_eq fan nonempty cone
      (coneDivisorCharacter fan regular b cone + coneDivisorCharacter fan regular c cone)
      (coneDivisorCharacter fan regular (b + c) cone) (by
        intro ρ
        simp only [AddMonoidHom.add_apply, coneDivisorCharacter_ray,
          coneDivisorCoefficients, Pi.add_apply])
    change (invariantCartierDivisor fan nonempty regular b +
        invariantCartierDivisor fan nonempty regular c) |_ U =
      classMap (Additive.ofMul (rationalCharacterUnit fan nonempty
        (coneDivisorCharacter fan regular (b + c) cone)))
    calc
      _ = (invariantCartierDivisor fan nonempty regular b |_ U) +
          (invariantCartierDivisor fan nonempty regular c |_ U) := by
        simp only [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict, map_add]
      _ = classMap (Additive.ofMul (rationalCharacterUnit fan nonempty
            (coneDivisorCharacter fan regular b cone))) +
          classMap (Additive.ofMul (rationalCharacterUnit fan nonempty
            (coneDivisorCharacter fan regular c cone))) := by
        rw [invariantCartierDivisor_localEquation, invariantCartierDivisor_localEquation]
      _ = classMap (Additive.ofMul (rationalCharacterUnit fan nonempty
          (coneDivisorCharacter fan regular b cone +
            coneDivisorCharacter fan regular c cone))) := by
        rw [rationalCharacterUnit_add, _root_.ofMul_mul, map_add]
      _ = _ := equation

/-- The full coefficient-to-Cartier map, with zero and addition proved
in the genuine Cartier divisor group. -/
def invariantCartierDivisorHom (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) :
    letI := toricSchemeIntegral fan nonempty
    (fan.Ray → ℤ) →+
      TauCeti.AlgebraicGeometry.Scheme.CartierDivisor fan.algebraicRealization := by
  letI := toricSchemeIntegral fan nonempty
  exact {
    toFun := invariantCartierDivisor fan nonempty regular
    map_zero' := invariantCartierDivisor_zero fan nonempty regular
    map_add' := invariantCartierDivisor_add fan nonempty regular }

@[simp]
theorem invariantCartierDivisor_neg (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (b : fan.Ray → ℤ) :
    letI := toricSchemeIntegral fan nonempty
    invariantCartierDivisor fan nonempty regular (-b) =
      -invariantCartierDivisor fan nonempty regular b :=
  (invariantCartierDivisorHom fan nonempty regular).map_neg b

@[simp]
theorem invariantCartierDivisor_sub (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (b c : fan.Ray → ℤ) :
    letI := toricSchemeIntegral fan nonempty
    invariantCartierDivisor fan nonempty regular (b - c) =
      invariantCartierDivisor fan nonempty regular b -
        invariantCartierDivisor fan nonempty regular c :=
  (invariantCartierDivisorHom fan nonempty regular).map_sub b c

/-- Tensoring the two actual invariant Cartier sheaves gives the actual
sheaf of the sum coefficient vector. The first isomorphism is the genuine
multiplication map for Cartier sheaves, and the final transport uses the
proved equality of actual Cartier divisors above. -/
def invariantCartierTensorIso (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (b c : fan.Ray → ℤ) :
    letI := toricSchemeIntegral fan nonempty
    (invariantCartierDivisor fan nonempty regular b).sheaf ⊗
        (invariantCartierDivisor fan nonempty regular c).sheaf ≅
      (invariantCartierDivisor fan nonempty regular (b + c)).sheaf := by
  letI := toricSchemeIntegral fan nonempty
  exact TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.tensorSheafIso
      (invariantCartierDivisor fan nonempty regular b)
      (invariantCartierDivisor fan nonempty regular c) ≪≫
    eqToIso (congrArg TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.sheaf
      (invariantCartierDivisor_add fan nonempty regular b c).symm)

end ToricPower
