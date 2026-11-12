module

public import ToricPower.DivisorWeightCartierAtlas

/-!
# Pulling back toric Cartier character data

A morphism of fans pulls local equation characters back by its genuine
lattice homomorphism. This construction uses no function-field map and
therefore also applies to inclusions of lower-dimensional subtori.

The comparison of character atlases below is an equality of actual Cartier
divisors, proved by uniqueness of gluing in the Cartier-divisor sheaf.
The final identification with pullback of module sheaves is a separate
local-frame compatibility statement.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.Toric

namespace ToricPower

universe u v

variable {N N' : Type u} {V V' : Type v}
  [AddCommGroup N] [AddCommGroup N'] [AddCommGroup V] [AddCommGroup V']
  [Module ℝ V] [Module ℝ V'] {i : N →+ V} {i' : N' →+ V'}
  {source : Fan i} {target : Fan i'}

/-- The actual least target chart containing the image of a source cone. -/
def fanMapTargetCone (mapping : FanHom source target) (cone : source.cones) : target.cones :=
  ⟨mapping.leastCone cone.property, mapping.leastCone_mem cone.property⟩

/-- Regularity of a character is preserved by any actual cone map. -/
theorem character_pullback_mem (mapping : FanHom source target)
    {sourceCone : PointedCone ℝ V} {targetCone : PointedCone ℝ V'}
    (mapsTo : Set.MapsTo mapping.realMap sourceCone targetCone)
    {character : N' →+ ℤ} (regular : character ∈ dualSemigroup target.lattice targetCone) :
    character.comp mapping.latticeMap ∈ dualSemigroup source.lattice sourceCone := by
  rw [mem_dualSemigroup, source.lattice.realCharacter_comp target.lattice
    mapping.latticeMap mapping.realMap mapping.map_lattice]
  intro point present
  exact (mem_dualSemigroup target.lattice character).mp regular (mapsTo present)

namespace ToricCharacterAtlas

/-- Pull back local equation characters through the actual map of lattices. -/
def pullback (atlas : ToricCharacterAtlas target) (mapping : FanHom source target) :
    ToricCharacterAtlas source where
  equation cone := (atlas.equation (fanMapTargetCone mapping cone)).comp mapping.latticeMap
  positive first second := by
    have mapsTo : Set.MapsTo mapping.realMap (first ⊓ second).val
        ((fanMapTargetCone mapping first) ⊓ (fanMapTargetCone mapping second)).val :=
      fun _point present =>
        ⟨mapping.mapsTo_leastCone first.property present.1,
          mapping.mapsTo_leastCone second.property present.2⟩
    simpa only [AddMonoidHom.sub_comp] using
      character_pullback_mem mapping mapsTo
        (atlas.positive (fanMapTargetCone mapping first) (fanMapTargetCone mapping second))
  negative first second := by
    have mapsTo : Set.MapsTo mapping.realMap (first ⊓ second).val
        ((fanMapTargetCone mapping first) ⊓ (fanMapTargetCone mapping second)).val :=
      fun _point present =>
        ⟨mapping.mapsTo_leastCone first.property present.1,
          mapping.mapsTo_leastCone second.property present.2⟩
    simpa only [AddMonoidHom.sub_comp, AddMonoidHom.neg_comp] using
      character_pullback_mem mapping mapsTo
        (atlas.negative (fanMapTargetCone mapping first) (fanMapTargetCone mapping second))

@[simp]
theorem pullback_equation (atlas : ToricCharacterAtlas target) (mapping : FanHom source target)
    (cone : source.cones) :
    (atlas.pullback mapping).equation cone =
      (atlas.equation (fanMapTargetCone mapping cone)).comp mapping.latticeMap := rfl

variable {fan : Fan i}

/-- Local equation characters differing by regular units define the same
actual global Cartier divisor. -/
theorem cartierDivisor_eq_of_equation_difference_units
    (first second : ToricCharacterAtlas fan) (nonempty : Nonempty fan.cones)
    (positive : ∀ cone, first.equation cone - second.equation cone ∈
      dualSemigroup fan.lattice cone.val)
    (negative : ∀ cone, -(first.equation cone - second.equation cone) ∈
      dualSemigroup fan.lattice cone.val) :
    first.cartierDivisor nonempty = second.cartierDivisor nonempty := by
  letI := toricSchemeIntegral fan nonempty
  let firstAtlas := first.cartierEquationAtlas nonempty
  apply firstAtlas.existsUnique_cartierDivisor.unique
    firstAtlas.existsUnique_cartierDivisor.exists.choose_spec
  intro cone
  letI := chartOpen_nonempty fan cone
  change second.cartierDivisor nonempty |_ (fan.affineToricChartι cone).opensRange =
    TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass fan.algebraicRealization
      (fan.affineToricChartι cone).opensRange
      (Additive.ofMul (rationalCharacterUnit fan nonempty (first.equation cone)))
  rw [second.cartierDivisor_restrict]
  symm
  apply (TauCeti.AlgebraicGeometry.Scheme.rationalUnitClass_eq_rationalUnitClass_iff
    fan.algebraicRealization (fan.affineToricChartι cone).opensRange _ _).mpr
  refine ⟨Units.map (chartCoordinateSectionsEquiv fan cone).toMonoidHom
    (toricMonomialUnit fan.lattice cone.val (first.equation cone - second.equation cone)
      (positive cone) (negative cone)), ?_⟩
  rw [chartCoordinateGerm_regularUnit, chartCoordinateGerm_monomialUnit]
  exact rationalCharacterUnit_sub_mul fan nonempty _ _

/-- Agreement on every primitive ray suffices to identify the actual
Cartier divisors. No smoothness or completeness assumption is needed. -/
theorem cartierDivisor_eq_of_ray_values
    (first second : ToricCharacterAtlas fan) (nonempty : Nonempty fan.cones)
    (equal : ∀ cone (ray : ToricRay cone.val),
      first.equation cone (primitiveGenerator fan.lattice (fan.isToricCone cone.property) ray) =
      second.equation cone (primitiveGenerator fan.lattice (fan.isToricCone cone.property) ray)) :
    first.cartierDivisor nonempty = second.cartierDivisor nonempty := by
  apply cartierDivisor_eq_of_equation_difference_units first second nonempty
  · intro cone
    rw [mem_dualSemigroup_iff_primitiveGenerator fan.lattice (fan.isToricCone cone.property)]
    intro ray
    simp only [AddMonoidHom.sub_apply, equal cone ray, sub_self, le_refl]
  · intro cone
    rw [mem_dualSemigroup_iff_primitiveGenerator fan.lattice (fan.isToricCone cone.property)]
    intro ray
    simp only [AddMonoidHom.neg_apply, AddMonoidHom.sub_apply, equal cone ray,
      sub_self, neg_zero, le_refl]

end ToricCharacterAtlas

end ToricPower
