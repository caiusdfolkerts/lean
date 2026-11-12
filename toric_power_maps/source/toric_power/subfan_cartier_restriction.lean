module

public import ToricPower.ToricPulledCartierSheaf
public import ToricPower.RestrictedCartierAtlas
public import ToricPower.SubfanBoundaryCharacters
public import ToricPower.SubfanOpenImmersion

/-!
# Actual Cartier lines restrict to their retained ray coefficients

Restriction to a subfan preserves the lattice and every old primitive
ray. The character pullback therefore has exactly the retained Cartier
coefficients. The global pullback comparison identifies its sheaf with
ordinary open restriction. In particular every boundary twist restricts
to the original line bundle.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory TauCeti.Toric
open Scheme.Modules

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (fan extension : Fan i) (included : fan.cones ⊆ extension.cones)
  (regular : extension.IsRegular) (nonempty : Nonempty fan.cones)

/-- Pullback of the actual invariant Cartier atlas retains precisely
the coefficients of the original rays. -/
theorem subfanInvariantCartierAtlas_eq (b : extension.Ray → ℤ) :
    ((invariantDivisorCharacterAtlas extension regular b).pullback
      (subfanFanHom fan extension included)).cartierDivisor nonempty =
    invariantCartierDivisor fan nonempty (subfan_isRegular fan extension included regular)
      (fun ρ => b (subfanRayEmbedding fan extension included ρ)) := by
  apply ToricCharacterAtlas.cartierDivisor_eq_of_ray_values
    ((invariantDivisorCharacterAtlas extension regular b).pullback
      (subfanFanHom fan extension included))
    (invariantDivisorCharacterAtlas fan (subfan_isRegular fan extension included regular)
      (fun ρ => b (subfanRayEmbedding fan extension included ρ))) nonempty
  intro cone ray
  change coneDivisorCharacter extension regular b
      (fanMapTargetCone (subfanFanHom fan extension included) cone)
      (primitiveGenerator fan.lattice (fan.isToricCone cone.property) ray) =
    coneDivisorCharacter fan (subfan_isRegular fan extension included regular)
      (fun ρ => b (subfanRayEmbedding fan extension included ρ)) cone
      (primitiveGenerator fan.lattice (fan.isToricCone cone.property) ray)
  rw [coneDivisorCharacter_ray,← fanRayPrimitiveGenerator_ofToricRay fan cone ray,
    ← subfanRayEmbedding_primitive fan extension included (Fan.Ray.ofToricRay fan cone ray)]
  apply coneDivisorCharacter_fanRay extension regular b
    (fanMapTargetCone (subfanFanHom fan extension included) cone)
    (subfanRayEmbedding fan extension included (Fan.Ray.ofToricRay fan cone ray))
  change (Fan.Ray.ofToricRay fan cone ray).toCone.val ≤
    (subfanFanHom fan extension included).leastCone cone.property
  rw [subfanFanHom_leastCone]
  exact Fan.Ray.toCone_ofToricRay_le fan cone ray

/-- A global isomorphism of the actual restricted Cartier line sheaf. -/
def subfanInvariantCartierRestrictionIso (b : extension.Ray → ℤ) :
    let newNonempty := nonempty.map (subfanConeEmbedding fan extension included)
    letI := toricSchemeIntegral fan nonempty
    letI := toricSchemeIntegral extension newNonempty
    letI := subfanSchemeMap_isOpenImmersion fan extension included
    (invariantCartierDivisor extension newNonempty regular b).sheaf.restrict
        (subfanSchemeMap fan extension included) ≅
      (invariantCartierDivisor fan nonempty (subfan_isRegular fan extension included regular)
        (fun ρ => b (subfanRayEmbedding fan extension included ρ))).sheaf := by
  let newNonempty := nonempty.map (subfanConeEmbedding fan extension included)
  letI := toricSchemeIntegral fan nonempty
  letI := toricSchemeIntegral extension newNonempty
  letI := subfanSchemeMap_isOpenImmersion fan extension included
  exact ((restrictFunctorIsoPullback (subfanSchemeMap fan extension included)).app
      (invariantCartierDivisor extension newNonempty regular b).sheaf) ≪≫
    ((invariantDivisorCharacterAtlas extension regular b).pullbackSheafIso
      nonempty newNonempty (subfanFanHom fan extension included)).symm ≪≫
    eqToIso (congrArg (fun D => D.sheaf)
      (subfanInvariantCartierAtlas_eq fan extension included regular nonempty b))

/-- Every boundary twist restricts to the original Cartier line. -/
def subfanBoundaryCartierRestrictionIso (b : fan.Ray → ℤ) (a : ℕ) :
    let newNonempty := nonempty.map (subfanConeEmbedding fan extension included)
    letI := toricSchemeIntegral fan nonempty
    letI := toricSchemeIntegral extension newNonempty
    letI := subfanSchemeMap_isOpenImmersion fan extension included
    (invariantCartierDivisor extension newNonempty regular
      (subfanBoundaryTwist fan extension b a)).sheaf.restrict
        (subfanSchemeMap fan extension included) ≅
      (invariantCartierDivisor fan nonempty
        (subfan_isRegular fan extension included regular) b).sheaf := by
  let newNonempty := nonempty.map (subfanConeEmbedding fan extension included)
  letI := toricSchemeIntegral fan nonempty
  letI := toricSchemeIntegral extension newNonempty
  letI := subfanSchemeMap_isOpenImmersion fan extension included
  refine subfanInvariantCartierRestrictionIso fan extension included regular nonempty
    (subfanBoundaryTwist fan extension b a) ≪≫ eqToIso ?_
  congr 2
  funext ρ
  exact subfanBoundaryTwist_old fan extension included b a ρ

end ToricPower

end
