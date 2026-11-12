module

public import ToricPower.CechLaurentCoefficients
public import ToricPower.DivisorWeightMonomialMaps

/-!
# Actual monomial sheaf maps in full Laurent coordinates

Multiplication by the actual rational character `u` sends a section of
weight `m` to weight `u + m`, with its complex coefficient unchanged.
The proof compares the actual Cartier-sheaf inclusions in the function
field. It then extends from basis sections to every finite Laurent sum.
No character truncation or maximal-cone restriction is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

open AlgebraicGeometry CategoryTheory TopologicalSpace MonoidAlgebra
open TauCeti.Toric
open scoped Classical

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

/-- The actual regularity inequality proves that translation by the
monomial character sends every source chart weight to a target weight. -/
def toricDivisorWeightMonomialMap (fan : Fan i) (b c : fan.Ray → ℤ)
    (character : N →+ ℤ)
    (nonnegative : ∀ ρ, 0 ≤ c ρ - b ρ + character (fanRayPrimitiveGenerator fan ρ))
    (cone : fan.cones) :
    ToricChartDivisorWeight fan b cone → ToricChartDivisorWeight fan c cone :=
  fun m => ⟨character + m.val, by
    intro ρ
    have original := m.property ρ
    have multiplier := nonnegative (Fan.Ray.ofToricRay fan cone ρ)
    rw [fanRayPrimitiveGenerator_ofToricRay] at multiplier
    simp only [coneDivisorCoefficients, AddMonoidHom.add_apply] at original ⊢
    omega⟩

/-- The actual monomial sheaf map shifts the full Laurent coefficient
family by its character. This is an equality of actual chart sections. -/
theorem toricDivisorSectionCoefficientsEquiv_monomial (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (b c : fan.Ray → ℤ) (character : N →+ ℤ)
    (nonnegative : ∀ ρ, 0 ≤ c ρ - b ρ + character (fanRayPrimitiveGenerator fan ρ))
    (cone : fan.cones) (p : ToricChartDivisorWeight fan b cone →₀ ℂ) :
    letI := toricSchemeIntegral fan nonempty
    Scheme.Modules.Hom.app
      (toricCartierMonomialMap fan nonempty regular b c character nonnegative)
      (fan.affineToricChartι cone).opensRange
      (toricDivisorSectionCoefficientsEquiv fan nonempty regular b cone p) =
    toricDivisorSectionCoefficientsEquiv fan nonempty regular c cone
      (Finsupp.mapDomain (toricDivisorWeightMonomialMap fan b c character nonnegative cone) p) := by
  letI := toricSchemeIntegral fan nonempty
  letI := chartOpen_nonempty fan cone
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, Finsupp.mapDomain_add, hp, hq]
  | single m a =>
    rw [Finsupp.mapDomain_single]
    apply (invariantCartierDivisor fan nonempty regular c).sheafι_app_injective
      (fan.affineToricChartι cone).opensRange
    apply (TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv
      (fan.affineToricChartι cone).opensRange).injective
    rw [toricCartierMonomialMap_value,
      toricDivisorSectionCoefficientsEquiv_single_value,
      toricDivisorSectionCoefficientsEquiv_single_value,
      ← toricIntrinsicLaurentGerm_character, ← map_mul]
    congr 1
    rw [single_mul_single, one_mul]
    rfl

/-- The same computation in the supported submodule of the entire
character lattice: the polynomial is translated, with every coefficient
retained and no finite bound on its possible characters. -/
theorem toricDivisorLaurentCoefficientsEquiv_monomial (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (b c : fan.Ray → ℤ) (character : N →+ ℤ)
    (nonnegative : ∀ ρ, 0 ≤ c ρ - b ρ + character (fanRayPrimitiveGenerator fan ρ))
    (cone : fan.cones)
    (s : letI := toricSchemeIntegral fan nonempty;
      Γ((invariantCartierDivisor fan nonempty regular b).sheaf,
        (fan.affineToricChartι cone).opensRange)) :
    letI := toricSchemeIntegral fan nonempty
    (toricDivisorLaurentCoefficientsEquiv fan nonempty regular c cone
      (Scheme.Modules.Hom.app
        (toricCartierMonomialMap fan nonempty regular b c character nonnegative)
        (fan.affineToricChartι cone).opensRange s)).val =
      Finsupp.mapDomain (fun m : N →+ ℤ => character + m)
        (toricDivisorLaurentCoefficientsEquiv fan nonempty regular b cone s).val := by
  letI := toricSchemeIntegral fan nonempty
  obtain ⟨p, rfl⟩ :=
    (toricDivisorSectionCoefficientsEquiv fan nonempty regular b cone).surjective s
  rw [toricDivisorSectionCoefficientsEquiv_monomial]
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq =>
    simpa only [Finsupp.mapDomain_add, map_add, Submodule.coe_add, hp, hq]
  | single m a =>
    rw [Finsupp.mapDomain_single, toricDivisorLaurentCoefficientsEquiv_single,
      toricDivisorLaurentCoefficientsEquiv_single, Finsupp.mapDomain_single]
    rfl

end ToricPower
