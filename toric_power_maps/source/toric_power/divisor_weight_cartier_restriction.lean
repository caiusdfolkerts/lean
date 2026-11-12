module

public import ToricPower.DivisorWeightCartier

set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[expose] public noncomputable section

/-! ## Source section: DivisorWeightCartierRestriction -/

/-!
# The actual ring map in Cartier coordinates on a face

One Cartier character on a chart also trivializes its restrictions to every
face.  In these trivializations, the restriction of a Laurent-supported divisor
module is exactly the chart coordinate-ring homomorphism.  This is the rank-one
bridge used to identify the associated sheaves with Cartier-divisor sheaves and
to glue their local monomial splitting maps.

These statements do not assert that a global sheaf has already been glued.
They verify the actual algebraic square that the geometric gluing must use.
-/



namespace ToricPower

open MonoidAlgebra

variable {ι ι' κ : Type*} [Fintype κ]

/-- Restricting a Cartier coefficient vector preserves the same Cartier
character.  No new character is chosen on the face. -/
theorem cartierCoefficients_restrict (f : ι' → ι)
    (A : ι → κ → ℤ) (b : ι → ℤ) (q : κ → ℤ) (hq : b = rayMap A q) :
    (fun i => b (f i)) = rayMap (fun i => A (f i)) q := by
  funext i
  exact congrFun hq (f i)

/-- The zero-divisor identification sends section restriction to the actual
coordinate-ring map. -/
theorem chartRingZeroDivisorLinearEquiv_restrict (R : Type*) [Semiring R]
    (f : ι' → ι) (A : ι → κ → ℤ) (a : RayChartRing R A) :
    divisorSectionRestrict R f A 0 1 (chartRingZeroDivisorLinearEquiv R A a) =
      chartRingZeroDivisorLinearEquiv R (fun i => A (f i))
        (rayChartRestrictionHom R f A a) := by
  apply Subtype.ext
  exact (rayChartPower_map_restrict R f A 1 a).symm

/-- The full rank-one restriction square: in the same Cartier generator
`χ^(-q)`, the map is precisely the coordinate-ring homomorphism. -/
theorem divisorCartierTrivialization_restrict (R : Type*) [Semiring R]
    (f : ι' → ι) (A : ι → κ → ℤ) (b : ι → ℤ)
    (q : κ → ℤ) (hq : b = rayMap A q) (a : RayChartRing R A) :
    divisorSectionRestrict R f A b 1 (divisorCartierTrivialization R A b q hq a) =
      divisorCartierTrivialization R (fun i => A (f i)) (fun i => b (f i)) q
        (cartierCoefficients_restrict f A b q hq) (rayChartRestrictionHom R f A a) := by
  apply Subtype.ext
  change mapDomain (rayChartPowerMonoidHom A 1) a *
      single (Multiplicative.ofAdd (-q)) 1 =
    mapDomain (rayChartPowerMonoidHom (fun i => A (f i)) 1)
      (rayChartRestrictionHom R f A a) * single (Multiplicative.ofAdd (-q)) 1
  rw [rayChartPower_map_restrict]

/-- Conjugating the actual divisor-section restriction by its Cartier
trivializations gives the actual chart-ring homomorphism on every section. -/
theorem divisorSectionRestrict_in_cartier_coordinates (R : Type*) [Semiring R]
    (f : ι' → ι) (A : ι → κ → ℤ) (b : ι → ℤ)
    (q : κ → ℤ) (hq : b = rayMap A q) (x : DivisorSectionModule R A b 1) :
    (divisorCartierTrivialization R (fun i => A (f i)) (fun i => b (f i)) q
      (cartierCoefficients_restrict f A b q hq)).symm
        (divisorSectionRestrict R f A b 1 x) =
      rayChartRestrictionHom R f A ((divisorCartierTrivialization R A b q hq).symm x) := by
  have h := divisorCartierTrivialization_restrict R f A b q hq
    ((divisorCartierTrivialization R A b q hq).symm x)
  have h' := congrArg
    (divisorCartierTrivialization R (fun i => A (f i)) (fun i => b (f i)) q
      (cartierCoefficients_restrict f A b q hq)).symm h
  simpa only [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply] using h'

end ToricPower

