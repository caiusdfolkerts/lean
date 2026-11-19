module

public import PaperVerification.KoszulBarObstruction
public import PaperVerification.AlternatingFormsExteriorGenericHilbert
public import PaperVerification.AlternatingFormsQuadraticDualTensorHilbert

/-!
# The actual exterior quotient and quadratic-dual series obstruction

This file specializes the proved formal-series contradiction to the literal
exterior quotient and its annihilator-defined tensor quadratic dual. The
injectivity hypothesis is the precise input to the separate PBW theorem;
this result is not the full generic Koszul classification.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators PowerSeries

namespace PaperVerification.KoszulBarObstruction

open PaperVerification.AlternatingForms

def actualExteriorSeries {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    (f g : ⋀[K]^2 M) : ℤ⟦X⟧ :=
  PowerSeries.mk (fun d => (Module.finrank K (ExteriorQuotientDegree f g d) : ℤ))

/-- This obstruction uses the literal exterior quotient and the actual
annihilator-defined tensor quadratic dual, not arbitrary Hilbert series. -/
theorem actual_exterior_dual_no_koszul_identity
    {K ν : Type*} [Field K] [CharZero K] [Fintype ν] [LinearOrder ν] [Nonempty ν]
    (f g : ⋀[K]^2 (ν → K))
    (hinj : Function.Injective (orbitExteriorRelationMap f g 1)) :
    actualExteriorSeries f g *
      PowerSeries.rescale (-1 : ℤ) (QuadraticDual.tensorHilbertSeries f g)≠1 := by
  apply no_bounded_koszul_identity (Fintype.card ν)
  · simp only [actualExteriorSeries,PowerSeries.coeff_mk]
    rw [exteriorQuotientDegree_finrank_eq_zero_high f g _ (by simp),Nat.cast_zero]
  · exact QuadraticDual.tensorHilbertSeries_mul_denominator_eq_one f g hinj

end PaperVerification.KoszulBarObstruction
