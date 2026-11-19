module

public import ToricPower.ArrangementNormalizedCoverLift
public import ToricPower.WeightedCoverFiniteSupport

/-! # The actual normalized Cartier covering lift has finite homological fibers -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  [nonempty : Nonempty fan.cones] (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

include regular in
/-- This is a property of the original full Čech complex, for every
integer degree, every quotient cell, and every integral character. -/
theorem arrangementNormalizedCoverComplex_finite_support
    (complete : fan.IsComplete) (b : fan.Ray → ℤ) (q : ℤ)
    (c : IncidenceObject (fanArrangementMatrix fan basis rays)) :
    {m : (universalWeightFunctor (fanArrangementMatrix fan basis rays)).obj c | ¬ IsZero
      (((arrangementNormalizedCoverComplex fan basis rays b).homology q).obj
        ((universalWeightFunctor (fanArrangementMatrix fan basis rays)).elementsMk c m))}.Finite :=
  weightedCoverLiftComplex_finite_support (fanArrangementMatrix fan basis rays) ℂ
    (arrangementNormalizedLiftedCech fan basis rays b)
    (arrangementNormalizedLiftedSupport_finite fan regular basis rays complete b) q c

end ToricPower

end
