module

public import ToricPower.CompleteFanFiniteWeights
public import ToricPower.ToricCohomologyFormula

/-!
# Finite weight support in the actual toric Čech formula

The complete-fan geometric finiteness theorem specializes to the literal
negative-ray spaces in the all-character sheaf-cohomology formula. Every
integral character and every reduced degree remain in the statement.

The equivalent Čech statement uses the actual proved additive comparison.
No claim about finite-dimensional complex vector spaces is inferred from
an additive-group isomorphism.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory TauCeti.Toric
open ToricPower.CechDowkerReduced ToricPower.CechReducedSingular

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  {Index : Type} [Fintype Index] (charts : Index → fan.cones)
  (surjective : Function.Surjective charts)
  (regular : fan.IsRegular) (complete : fan.IsComplete) (b : fan.Ray → ℤ)

include surjective regular complete

/-- Only finitely many terms of the full integral-character cohomology
formula can be nonzero, simultaneously over every cohomological degree. -/
theorem toricNegativeRayCohomology_nonzeroWeightSet_finite :
    {m : N →+ ℤ | ∃ degree, Nontrivial (reducedSingularCohomology ℂ
      (toricNegativeRaySpace fan charts b m) degree)}.Finite := by
  exact completeFan_nonzeroWeightSet_finite_algebraic fan charts surjective
    (toricFiniteRayEquiv fan) ℂ regular complete b

/-- The same finite support statement for homology of the actual
all-character affine Čech weight complexes. -/
theorem toricCechCohomology_nonzeroWeightSet_finite (anchor : Index) :
    {m : N →+ ℤ | ∃ degree, Nontrivial
      ((toricCechWeightComplex fan charts b m).homology degree)}.Finite := by
  apply (toricNegativeRayCohomology_nonzeroWeightSet_finite
    fan charts surjective regular complete b).subset
  rintro m ⟨degree, nonzero⟩
  refine ⟨degree, ?_⟩
  let equivalence := toricCechWeightRayReducedIso fan charts b m anchor degree ≪≫
    toricNegativeRayReducedSingularIso fan charts b m degree
  exact equivalence.addCommGroupIsoToAddEquiv.toEquiv.nontrivial_congr.mp nonzero

end ToricPower
