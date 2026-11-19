module

public import ToricPower.ToricCartierSectionsLinear
public import ToricPower.CechLaurentCoefficients

/-!
# Complex-linear Laurent coordinates on every Čech intersection

The scalars on sections come from the specified toric structure map to
`Spec ℂ`. The coefficient scalars are the ordinary ones on Laurent
polynomials. The comparison is exactly the already checked additive
coordinate map, now proved linear for these two actual actions.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Opposite
open TauCeti.Toric

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)

/-- The full Laurent-coordinate map is linear for the specified actions. -/
def toricDivisorLaurentCoefficientsLinearEquiv (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (b : fan.Ray → ℤ) (cone : fan.cones) :
    letI := toricSchemeIntegral fan nonempty
    (FiniteCover.schemeBaseSections ℂ fan.algebraicRealization
      (fan.affineToricChartι cone).opensRange).obj
        (invariantCartierDivisor fan nonempty regular b).sheaf ≃ₗ[ℂ]
      ToricChartLaurentCoefficients fan b cone :=
  (toricDivisorSectionCoefficientsLinearEquiv fan nonempty regular b cone).symm.trans
    ((Finsupp.domLCongr (R := ℂ) (toricChartWeightGlobalEquiv fan b cone)).trans
      (Finsupp.supportedEquivFinsupp (R := ℂ)
        {m : N →+ ℤ | toricCharacterAllowed fan b cone m}).symm)

/-- No change of the underlying Laurent coordinate map is made. -/
theorem toricDivisorLaurentCoefficientsLinearEquiv_toAddEquiv
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (b : fan.Ray → ℤ) (cone : fan.cones) :
    (toricDivisorLaurentCoefficientsLinearEquiv fan nonempty regular b cone).toAddEquiv =
      toricDivisorLaurentCoefficientsEquiv fan nonempty regular b cone := rfl

/-- Equality of actual opens transports their specified base-field sections. -/
def baseSectionOpenLinearEquiv (k : Type) [Field k] (X : Scheme)
    [X.Over (Spec (.of k))] (F : X.Modules) {U W : X.Opens} (h : U = W) :
    (FiniteCover.schemeBaseSections k X U).obj F ≃ₗ[k]
      (FiniteCover.schemeBaseSections k X W).obj F :=
  (eqToIso (congrArg (fun U => (FiniteCover.schemeBaseSections k X U).obj F) h)).toLinearEquiv

/-- The linear equality transport has the original additive transport. -/
theorem baseSectionOpenLinearEquiv_toAddEquiv (k : Type) [Field k] (X : Scheme)
    [X.Over (Spec (.of k))] (F : X.Modules) {U W : X.Opens} (h : U = W) :
    (baseSectionOpenLinearEquiv k X F h).toAddEquiv = toricSectionOpenEquiv X F h := by
  subst W
  rfl

variable {Index : Type} (charts : Index → fan.cones)

/-- The actual base-field section module on a tuple intersection. -/
abbrev toricCechActualLinearCoefficient (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (b : fan.Ray → ℤ) (degree : ℕ)
    (tuple : Fin (degree + 1) → Index) : ModuleCat ℂ :=
  letI := toricSchemeIntegral fan nonempty
  (FiniteCover.schemeBaseSections ℂ fan.algebraicRealization
    (BondalThomsen.FiniteAffineCechHigherComparison.cechIntersection
      (toricCechChartOpen fan charts) degree tuple)).obj
        (invariantCartierDivisor fan nonempty regular b).sheaf

/-- Ordinary Laurent polynomials with precisely the actual chart support. -/
abbrev toricCechLaurentLinearCoefficient (b : fan.Ray → ℤ) (degree : ℕ)
    (tuple : Fin (degree + 1) → Index) : ModuleCat ℂ :=
  ModuleCat.of ℂ (ToricChartLaurentCoefficients fan b
    (toricCechCone fan charts degree tuple))

/-- Every tuple's full section comparison is complex-linear. -/
def toricCechCoefficientLinearEquiv (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (b : fan.Ray → ℤ) (degree : ℕ)
    (tuple : Fin (degree + 1) → Index) :
    toricCechActualLinearCoefficient fan charts nonempty regular b degree tuple ≃ₗ[ℂ]
      toricCechLaurentLinearCoefficient fan charts b degree tuple := by
  letI := toricSchemeIntegral fan nonempty
  exact (baseSectionOpenLinearEquiv ℂ fan.algebraicRealization
      (invariantCartierDivisor fan nonempty regular b).sheaf
      (toricCechIntersection_eq_chart fan charts degree tuple)).trans
    (toricDivisorLaurentCoefficientsLinearEquiv fan nonempty regular b
      (toricCechCone fan charts degree tuple))

/-- The comparison retains every previously verified restriction and
monomial coefficient formula literally. -/
theorem toricCechCoefficientLinearEquiv_toAddEquiv (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (b : fan.Ray → ℤ) (degree : ℕ)
    (tuple : Fin (degree + 1) → Index) :
    (toricCechCoefficientLinearEquiv fan charts nonempty regular b degree tuple).toAddEquiv =
      toricCechCoefficientEquiv fan charts nonempty regular b degree tuple := by
  letI := toricSchemeIntegral fan nonempty
  change (baseSectionOpenLinearEquiv ℂ fan.algebraicRealization
      (invariantCartierDivisor fan nonempty regular b).sheaf
      (toricCechIntersection_eq_chart fan charts degree tuple)).toAddEquiv.trans
      (toricDivisorLaurentCoefficientsLinearEquiv fan nonempty regular b
        (toricCechCone fan charts degree tuple)).toAddEquiv = _
  rw [baseSectionOpenLinearEquiv_toAddEquiv,
    toricDivisorLaurentCoefficientsLinearEquiv_toAddEquiv]
  rfl

/-- The linear map and the original additive map agree on every section. -/
theorem toricCechCoefficientLinearEquiv_apply (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (b : fan.Ray → ℤ) (degree : ℕ)
    (tuple : Fin (degree+1) → Index)
    (x : toricCechActualLinearCoefficient fan charts nonempty regular b degree tuple) :
    toricCechCoefficientLinearEquiv fan charts nonempty regular b degree tuple x =
      toricCechCoefficientEquiv fan charts nonempty regular b degree tuple x :=
  DFunLike.congr_fun
    (toricCechCoefficientLinearEquiv_toAddEquiv fan charts nonempty regular b degree tuple) x

end ToricPower
