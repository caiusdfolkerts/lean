module

public import ToricPower.SchemeCechScalarComparison
public import ToricPower.CechLinearFiniteDimensional
public import ToricPower.ToricInvariantLineBundleClassification
public import ToricPower.ToricCoherentCohomologyFiniteness

/-!
# Finite-dimensional ordinary coherent cohomology on complete smooth toric varieties

The actual complex-linear Čech comparison transfers the finite-character
calculation to ordinary sheaf cohomology with its specified complex scalar
action. Actual invariant representatives cover every line bundle. Finally,
finite Cartier epimorphisms and the uniform affine-cover vanishing bound
prove finite-dimensionality for every coherent sheaf and every degree.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric
open TauCeti.AlgebraicGeometry.Scheme.Modules

namespace ToricPower

universe v
variable {N : Type} {V : Type v} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

/-- Every invariant Cartier sheaf has finite-dimensional ordinary
cohomology over the actual complex base field. -/
theorem toricInvariantCartierCohomology_finite (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular) (complete : fan.IsComplete)
    (b : fan.Ray → ℤ) (degree : ℕ) :
    letI := toricSchemeIntegral fan nonempty
    FiniteDimensional ℂ
      (Cohomology (invariantCartierDivisor fan nonempty regular b).sheaf degree) := by
  letI := toricSchemeIntegral fan nonempty
  letI := toricScheme_isNoetherian fan
  letI := fan.algebraicRealization_isSeparated
  letI : Fintype (ToricMeetChartIndex fan) := Fintype.ofFinite _
  let charts := toricMeetChartEquiv fan
  let anchor : ToricMeetChartIndex fan := charts.symm (Classical.choice nonempty)
  letI := (invariantCartierDivisor fan nonempty regular b).isInvertible_sheaf
  letI : FiniteDimensional ℂ
      (((CechScalar.linearComplexFunctor ℂ fan.algebraicRealization
        (toricCechChartOpen fan charts)).obj
          (invariantCartierDivisor fan nonempty regular b).sheaf).homology degree) := by
    change FiniteDimensional ℂ
      ((toricCechActualLinearComplex fan charts b nonempty regular).homology degree)
    exact toricCechActualLinearHomology_finite fan charts b charts.surjective
      regular complete anchor nonempty degree
  let comparison := CechScalar.quasicoherentLinearCechIso ℂ fan.algebraicRealization
    (toricCechChartOpen fan charts)
    (toricCechChartOpen_covers fan charts charts.surjective).iSup_eq_top
    (fun a => isAffineOpen_opensRange (fan.affineToricChartι (charts a)))
    (invariantCartierDivisor fan nonempty regular b).sheaf degree
  exact Module.Finite.equiv comparison.symm.toLinearEquiv

/-- Invariant representatives transfer actual linear cohomology
finiteness to every invertible sheaf, with no linearization assumption. -/
theorem toricInvertibleCohomology_finite (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular) (complete : fan.IsComplete)
    (F : fan.algebraicRealization.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible fan.algebraicRealization F]
    (degree : ℕ) : FiniteDimensional ℂ (Cohomology F degree) := by
  letI := toricSchemeIntegral fan nonempty
  letI : FiniteDimensional ℂ
      ((cohomologyBaseFunctor ℂ fan.algebraicRealization degree).obj
        (invariantCartierDivisor fan nonempty regular
          (toricLineBundleInvariantCoefficients fan nonempty regular F)).sheaf) := by
    change FiniteDimensional ℂ (Cohomology
      (invariantCartierDivisor fan nonempty regular
        (toricLineBundleInvariantCoefficients fan nonempty regular F)).sheaf degree)
    exact toricInvariantCartierCohomology_finite fan nonempty regular complete
      (toricLineBundleInvariantCoefficients fan nonempty regular F) degree
  exact Module.Finite.equiv
    ((cohomologyBaseFunctor ℂ fan.algebraicRealization degree).mapIso
      (toricLineBundleInvariantIso fan nonempty regular F)).symm.toLinearEquiv

/-- All coherent sheaves on an arbitrary complete smooth toric variety
have finite-dimensional ordinary cohomology in every degree. All scalar
structures are the canonical actions of the actual complex base field. -/
theorem toricCoherentCohomology_finite (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular) (complete : fan.IsComplete)
    (M : fan.algebraicRealization.Modules) [M.IsFinitePresentation] (degree : ℕ) :
    FiniteDimensional ℂ (Cohomology M degree) := by
  letI := toricSchemeIntegral fan nonempty
  exact toricCoherentCohomology_finite_of_cartier fan nonempty regular
    (fun D n => by
      letI := D.isInvertible_sheaf
      exact toricInvertibleCohomology_finite fan nonempty regular complete D.sheaf n)
    M degree

end ToricPower

end
