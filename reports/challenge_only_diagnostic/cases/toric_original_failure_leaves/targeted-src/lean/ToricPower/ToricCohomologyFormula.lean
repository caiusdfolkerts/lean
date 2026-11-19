module

public import ToricPower.CechToricRayCohomology
public import ToricPower.CechReducedSingular

/-!
# Actual toric cohomology and ordinary reduced singular cohomology

This composes the actual sheaf Čech comparison, every integral character
summand, the augmented Dowker equivalence, and the genuine small-chain
comparison with ordinary singular chains. The negative-ray space is the
standard geometric realization of the literal induced ray complex.

The result is an additive-group isomorphism. It does not claim that an
unspecified torus representation has been identified with its eigenspaces.
The corresponding equivariant statement requires separate action data.

Candidate source, pending pinned compilation.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open TauCeti.Toric
open ToricPower.NegativeSupportCech ToricPower.CechDowkerReduced
open ToricPower.CechReducedSingular
open BondalThomsen.ConvexNerveReducedCochainAcyclicity
open scoped Classical DirectSum

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  {Index : Type} [Fintype Index] (charts : Index → fan.cones)
  (b : fan.Ray → ℤ) (m : N →+ ℤ)

/-- Ordinary geometric realization of the actual negative-ray incidence
complex. Vertices and faces use the full finite ray enumeration, whose
equivalence with the original ray type was proved explicitly. -/
abbrev toricNegativeRaySpace :=
  incidenceRealization
    (negativeRayIncidence (toricEnumeratedRayIncidence fan charts)
      (toricEnumeratedNegative fan b m)) (fun _ => True)

def toricNegativeRayReducedSingularIso (degree : ℕ) :
    toricNegativeRayReduced fan charts b m degree ≅
      reducedSingularCohomology ℂ (toricNegativeRaySpace fan charts b m) degree :=
  incidenceReducedSingularIso
    (negativeRayIncidence (toricEnumeratedRayIncidence fan charts)
      (toricEnumeratedNegative fan b m)) (fun _ => True) ℂ degree

variable (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  (surjective : Function.Surjective charts)

/-- The actual all-character additive cohomology formula. The target is
ordinary reduced singular cohomology of the standard negative-ray
realizations, not a proxy defined from sheaf cohomology. -/
def toricCartierCohomologySingularIso (anchor : Index) (degree : ℕ) :
    letI := toricSchemeIntegral fan nonempty
    AddCommGrpCat.of (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology
      (invariantCartierDivisor fan nonempty regular b).sheaf degree) ≅
      AddCommGrpCat.of (DirectSum (N →+ ℤ) (fun character =>
        ↑(reducedSingularCohomology ℂ
          (toricNegativeRaySpace fan charts b character) degree))) :=
  toricCartierCohomologyNegativeRayIso fan charts b nonempty regular surjective anchor degree ≪≫
    CechDirectSumHomology.directSumIso
      (fun character => toricNegativeRayReduced fan charts b character degree)
      (fun character => reducedSingularCohomology ℂ
        (toricNegativeRaySpace fan charts b character) degree)
      (fun character => toricNegativeRayReducedSingularIso fan charts b character degree)

/-- Every finite regular fan, every Cartier coefficient vector, all
cohomological degrees, and the full integral character lattice. The actual
finite cover and its nonempty anchor are supplied by the fan itself. -/
def toricCartierCohomologyAllSingularIso (degree : ℕ) :
    letI := toricSchemeIntegral fan nonempty
    AddCommGrpCat.of (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology
      (invariantCartierDivisor fan nonempty regular b).sheaf degree) ≅
      AddCommGrpCat.of (DirectSum (N →+ ℤ) (fun character =>
        ↑(reducedSingularCohomology ℂ
          (toricNegativeRaySpace fan (toricFiniteCechCharts fan) b character) degree))) :=
  toricCartierCohomologySingularIso fan (toricFiniteCechCharts fan) b nonempty regular
    (toricFiniteCechCharts_surjective fan)
    (toricCechAnchor fan (toricFiniteCechCharts fan) nonempty
      (toricFiniteCechCharts_surjective fan)) degree

end ToricPower
