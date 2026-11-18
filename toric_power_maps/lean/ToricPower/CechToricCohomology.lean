module

public import ToricPower.CechCharacterDirectSum
public import ToricPower.CechNegativeRelative
public import ToricPower.ToricSeparated

/-!
# Actual toric line-sheaf cohomology and character complexes

This module composes the genuine finite-affine Čech comparison, actual
Laurent-section comparison, finite-support character decomposition, and
AB4 homology comparison. Its source is actual Zariski sheaf cohomology.
The final combinatorial target here is the negative *chart* nerve. The
separate chart-versus-ray nerve equivalence remains explicit work.

Every finite regular fan is allowed; no completeness or spanning-ray
hypothesis is introduced. Candidate source, pending pinned compilation.
-/

@[expose] public noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open TauCeti.Toric
open scoped Classical DirectSum

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {Index : Type} [Fintype Index] (charts : Index → fan.cones)
  (surjective : Function.Surjective charts) (b : fan.Ray → ℤ)

/-- Actual sheaf cohomology of the invariant Cartier line sheaf is the
literal direct sum of the relative incidence homologies of all characters. -/
def toricCartierCohomologyWeightSumIso (degree : ℕ) :
    letI := toricSchemeIntegral fan nonempty
    AddCommGrpCat.of (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology
      (invariantCartierDivisor fan nonempty regular b).sheaf degree) ≅
      AddCommGrpCat.of (DirectSum (N →+ ℤ)
        (fun m => ↑((toricCechWeightComplex fan charts b m).homology degree))) := by
  letI := toricSchemeIntegral fan nonempty
  letI := toricScheme_isNoetherian fan
  letI := fan.algebraicRealization_isSeparated
  letI := (invariantCartierDivisor fan nonempty regular b).isInvertible_sheaf
  exact BondalThomsen.FiniteAffineCechAllDegreeComparison.cechSchemeCohomologyIso
      (toricCechChartOpen fan charts)
      (toricCechChartOpen_covers fan charts surjective).iSup_eq_top
      (toricCechChartOpen_isAffine fan charts)
      (invariantCartierDivisor fan nonempty regular b).sheaf degree ≪≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) degree).mapIso
      (toricCechLaurentComplexIso fan charts b nonempty regular) ≪≫
    toricCechLaurentHomologyWeightSumIso fan charts b degree

/-- A genuine all-degree comparison with reduced cohomology of the
negative chart nerve, including the augmented degree-minus-one group. -/
def toricCartierCohomologyNegativeChartIso (anchor : Index) (degree : ℕ) :
    letI := toricSchemeIntegral fan nonempty
    AddCommGrpCat.of (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology
      (invariantCartierDivisor fan nonempty regular b).sheaf degree) ≅
      AddCommGrpCat.of (DirectSum (N →+ ℤ) (fun m =>
        ↑(NegativeSupportRelative.negativeReducedShifted ℂ
          (toricCechRayIncidence fan charts) (toricCharacterNegative fan b m) anchor degree))) :=
  toricCartierCohomologyWeightSumIso fan nonempty regular charts surjective b degree ≪≫
    CechDirectSumHomology.directSumIso
      (fun m => (toricCechWeightComplex fan charts b m).homology degree)
      (fun m => NegativeSupportRelative.negativeReducedShifted ℂ
        (toricCechRayIncidence fan charts) (toricCharacterNegative fan b m) anchor degree)
      (fun m =>
      NegativeSupportRelative.relativeHomologyReducedIso ℂ
        (toricCechRayIncidence fan charts) (toricCharacterNegative fan b m) anchor degree)

/-- A finite enumeration of all actual fan cones. It does not select
only full-dimensional or maximal cones. -/
def toricFiniteCechCharts : Fin (Nat.card fan.cones) → fan.cones :=
  (Finite.equivFin fan.cones).symm

theorem toricFiniteCechCharts_surjective :
    Function.Surjective (toricFiniteCechCharts fan) :=
  (Finite.equivFin fan.cones).symm.surjective

/-- The enumeration and affine-cover hypotheses are discharged for every
nonempty finite regular fan. The target still uses its actual full lattice. -/
def toricCartierCohomologyAllWeightsIso (degree : ℕ) :
    letI := toricSchemeIntegral fan nonempty
    AddCommGrpCat.of (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology
      (invariantCartierDivisor fan nonempty regular b).sheaf degree) ≅
      AddCommGrpCat.of (DirectSum (N →+ ℤ)
        (fun m => ↑((toricCechWeightComplex fan (toricFiniteCechCharts fan) b m).homology degree))) :=
  toricCartierCohomologyWeightSumIso fan nonempty regular (toricFiniteCechCharts fan)
    (toricFiniteCechCharts_surjective fan) b degree

include surjective in
/-- The all-character decomposition detects nonvanishing in each actual
sheaf-cohomology degree. No bounded character search is involved. -/
theorem toricCartierCohomologyWeight_nontrivial_iff (degree : ℕ) :
    letI := toricSchemeIntegral fan nonempty
    Nontrivial (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology
      (invariantCartierDivisor fan nonempty regular b).sheaf degree) ↔
      ∃ character : N →+ ℤ,
        Nontrivial ((toricCechWeightComplex fan charts b character).homology degree) := by
  letI := toricSchemeIntegral fan nonempty
  exact (toricCartierCohomologyWeightSumIso fan nonempty regular charts surjective b degree).addCommGroupIsoToAddEquiv.toEquiv.nontrivial_congr.trans
      (CechDirectSumHomology.directSum_nontrivial_iff (fun character =>
        (toricCechWeightComplex fan charts b character).homology degree))

include surjective in
theorem toricCartierCohomologyWeight_nonzero_iff :
    letI := toricSchemeIntegral fan nonempty
    (∃ degree : ℕ, Nontrivial (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology
      (invariantCartierDivisor fan nonempty regular b).sheaf degree)) ↔
      ∃ character : N →+ ℤ, ∃ degree : ℕ,
        Nontrivial ((toricCechWeightComplex fan charts b character).homology degree) := by
  letI := toricSchemeIntegral fan nonempty
  constructor
  · rintro ⟨degree, nonzero⟩
    obtain ⟨character, nonzero⟩ :=
      (toricCartierCohomologyWeight_nontrivial_iff
        fan nonempty regular charts surjective b degree).mp nonzero
    exact ⟨character, degree, nonzero⟩
  · rintro ⟨character, degree, nonzero⟩
    exact ⟨degree, (toricCartierCohomologyWeight_nontrivial_iff
      fan nonempty regular charts surjective b degree).mpr ⟨character, nonzero⟩⟩

end ToricPower
