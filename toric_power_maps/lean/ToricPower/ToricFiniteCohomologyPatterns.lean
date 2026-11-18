module

public import ToricPower.ToricCohomologyFormula
public import ToricPower.FiniteNegativePatterns

/-!
# The finite integer-pattern criterion for actual toric cohomology

For each subset of the actual finite ray set, the topological test is
ordinary reduced singular cohomology of the induced ray complex. The
integer feasibility condition uses every character of the full integral
lattice and exactly the inequalities in Section 5: at most −1 on the
selected rays and at least zero on the other rays. Actual nonvanishing of
the invariant Cartier line's Zariski cohomology is equivalent to one of
these finitely many simultaneous tests.

This statement is cohomological and does not assert classical generation.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 400000

open AlgebraicGeometry CategoryTheory TauCeti.Toric
open ToricPower.NegativeSupportCech ToricPower.CechReducedSingular
open ToricPower.FiniteNegativePatterns ToricPower.CechDowkerReduced
open BondalThomsen.ConvexNerveReducedCochainAcyclicity
open scoped Classical
namespace ToricPower
variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

/-- Ordinary reduced cohomological nonvanishing of the actual induced
ray complex, with all degrees at least minus one included. -/
def toricRaySelectionHasCohomology (fan : Fan i)
    (negative : Fin (Nat.card fan.Ray) → Prop) : Prop :=
  ∃ degree : ℕ, Nontrivial (reducedSingularCohomology ℂ
    (incidenceRealization
      (negativeRayIncidence
        (toricEnumeratedRayIncidence fan (toricFiniteCechCharts fan)) negative)
      (fun _ => True)) degree)

/-- The paper's set of cohomologically nonzero ray subsets. -/
def toricPatternHasCohomology (fan : Fan i) (negative : Finset (Fin (Nat.card fan.Ray))) : Prop :=
  toricRaySelectionHasCohomology fan (fun ray => ray ∈ negative)

/-- The exact integral affine ray-pairing values. -/
def toricPatternValues (fan : Fan i) (b : fan.Ray → ℤ)
    (character : N →+ ℤ) (ray : Fin (Nat.card fan.Ray)) : ℤ :=
  b (toricFiniteRayEquiv fan ray) +
    character (fanRayPrimitiveGenerator fan (toricFiniteRayEquiv fan ray))

/-- The selected pattern is realized by a character of the full lattice.
This is precisely lattice-point feasibility of the displayed inequalities. -/
def toricPatternLatticeFeasible (fan : Fan i) (b : fan.Ray → ℤ)
    (negative : Finset (Fin (Nat.card fan.Ray))) : Prop :=
  latticeFeasible (toricPatternValues fan b) negative

/-- A finite disjunction of induced-complex cohomology and exact integer
feasibility, with no bounded search for characters. -/
def toricFiniteCohomologyPatternCriterion (fan : Fan i) (b : fan.Ray → ℤ) : Prop :=
  ∃ negative ∈ (Finset.univ : Finset (Fin (Nat.card fan.Ray))).powerset,
    toricPatternHasCohomology fan negative ∧ toricPatternLatticeFeasible fan b negative

/-- Recording signs by a finite set changes none of the selected vertices. -/
theorem toricPatternHasCohomology_negativeSet (fan : Fan i) (b : fan.Ray → ℤ)
    (character : N →+ ℤ) :
    toricPatternHasCohomology fan (negativeSet (toricPatternValues fan b character)) ↔
      toricRaySelectionHasCohomology fan (toricEnumeratedNegative fan b character) := by
  have same : (fun ray => ray ∈ negativeSet (toricPatternValues fan b character)) =
      toricEnumeratedNegative fan b character := by
    funext ray
    apply propext
    rw [mem_negativeSet]
    rfl
  change toricRaySelectionHasCohomology fan _ ↔ _
  rw [same]

/-- The full all-character cohomology decomposition detects exactly the
actual induced-ray topological tests. -/
theorem toricCartierCohomology_nonzero_iff_raySelection (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular) (b : fan.Ray → ℤ) :
    letI := toricSchemeIntegral fan nonempty
    (∃ degree : ℕ, Nontrivial (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology
      (invariantCartierDivisor fan nonempty regular b).sheaf degree)) ↔
    ∃ character : N →+ ℤ,
      toricRaySelectionHasCohomology fan (toricEnumeratedNegative fan b character) := by
  letI := toricSchemeIntegral fan nonempty
  have eachDegree (degree : ℕ) :=
    (toricCartierCohomologyAllSingularIso fan b nonempty regular degree).addCommGroupIsoToAddEquiv.toEquiv.nontrivial_congr.trans
      (CechDirectSumHomology.directSum_nontrivial_iff (fun character =>
        reducedSingularCohomology ℂ
          (toricNegativeRaySpace fan (toricFiniteCechCharts fan) b character) degree))
  constructor
  · rintro ⟨degree, nonzero⟩
    obtain ⟨character, nonzero⟩ := (eachDegree degree).mp nonzero
    exact ⟨character, degree, nonzero⟩
  · rintro ⟨character, degree, nonzero⟩
    exact ⟨degree, (eachDegree degree).mpr ⟨character, nonzero⟩⟩

/-- The exact finite-pattern reformulation of nonvanishing of the actual
Cartier sheaf's total cohomology, on every nonempty regular finite fan. -/
theorem toricCartierCohomology_nonzero_iff_finitePattern (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular) (b : fan.Ray → ℤ) :
    letI := toricSchemeIntegral fan nonempty
    (∃ degree : ℕ, Nontrivial (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology
      (invariantCartierDivisor fan nonempty regular b).sheaf degree)) ↔
      toricFiniteCohomologyPatternCriterion fan b := by
  letI := toricSchemeIntegral fan nonempty
  exact (toricCartierCohomology_nonzero_iff_raySelection fan nonempty regular b).trans
    ((exists_congr fun character =>
      (toricPatternHasCohomology_negativeSet fan b character).symm).trans
      (exists_character_iff_finite_pattern (toricPatternValues fan b)
        (toricPatternHasCohomology fan)))

end ToricPower
