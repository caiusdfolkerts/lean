module

public import PaperVerification.E6ClassCount
public import PaperVerification.E6Normalization
public import PaperVerification.E7Roots
public import PaperVerification.E7TranslationClasses
public import PaperVerification.E8PaperTheorems
public import PaperVerification.E8TranslationClasses
public import PaperVerification.DnTranslationClasses
public import PaperVerification.BWTranslationClasses
public import PaperVerification.BWThetaFormula
public import PaperVerification.BWNorm
public import PaperVerification.LatticeMixtures
public import PaperVerification.LatticeMixturesExtended
public import PaperVerification.LatticeMetricMeaning
public import PaperVerification.E7MetricMeaning
public import PaperVerification.E7PaperRepresentatives

@[expose] public section

/-! # Explicit endpoints for the cold-spots manuscript

These declarations collect the full statements in one place.  The coordinate
sets and the predicates are those used throughout the proofs; no additional
analytic, geometric, integrality, or finite-support hypothesis is introduced.
The Euclidean metric interpretation is proved in `LatticeMetricMeaning` and
`E7MetricMeaning`, and the lattice normalizations have separate root/code proofs.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open MeasureTheory
open PaperVerification.PositiveMixtures
open scoped ENNReal

/-- Theorem 1.1, including every even dimension n≥8 and every α>0. -/
theorem lattice_theorem_1_1 :
    (∀ α : ℝ, 0 < α → ∀ x : Fin 6 → ℝ,
      IsColdSpot e6Set α x ↔ IsDeepHole e6Set x) ∧
    (∀ α : ℝ, 0 < α → ∀ x : Fin 8 → ℝ,
      IsColdSpot (dPlusSet 8) α x ↔ IsDeepHole (dPlusSet 8) x) ∧
    (∀ α : ℝ, 0 < α → ∀ x : zeroSumSpace,
      IsE7ColdSpot α x ↔ IsE7DeepHole x) ∧
    (∀ α : ℝ, 0 < α → ∀ x : Fin 16 → ℝ,
      IsColdSpot bw16Set α x ↔ IsDeepHole bw16Set x) ∧
    (∀ n : ℕ, 8 ≤ n → Even n → ∀ α : ℝ, 0 < α → ∀ x : Fin n → ℝ,
      IsColdSpot (dPlusSet n) α x ↔ IsDeepHole (dPlusSet n) x) :=
  ⟨fun _ hα x ↦ coldSpot_E6_iff_deepHole hα x,
   fun _ hα x ↦ coldSpot_E8_iff_deepHole hα x,
   fun _ hα x ↦ coldSpot_E7_dual_iff_deepHole hα x,
   fun _ hα x ↦ coldSpot_bw16_iff_deepHole hα x,
   fun _ hn heven _ hα x ↦ coldSpot_dPlus_iff_deepHole hn heven hα x⟩

/-- All entries of the radius column are upper bounds with actual attainment. -/
theorem lattice_covering_radius_table :
    ((∀ x : Fin 6 → ℝ, squaredDepth e6Set x ≤ 4/3) ∧
      ∃ x : Fin 6 → ℝ, squaredDepth e6Set x=4/3) ∧
    ((∀ x : Fin 8 → ℝ, squaredDepth (dPlusSet 8) x ≤ 1) ∧
      ∃ x : Fin 8 → ℝ, squaredDepth (dPlusSet 8) x=1) ∧
    ((∀ x : zeroSumSpace, e7SquaredDepth x ≤ 7/8) ∧
      ∃ x : zeroSumSpace, e7SquaredDepth x=7/8) ∧
    ((∀ x : Fin 16 → ℝ, squaredDepth bw16Set x ≤ 3) ∧
      ∃ x : Fin 16 → ℝ, squaredDepth bw16Set x=3) ∧
    (∀ n : ℕ, 8 ≤ n → Even n →
      (∀ x : Fin n → ℝ, squaredDepth (dPlusSet n) x ≤ (n:ℝ)/8) ∧
        ∃ x : Fin n → ℝ, squaredDepth (dPlusSet n) x=(n:ℝ)/8) := by
  refine ⟨⟨e6_covering_radius_squared,e6PhysicalPoint e6HoleWitness,
    e6_covering_radius_attained⟩,?_,e7_covering_radius,bw16_squared_covering_radius,
    fun _ hn heven ↦ dPlus_squared_covering_radius hn heven⟩
  simpa using dPlus_squared_covering_radius (n:=8) (by decide) (by decide)

theorem e6_deep_translation_class_count_uniform :
    Nat.card (DeepTranslationClasses e6AddSubgroup)=2 := by
  simpa only [DeepTranslationClasses,e6AddSubgroup_coe,E6DeepTranslationClasses]
    using e6_deep_translation_class_count

/-- The class column counts actual quotient classes of all real deep holes. -/
theorem lattice_translation_class_table :
    Nat.card (DeepTranslationClasses e6AddSubgroup)=2 ∧
    Nat.card (DeepTranslationClasses (dPlusAddSubgroup 8 (by decide)))=135 ∧
    Nat.card E7DeepTranslationClasses=36 ∧
    Nat.card (DeepTranslationClasses bw16AddSubgroup)=120 ∧
    (∀ n : ℕ, 8 < n → ∀ heven : Even n,
      Nat.card (DeepTranslationClasses (dPlusAddSubgroup n heven))=n.choose (n/2)) :=
  ⟨e6_deep_translation_class_count_uniform,e8_deep_translation_class_count,
   e7_dual_deep_translation_class_count,bw16_deep_translation_class_count,
   fun _ hn heven ↦ dPlus_deep_translation_class_count hn heven⟩

/-- Corollary 1.2 for the literal convergent real sums of integral potentials.
The positive measure is arbitrary. No sigma-finiteness hypothesis is imposed. -/
theorem lattice_corollary_1_2 (ν : Measure PositiveParameter) (hν : ν≠0) :
    ((∀ x : Fin 6 → ℝ, setMixtureEnergyENNReal e6Set ν x≠∞) →
      ∀ x : Fin 6 → ℝ, IsMixtureColdSpot e6Set ν x ↔ IsDeepHole e6Set x) ∧
    ((∀ x : Fin 8 → ℝ, setMixtureEnergyENNReal (dPlusSet 8) ν x≠∞) →
      ∀ x : Fin 8 → ℝ, IsMixtureColdSpot (dPlusSet 8) ν x ↔ IsDeepHole (dPlusSet 8) x) ∧
    ((∀ x : zeroSumSpace, e7MixtureEnergyENNReal ν x≠∞) →
      ∀ x : zeroSumSpace, (∀ y, e7MixtureEnergy ν x ≤ e7MixtureEnergy ν y) ↔ IsE7DeepHole x) ∧
    ((∀ x : Fin 16 → ℝ, setMixtureEnergyENNReal bw16Set ν x≠∞) →
      ∀ x : Fin 16 → ℝ, IsMixtureColdSpot bw16Set ν x ↔ IsDeepHole bw16Set x) ∧
    (∀ n : ℕ, 8 ≤ n → Even n →
      (∀ x : Fin n → ℝ, setMixtureEnergyENNReal (dPlusSet n) ν x≠∞) →
      ∀ x : Fin n → ℝ, IsMixtureColdSpot (dPlusSet n) ν x ↔ IsDeepHole (dPlusSet n) x) :=
  ⟨fun hconv x ↦ mixture_coldSpot_E6_iff_deepHole ν hν hconv x,
   fun hconv x ↦ mixture_coldSpot_E8_iff_deepHole ν hν hconv x,
   fun hconv x ↦ mixture_coldSpot_E7_dual_iff_deepHole ν hν hconv x,
   fun hconv x ↦ mixture_coldSpot_bw16_iff_deepHole ν hν hconv x,
   fun _ hn heven hconv x ↦ mixture_coldSpot_dPlus_iff_deepHole hn heven ν hν hconv x⟩

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.lattice_theorem_1_1
#print axioms PaperVerification.ColdSpots.lattice_covering_radius_table
#print axioms PaperVerification.ColdSpots.lattice_translation_class_table
#print axioms PaperVerification.ColdSpots.lattice_corollary_1_2
