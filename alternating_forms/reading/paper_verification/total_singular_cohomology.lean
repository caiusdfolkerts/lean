import PaperVerification.DirectSumConcentration
import PaperVerification.ExactSequenceRank
import PaperVerification.EmptySingularCohomology
import OAI.AlgebraicTopology.Cohomology.Singular.RelativeSequence

/-!
# Total singular cohomology and the actual pair sequence

The total group is the direct sum of the genuine singular groups over all
natural degrees. Degreewise exactness gives exactness of the direct-sum maps.
Thus a finite paving can be treated without a cohomological degree cutoff.
-/

namespace PaperVerification.TotalSingularCohomology

noncomputable section

open CategoryTheory CategoryTheory.Limits
open OAI.AlgebraicTopology.Cohomology.Singular
open scoped DirectSum

variable {K : Type} [Field K]

abbrev total (X : TopCat.{0}) :=
  ⨁ n : ℕ, Basic.singularCohomology (ModuleCat.of K K) X n

abbrev relativeTotal (X : TopCat.{0}) (A : Set X) :=
  ⨁ n : ℕ, RelativeSequence.relativeSingularCohomology (ModuleCat.of K K) X A n

def inclusion (X : TopCat.{0}) (A : Set X) :
    relativeTotal (K := K) X A →ₗ[K] total (K := K) X :=
  DirectSum.lmap fun n =>
    (RelativeSequence.relativeCohomologyInclusion (ModuleCat.of K K) X A n).hom

def restriction (X : TopCat.{0}) (A : Set X) :
    total (K := K) X →ₗ[K] total (K := K) (TopCat.of A) :=
  DirectSum.lmap fun n =>
    (RelativeSequence.subspaceCohomologyRestriction (ModuleCat.of K K) X A n).hom

/-- The direct sum of the original pair-sequence maps is exact. -/
theorem range_inclusion_eq_ker_restriction (X : TopCat.{0}) (A : Set X) :
    LinearMap.range (inclusion (K := K) X A) = LinearMap.ker (restriction (K := K) X A) :=
  DirectSumConcentration.range_eq_ker _ _ fun n =>
    RelativeSequence.relativeCohomology_range_inclusion (ModuleCat.of K K) X A n

theorem finite_and_finrank_le (X : TopCat.{0}) (A : Set X)
    [Module.Finite K (relativeTotal (K := K) X A)]
    [Module.Finite K (total (K := K) (TopCat.of A))] :
    Module.Finite K (total (K := K) X) ∧
      Module.finrank K (total (K := K) X) ≤
        Module.finrank K (relativeTotal (K := K) X A) +
        Module.finrank K (total (K := K) (TopCat.of A)) :=
  ⟨ExactSequenceRank.finite_middle (inclusion X A) (restriction X A)
      (range_inclusion_eq_ker_restriction X A),
    ExactSequenceRank.finrank_middle_le (inclusion X A) (restriction X A)
      (range_inclusion_eq_ker_restriction X A)⟩

/-- The initial total group of an empty stage is literally zero. -/
theorem subsingleton_of_isEmpty (X : TopCat.{0}) [IsEmpty X] :
    Subsingleton (total (K := K) X) := by
  letI (n : ℕ) : Subsingleton (Basic.singularCohomology (ModuleCat.of K K) X n) :=
    ModuleCat.subsingleton_of_isZero
      (EmptySingularCohomology.cohomology_isZero (ModuleCat.of K K) X n)
  infer_instance

end
end PaperVerification.TotalSingularCohomology
