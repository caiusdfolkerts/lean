import PaperVerification.ExactSequenceRank
import OAI.AlgebraicTopology.Cohomology.Singular.RelativeSequence

/-!
# Rank and vanishing in the genuine singular-cohomology pair sequence

These statements use the original relative, absolute, and subspace groups,
with exactness proved from their actual singular cochain complexes.
-/

namespace PaperVerification.SingularCohomologyRank

noncomputable section

open CategoryTheory CategoryTheory.Limits
open OAI.AlgebraicTopology.Cohomology.Singular

section Pair

variable {K : Type} [Field K] (X : TopCat.{0}) (A : Set X) (n : ℕ)

/-- Finiteness propagates through the actual relative/absolute/subspace
cohomology sequence, without assuming that restriction is surjective. -/
theorem finite_of_pair
    [Module.Finite K (RelativeSequence.relativeSingularCohomology
      (ModuleCat.of K K) X A n)]
    [Module.Finite K (Basic.singularCohomology (ModuleCat.of K K) (TopCat.of A) n)] :
    Module.Finite K (Basic.singularCohomology (ModuleCat.of K K) X n) :=
  ExactSequenceRank.finite_middle
    (RelativeSequence.relativeCohomologyInclusion (ModuleCat.of K K) X A n).hom
    (RelativeSequence.subspaceCohomologyRestriction (ModuleCat.of K K) X A n).hom
    (RelativeSequence.relativeCohomology_range_inclusion (ModuleCat.of K K) X A n)

/-- The rank estimate uses the original maps in the long exact sequence. -/
theorem finrank_le_relative_add_subspace
    [Module.Finite K (RelativeSequence.relativeSingularCohomology
      (ModuleCat.of K K) X A n)]
    [Module.Finite K (Basic.singularCohomology (ModuleCat.of K K) (TopCat.of A) n)] :
    Module.finrank K (Basic.singularCohomology (ModuleCat.of K K) X n) ≤
      Module.finrank K (RelativeSequence.relativeSingularCohomology
        (ModuleCat.of K K) X A n) +
      Module.finrank K (Basic.singularCohomology (ModuleCat.of K K) (TopCat.of A) n) :=
  ExactSequenceRank.finrank_middle_le
    (RelativeSequence.relativeCohomologyInclusion (ModuleCat.of K K) X A n).hom
    (RelativeSequence.subspaceCohomologyRestriction (ModuleCat.of K K) X A n).hom
    (RelativeSequence.relativeCohomology_range_inclusion (ModuleCat.of K K) X A n)

/-- Vanishing propagates through the same sequence. -/
theorem isZero_of_pair
    (hrel : IsZero (RelativeSequence.relativeSingularCohomology
      (ModuleCat.of K K) X A n))
    (hopen : IsZero (Basic.singularCohomology (ModuleCat.of K K) (TopCat.of A) n)) :
    IsZero (Basic.singularCohomology (ModuleCat.of K K) X n) := by
  letI := ModuleCat.subsingleton_of_isZero hrel
  letI := ModuleCat.subsingleton_of_isZero hopen
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact ExactSequenceRank.subsingleton_middle
    (RelativeSequence.relativeCohomologyInclusion (ModuleCat.of K K) X A n).hom
    (RelativeSequence.subspaceCohomologyRestriction (ModuleCat.of K K) X A n).hom
    (RelativeSequence.relativeCohomology_range_inclusion (ModuleCat.of K K) X A n)

end Pair

end
end PaperVerification.SingularCohomologyRank
