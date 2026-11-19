module

public import ToricPower.PackedFanRationalCompletion
public import ToricPower.CompletedStarCoverage
public import ToricPower.CompletedStarOldFaces

/-!
# Rank induction for actual smooth divisorial completion

This file assembles the quotient-star packing and rational exterior
completion. The only input is the independently constructed relative
regular refinement of a complete fan. Once that input is discharged by
the lattice multiplicity descent, this induction yields an unconditional
completion theorem in every rank.
-/

@[expose] public noncomputable section
open TauCeti.Toric

namespace ToricPower.FanSubdivision

universe u v

variable (regularize :
  ∀ {N : Type u} {V : Type v} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
    {i : N →+ V} (original coarse : Fan i), original.IsRegular →
    original.cones ⊆ coarse.cones → coarse.IsComplete →
    Nonempty (RelativeRegularFanRefinement original coarse))

include regularize in
/-- Strong induction in the actual lattice rank. Every auxiliary star
uses the literal quotient lattice and real quotient vector space. -/
theorem exists_smoothDivisorialCompletion_of_relative_regular_refinement
    {N : Type u} {V : Type v} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
    {i : N →+ V} (fan : Fan i) (nonempty : fan.cones.Nonempty)
    (regular : fan.IsRegular) : Nonempty (SmoothDivisorialCompletion fan) := by
  have byRank : ∀ n : ℕ,
      ∀ {N : Type u} {V : Type v} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
        {i : N →+ V} (fan : Fan i), Module.finrank ℤ N = n →
        fan.cones.Nonempty → fan.IsRegular → Nonempty (SmoothDivisorialCompletion fan) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n inductionHypothesis =>
      intro N V _ _ _ i fan rank nonempty regular
      obtain ⟨packing⟩ := exists_regularDivisorialRayPacking_of_steps fan regular (by
        intro current currentRegular contains ray
        have smaller : Module.finrank ℤ
            (RayQuotientLattice (fanRayPrimitiveGenerator current ray)) < n := by
          rw [← rank]
          exact canonicalRayStar_rank_lt current ray
        have starNonempty : (canonicalRayStar current ray).cones.Nonempty := by
          obtain ⟨cone⟩ := (inferInstance : Nonempty (canonicalRayStar current ray).cones)
          exact ⟨cone.val, cone.property⟩
        obtain ⟨completion⟩ := inductionHypothesis _ smaller
          (canonicalRayStar current ray) rfl starNonempty
          (canonicalRayStar_regular current ray currentRegular)
        let M := completedStarPackingThreshold current currentRegular ray completion
        refine ⟨completedStarPackedFan current currentRegular ray completion M le_rfl,
          completedStarPackedFan_contains current currentRegular ray completion M le_rfl,
          completedStarPackedFan_regular current currentRegular ray completion M le_rfl,
          completedStarPackedFan_fullOnRays current currentRegular ray completion M le_rfl,
          completedStarPackedFan_starCovers current currentRegular ray completion M le_rfl⟩)
      let completion := packedRayCompatibleCompletion fan packing nonempty
      obtain ⟨refinement⟩ := regularize fan completion.fan regular
        completion.contains completion.complete
      exact ⟨completion.toSmooth refinement⟩
  exact byRank _ fan rfl nonempty regular

end ToricPower.FanSubdivision
end
