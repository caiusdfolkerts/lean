module

public import ToricPower.FanStarCoverage
public import ToricPower.SubfanRayRetraction

/-!
# Finite iteration of genuine ray-star extensions

Each step retains every cone already constructed. Completeness of the
previously completed stars is monotone under this inclusion, so the
finite induction does not undo earlier steps. The local construction
of a star extension remains an explicit premise here; it is supplied
by the quotient-star construction in the subsequent assembly.
-/

@[expose] public noncomputable section

open TauCeti.Toric
namespace ToricPower.FanSubdivision

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (original : Fan i)

/-- A regular extension with every original ray star complete. -/
structure RegularRayPacking where
  fan : Fan i
  contains : original.cones ⊆ fan.cones
  regular : fan.IsRegular
  covers : ∀ ρ : original.Ray, RayStarCovers fan (i (fanRayPrimitiveGenerator original ρ))

theorem exists_regularRayPacking_of_steps (regular : original.IsRegular)
    (step : ∀ (current : Fan i), current.IsRegular →
      original.cones ⊆ current.cones → ∀ ρ : current.Ray,
        ∃ extension : Fan i, current.cones ⊆ extension.cones ∧ extension.IsRegular ∧
          RayStarCovers extension (i (fanRayPrimitiveGenerator current ρ))) :
    Nonempty (RegularRayPacking original) := by
  classical
  letI : Fintype original.Ray := Fintype.ofFinite _
  have finiteSteps : ∀ s : Finset original.Ray,
      ∃ current : Fan i, original.cones ⊆ current.cones ∧ current.IsRegular ∧
        ∀ ρ ∈ s, RayStarCovers current (i (fanRayPrimitiveGenerator original ρ)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        exact ⟨original,Set.Subset.refl _,regular,by simp⟩
    | @insert ρ s absent inductionHypothesis =>
        obtain ⟨current,contains,currentRegular,previous⟩ := inductionHypothesis
        let selected := subfanRayEmbedding original current contains ρ
        obtain ⟨extension,nextContains,nextRegular,covered⟩ :=
          step current currentRegular contains selected
        refine ⟨extension,contains.trans nextContains,nextRegular,?_⟩
        intro τ member
        rcases Finset.mem_insert.mp member with rfl | member
        · simpa only [selected,subfanRayEmbedding_primitive] using covered
        · exact (previous τ member).mono nextContains
  obtain ⟨extension,contains,extensionRegular,covered⟩ := finiteSteps Finset.univ
  exact ⟨⟨extension,contains,extensionRegular,fun ρ => covered ρ (Finset.mem_univ _)⟩⟩

end ToricPower.FanSubdivision
end

