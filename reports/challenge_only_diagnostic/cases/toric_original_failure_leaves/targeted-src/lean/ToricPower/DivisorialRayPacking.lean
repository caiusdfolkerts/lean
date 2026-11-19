module

public import ToricPower.FiniteRayPacking
public import ToricPower.FullOnRaysTrans

/-!
# Finite star completion preserving the full subfan on original rays

This version of the finite induction retains the precise old-ray
condition needed for the later divisorial boundary. Each step supplies
an actual extending regular fan and its full-on-rays proof.
-/

@[expose] public noncomputable section
open TauCeti.Toric
namespace ToricPower.FanSubdivision

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (original : Fan i)

structure RegularDivisorialRayPacking extends RegularRayPacking original where
  full : IsFullOnRays original fan

theorem exists_regularDivisorialRayPacking_of_steps (regular : original.IsRegular)
    (step : ∀ (current : Fan i), current.IsRegular →
      original.cones ⊆ current.cones → ∀ ρ : current.Ray,
        ∃ extension : Fan i, current.cones ⊆ extension.cones ∧ extension.IsRegular ∧
          IsFullOnRays current extension ∧
          RayStarCovers extension (i (fanRayPrimitiveGenerator current ρ))) :
    Nonempty (RegularDivisorialRayPacking original) := by
  classical
  letI : Fintype original.Ray := Fintype.ofFinite _
  have finiteSteps : ∀ s : Finset original.Ray,
      ∃ current : Fan i, original.cones ⊆ current.cones ∧ current.IsRegular ∧
        IsFullOnRays original current ∧
        ∀ ρ ∈ s, RayStarCovers current (i (fanRayPrimitiveGenerator original ρ)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        exact ⟨original,Set.Subset.refl _,regular,isFullOnRays_self original,by simp⟩
    | @insert ρ s absent inductionHypothesis =>
        obtain ⟨current,contains,currentRegular,currentFull,previous⟩ := inductionHypothesis
        let selected := subfanRayEmbedding original current contains ρ
        obtain ⟨extension,nextContains,nextRegular,nextFull,covered⟩ :=
          step current currentRegular contains selected
        refine ⟨extension,contains.trans nextContains,nextRegular,
          IsFullOnRays.trans contains nextContains currentFull nextFull,?_⟩
        intro τ member
        rcases Finset.mem_insert.mp member with rfl | member
        · simpa only [selected,subfanRayEmbedding_primitive] using covered
        · exact (previous τ member).mono nextContains
  obtain ⟨extension,contains,extensionRegular,full,covered⟩ := finiteSteps Finset.univ
  exact ⟨⟨⟨extension,contains,extensionRegular,
    fun ρ => covered ρ (Finset.mem_univ _)⟩,full⟩⟩

end ToricPower.FanSubdivision
end

