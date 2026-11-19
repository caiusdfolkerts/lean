module

public import ToricPower.ConeMultiplicityRegular
public import ToricPower.SmoothFanCompletionInduction

/-!
# Smooth divisorial completion of an arbitrary regular fan

Every nonempty finite regular rational fan admits a complete regular
extension in the same integral lattice. The extension is full on the
original rays, so its complement is supported on the added ray divisors.

The proof combines actual quotient-star completion by rank induction,
integral piecewise-linear exterior completion, relative simplicial
subdivision, and strict integer-determinant descent. No completeness,
projectivity, or fixed-rank restriction is imposed on the original fan.
-/

@[expose] public noncomputable section
open TauCeti.Toric

namespace ToricPower.FanSubdivision

universe u v

variable {N : Type u} {V : Type v} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

/-- Actual relative regularization of a complete fan, retaining every
cone of the prescribed regular subfan literally. -/
theorem exists_relative_regular_refinement (original coarse : Fan i)
    (regular : original.IsRegular) (contains : original.cones ⊆ coarse.cones)
    (complete : coarse.IsComplete) :
    Nonempty (RelativeRegularFanRefinement original coarse) := by
  apply exists_relative_regular_of_multiplicity_steps (coneMultiplicity coarse.lattice)
    (fun fan complete simplicial C member full large =>
      exists_stellarMultiplicityStep fan complete simplicial C member full large)
    (fun C toric simplicial full small =>
      isRegularCone_of_coneMultiplicity_le_one coarse.lattice toric simplicial full small)
    original coarse regular contains complete

/-- Every nonempty regular fan has an actual smooth divisorial completion.
This theorem has no external completion or refinement hypothesis. -/
theorem exists_smoothDivisorialCompletion (fan : Fan i)
    (nonempty : fan.cones.Nonempty) (regular : fan.IsRegular) :
    Nonempty (SmoothDivisorialCompletion fan) := by
  exact exists_smoothDivisorialCompletion_of_relative_regular_refinement
    (@exists_relative_regular_refinement) fan nonempty regular

/-- A chosen genuine completion, useful for the geometric boundary and
Cartier-extension arguments. Choice changes no mathematical hypothesis. -/
def smoothDivisorialCompletion (fan : Fan i)
    (nonempty : fan.cones.Nonempty) (regular : fan.IsRegular) :
    SmoothDivisorialCompletion fan :=
  Classical.choice (exists_smoothDivisorialCompletion fan nonempty regular)

/-- An unbundled formulation of the full completion result. -/
theorem exists_complete_regular_extension_fullOnRays (fan : Fan i)
    (nonempty : fan.cones.Nonempty) (regular : fan.IsRegular) :
    ∃ extension : Fan i, fan.cones ⊆ extension.cones ∧ extension.IsRegular ∧
      extension.IsComplete ∧ IsFullOnRays fan extension := by
  let completion := smoothDivisorialCompletion fan nonempty regular
  exact ⟨completion.fan, completion.contains, completion.regular, completion.complete,
    (isFullOnRays_iff_local fan completion.fan).mpr completion.oldRayClosed⟩

end ToricPower.FanSubdivision
end
