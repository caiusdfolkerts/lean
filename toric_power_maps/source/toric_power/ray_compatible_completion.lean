module

public import ToricPower.RelativeFanRefinement

/-!
# The old-ray invariant retained by arbitrary relative refinements

For every cone of the rational completion, all original rays in that
cone lie in one original cone. Any further refinement retaining the
original fan therefore has no additional cone consisting entirely of
old rays. This proves the divisorial condition after regularization,
without a separate cleanup subdivision.
-/

@[expose] public noncomputable section
open TauCeti.Toric

namespace ToricPower

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (original : Fan i)

structure RayCompatibleCompletion where
  fan : Fan i
  contains : original.cones ⊆ fan.cones
  complete : fan.IsComplete
  oldRays : ∀ σ : fan.cones, ∃ τ : original.cones,
    ∀ ρ : original.Ray, ρ.toCone.val ≤ σ.val → ρ.toCone.val ≤ τ.val

namespace RayCompatibleCompletion

variable {original} (completion : RayCompatibleCompletion original)
  (refinement : RelativeRegularFanRefinement original completion.fan)

theorem refinement_fullOnRays : IsFullOnRays original refinement.fan := by
  intro σ member allOld
  obtain ⟨τ,coarseMember,contained⟩ := refinement.refines σ member
  obtain ⟨oldFace,oldRays⟩ := completion.oldRays ⟨τ,coarseMember⟩
  have inOldFace : σ ≤ oldFace.val := by
    apply fanCone_le_of_rays refinement.fan ⟨σ,member⟩
      (subfanConeEmbedding original refinement.fan refinement.retains oldFace)
    intro ρ below
    let oldRay : original.Ray := ⟨⟨ρ.toCone.val,allOld ρ below⟩,ρ.property⟩
    change ρ.toCone.val ≤ σ at below
    change ρ.toCone.val ≤ oldFace.val
    exact oldRays oldRay (below.trans contained)
  exact original.mem_of_isFaceOf oldFace.property
    (refinement.fan.isFaceOf_of_le (refinement.retains oldFace.property) member inOldFace)

/-- An actual relative regular refinement of this actual rational completion
has exactly the smooth divisorial completion properties required downstream. -/
def toSmooth : SmoothDivisorialCompletion original :=
  refinement.toDivisorialCompletion completion.complete
    (completion.refinement_fullOnRays refinement)

end RayCompatibleCompletion
end ToricPower
end
