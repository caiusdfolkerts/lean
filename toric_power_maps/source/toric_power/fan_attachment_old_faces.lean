module

public import ToricPower.FiniteFanAttachment
public import ToricPower.SubfanRayRetraction

/-!
# Exact old faces imply the divisorial ray condition after attachment

If every attached cone meets each original cone in the same way as one
specified original face, that face contains every old ray of the new
cone. The conclusion therefore applies to every face introduced by the
actual fan constructor, not merely to its generating cones.
-/

@[expose] public noncomputable section
open TauCeti.Toric
namespace ToricPower.FanSubdivision

variable {N V J : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (fan : Fan i) [Finite J] (cones : J → PointedCone ℝ V)
  (toric : ∀ j, IsToricCone i (cones j))
  (intersections : ∀ j k, (cones j ⊓ cones k).IsFaceOf (cones j))
  (oldIntersections : ∀ j (σ : fan.cones),
    (cones j ⊓ σ.val).IsFaceOf (cones j) ∧ (cones j ⊓ σ.val).IsFaceOf σ.val)
  (oldFace : J → fan.cones)
  (sameIntersections : ∀ j (σ : fan.cones),
    cones j ⊓ σ.val = (oldFace j).val ⊓ σ.val)

include sameIntersections in
theorem attachFiniteCones_fullOnRays :
    IsFullOnRays fan (attachFiniteCones fan cones toric intersections oldIntersections) := by
  let extension := attachFiniteCones fan cones toric intersections oldIntersections
  have included : fan.cones ⊆ extension.cones :=
    attachFiniteCones_contains_original fan cones toric intersections oldIntersections
  intro F member allOld
  rcases (mem_attachFiniteCones_iff fan cones toric intersections oldIntersections F).mp member
    with old | ⟨j,face⟩
  · exact old
  · have below : F ≤ (oldFace j).val := by
      apply fanCone_le_of_rays extension ⟨F,member⟩
        (subfanConeEmbedding fan extension included (oldFace j))
      intro ρ contained
      change ρ.toCone.val ≤ F at contained
      change ρ.toCone.val ≤ (oldFace j).val
      have oldRay : ρ.toCone.val ∈ fan.cones := allOld ρ contained
      have comparison : ρ.toCone.val ≤ cones j ⊓ ρ.toCone.val :=
        le_inf (contained.trans face.le) le_rfl
      rw [sameIntersections j ⟨ρ.toCone.val,oldRay⟩] at comparison
      exact comparison.trans inf_le_left
    exact fan.mem_of_isFaceOf (oldFace j).property
      (extension.isFaceOf_of_le (included (oldFace j).property) member below)

end ToricPower.FanSubdivision
end

