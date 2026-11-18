module

public import ToricPower.FanRayIndex
public import TauCeti.Geometry.Toric.Algebraic.Regular

/-!
# Attaching finitely many compatible cones to an actual fan

The constructor retains the original cones and closes the attached
cones under faces. Its inputs are the ordinary toric-cone and face
intersection properties. The later packing construction proves these
properties for its explicit integral ray lifts.
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

def attachFiniteCones : Fan i :=
  Fan.ofCones fan.lattice (fan.cones ∪ Set.range cones)
    (fan.finite_cones.union (Set.finite_range cones))
    (by
      rintro σ (old | ⟨j,rfl⟩)
      · exact fan.isToricCone old
      · exact toric j)
    (by
      rintro σ τ (oldσ | ⟨j,rfl⟩) (oldτ | ⟨k,rfl⟩)
      · exact fan.inf_isFaceOf_left oldσ oldτ
      · rw [inf_comm]
        exact (oldIntersections k ⟨σ,oldσ⟩).2
      · exact (oldIntersections j ⟨τ,oldτ⟩).1
      · exact intersections j k)

theorem mem_attachFiniteCones_iff (σ : PointedCone ℝ V) :
    σ ∈ (attachFiniteCones fan cones toric intersections oldIntersections).cones ↔
      σ ∈ fan.cones ∨ ∃ j, σ.IsFaceOf (cones j) := by
  unfold attachFiniteCones
  rw [Fan.mem_ofCones_cones]
  constructor
  · rintro ⟨τ,(old | ⟨j,rfl⟩),face⟩
    · exact Or.inl (fan.mem_of_isFaceOf old face)
    · exact Or.inr ⟨j,face⟩
  · rintro (old | ⟨j,face⟩)
    · exact ⟨σ,Or.inl old,PointedCone.IsFaceOf.refl _⟩
    · exact ⟨cones j,Or.inr ⟨j,rfl⟩,face⟩

theorem attachFiniteCones_contains_original :
    fan.cones ⊆ (attachFiniteCones fan cones toric intersections oldIntersections).cones :=
  fun σ member => (mem_attachFiniteCones_iff fan cones toric intersections oldIntersections σ).mpr
    (Or.inl member)

theorem attachFiniteCones_contains_new (j : J) :
    cones j ∈ (attachFiniteCones fan cones toric intersections oldIntersections).cones :=
  (mem_attachFiniteCones_iff fan cones toric intersections oldIntersections (cones j)).mpr
    (Or.inr ⟨j,PointedCone.IsFaceOf.refl _⟩)

theorem attachFiniteCones_regular (regular : fan.IsRegular)
    (newRegular : ∀ j, IsRegularCone i (cones j)) :
    (attachFiniteCones fan cones toric intersections oldIntersections).IsRegular := by
  rw [Fan.isRegular_iff]
  intro σ member
  rcases (mem_attachFiniteCones_iff fan cones toric intersections oldIntersections σ).mp member
    with old | ⟨j,face⟩
  · exact Fan.isRegular_iff.mp regular σ old
  · exact (newRegular j).of_isFaceOf face

end ToricPower.FanSubdivision
end

