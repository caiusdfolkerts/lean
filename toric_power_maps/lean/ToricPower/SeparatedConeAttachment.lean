module

public import ToricPower.FanPackingPerturbation
public import ToricPower.FanRayCoordinates
public import TauCeti.Geometry.Convex.Cone.Face.Exposed

/-!
# Positive separating characters preserve the old fan faces

The finite perturbation bound is useful only if it gives genuine fan
attachments. Here strict positivity on the new generators proves that
their cone meets an old cone in precisely the original common face,
and that the intersection remains a face on both sides.
-/

@[expose] public noncomputable section
open TauCeti.Toric
namespace ToricPower.FanPacking

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem adjoining_positive_inf_isFaceOf
    (old opposite : PointedCone ℝ V) (form : V →ₗ[ℝ] ℝ)
    (nonnegative : ∀ x ∈ old, 0 ≤ form x)
    (nonpositive : ∀ x ∈ opposite, form x ≤ 0)
    (oldKernel : old ⊓ PointedCone.ofSubmodule form.ker = old ⊓ opposite)
    (generators : Set V) (positive : ∀ v ∈ generators, 0 < form v) :
    ((old ⊔ PointedCone.hull ℝ generators) ⊓ opposite).IsFaceOf
      (old ⊔ PointedCone.hull ℝ generators) := by
  have totalNonnegative : ∀ x ∈ old ⊔ PointedCone.hull ℝ generators, 0 ≤ form x := by
    intro x member
    obtain ⟨y,hy,z,hz,rfl⟩ := Submodule.mem_sup.mp member
    rw [map_add]
    exact add_nonneg (nonnegative y hy) (hull_nonnegative_and_zero form generators positive hz).1
  have kernelNonpositive : ∀ x ∈ PointedCone.ofSubmodule form.ker, form x ≤ 0 := by
    intro x member
    exact le_of_eq (show form x = 0 from member)
  have cut : (old ⊔ PointedCone.hull ℝ generators) ⊓
      PointedCone.ofSubmodule form.ker = old ⊓ opposite := by
    rw [adjoining_positive_generators_inf old _ form nonnegative kernelNonpositive generators positive,
      oldKernel]
  rw [adjoining_positive_generators_inf old opposite form nonnegative nonpositive generators positive,
    ← cut]
  exact PointedCone.isFaceOf_inf_ker totalNonnegative

variable {N : Type*} [AddCommGroup N] {i : N →+ V}
  (fan : Fan i) (ray : fan.Ray)

/-- A common-face separator for a star cone and an outside cone is
strictly positive on the selected primitive ray. -/
theorem exists_star_separator (σ τ : fan.cones) (contains : ray.toCone ≤ σ)
    (outside : ¬ ray.toCone ≤ τ) :
    ∃ m : N →+ ℤ, m ∈ dualSemigroup fan.lattice σ.val ∧
      -m ∈ dualSemigroup fan.lattice τ.val ∧ 0 < m (fanRayPrimitiveGenerator fan ray) ∧
      σ.val ⊓ PointedCone.ofSubmodule (fan.lattice.realCharacter m).ker = σ.val ⊓ τ.val := by
  obtain ⟨m,nonnegative,nonpositive,firstCut,_⟩ :=
    exists_mem_dualSemigroup_neg_mem_dualSemigroup_inf_ker_eq fan.lattice
      (fan.isToricCone σ.property).rational (fan.isToricCone τ.property).rational
      (fan.inf_isFaceOf_left σ.property τ.property)
      (fan.inf_isFaceOf_right σ.property τ.property)
  have member : fanRayRealVector fan ray ∈ σ.val := contains (fanRayRealVector_mem fan ray)
  have valueNonnegative : 0 ≤ m (fanRayPrimitiveGenerator fan ray) := by
    have nonnegativeReal := (mem_dualSemigroup fan.lattice m).mp nonnegative member
    change 0 ≤ fan.lattice.realCharacter m (i (fanRayPrimitiveGenerator fan ray)) at nonnegativeReal
    rw [fan.lattice.realCharacter_apply] at nonnegativeReal
    exact_mod_cast nonnegativeReal
  have nonzero : m (fanRayPrimitiveGenerator fan ray) ≠ 0 := by
    intro zero
    have kernelMember : fanRayRealVector fan ray ∈
        PointedCone.ofSubmodule (fan.lattice.realCharacter m).ker := by
      change fan.lattice.realCharacter m (i (fanRayPrimitiveGenerator fan ray)) = 0
      rw [fan.lattice.realCharacter_apply,zero,Int.cast_zero]
    have inOther : fanRayRealVector fan ray ∈ τ.val := by
      have common : fanRayRealVector fan ray ∈ σ.val ⊓ τ.val :=
        firstCut ▸ ⟨member,kernelMember⟩
      exact common.2
    apply outside
    change ray.toCone.val ≤ τ.val
    rw [fanRay_eq_hull_realVector]
    exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr inOther)
  exact ⟨m,nonnegative,nonpositive,lt_of_le_of_ne valueNonnegative nonzero.symm,firstCut⟩

end ToricPower.FanPacking
end
