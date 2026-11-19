module

public import ToricPower.FanRayCoordinates
public import ToricPower.FanRayQuotientCones

/-!
# The actual fan obtained by quotienting a ray star

The cones are the faces of the images of the original cones containing
the selected ray. Lattice rationality, salience, and every intersection
axiom are proved from the original fan and the rank-one kernel of the
quotient map. No fan structure on the quotient is supplied as a premise.
-/

@[expose] public noncomputable section

open TauCeti.Toric

namespace ToricPower.FanSubdivision

variable {N P V W : Type*} [AddCommGroup N] [AddCommGroup P]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  {i : N →+ V} {j : P →+ W}
  (fan : Fan i) (ray : fan.Ray)
  (latticeMap : N →+ P) (projection : V →ₗ[ℝ] W)
  (compatible : ∀ n, projection (i n) = j (latticeMap n))
  (kernel : LinearMap.ker projection = Submodule.span ℝ {fanRayRealVector fan ray})

theorem fanRayRealVector_ne_zero : fanRayRealVector fan ray ≠ 0 := by
  simpa only [fanRayRealVector, fanRayPrimitiveGenerator, map_zero] using fan.lattice.injective.ne
    (primitiveGenerator_ne_zero fan.lattice (fan.isToricCone ray.toCone.property)
      (ray.toToricRay fan ray.toCone le_rfl))

def rayStarSeedCones : Set (PointedCone ℝ W) :=
  (PointedCone.map projection) ''
    {σ : PointedCone ℝ V | σ ∈ fan.cones ∧ ray.toCone.val ≤ σ}

theorem rayStarSeedCones_finite : (rayStarSeedCones fan ray projection).Finite :=
  (fan.finite_cones.subset (fun _ member => member.1)).image _

include compatible kernel in
theorem rayStarImage_isToricCone (σ : PointedCone ℝ V)
    (member : σ ∈ fan.cones) (contains : ray.toCone.val ≤ σ) :
    IsToricCone j (PointedCone.map projection σ) := by
  refine ⟨(fan.isToricCone member).rational.map compatible, ?_⟩
  apply map_salient_of_kernel_face projection σ
  apply kernel_face_of_ray_face projection (fanRayRealVector fan ray) kernel σ
    (fan.isToricCone member).salient
    (contains (fanRayRealVector_mem fan ray)) (fanRayRealVector_ne_zero fan ray)
  rw [← fanRay_eq_hull_realVector]
  exact fan.isFaceOf_of_le member ray.toCone.property contains

include compatible kernel in
theorem rayStarSeedCones_isToricCone {σ : PointedCone ℝ W}
    (member : σ ∈ rayStarSeedCones fan ray projection) : IsToricCone j σ := by
  obtain ⟨τ,⟨hτ,contains⟩,rfl⟩ := member
  exact rayStarImage_isToricCone fan ray latticeMap projection compatible kernel τ hτ contains

include kernel in
theorem rayStarSeedCones_inf_isFaceOf {σ τ : PointedCone ℝ W}
    (first : σ ∈ rayStarSeedCones fan ray projection)
    (second : τ ∈ rayStarSeedCones fan ray projection) :
    (σ ⊓ τ).IsFaceOf σ := by
  obtain ⟨σ,⟨hσ,containsσ⟩,rfl⟩ := first
  obtain ⟨τ,⟨hτ,containsτ⟩,rfl⟩ := second
  have aσ := containsσ (fanRayRealVector_mem fan ray)
  have aτ := containsτ (fanRayRealVector_mem fan ray)
  rw [← map_inf_of_ray_mem projection (fanRayRealVector fan ray) kernel σ τ aσ aτ]
  exact face_map_of_ray_mem projection (fanRayRealVector fan ray) kernel σ (σ ⊓ τ)
    (fan.inf_isFaceOf_left hσ hτ) ⟨aσ,aτ⟩

/-- The quotient star is a genuine finite toric fan in the actual
target lattice. The canonical quotient-lattice construction will
supply these compatible maps and their exact kernel. -/
def rayStarQuotient (targetLattice : IsIntegralLattice j) : Fan j :=
  Fan.ofCones targetLattice (rayStarSeedCones fan ray projection)
    (rayStarSeedCones_finite fan ray projection)
    (fun {_} member => rayStarSeedCones_isToricCone fan ray latticeMap projection compatible kernel member)
    (fun {_ _} first second => rayStarSeedCones_inf_isFaceOf fan ray projection kernel first second)

/-- Every cone of the quotient star is exactly a face of an actual
projected original cone containing the selected ray. -/
theorem mem_rayStarQuotient_iff (targetLattice : IsIntegralLattice j)
    (τ : PointedCone ℝ W) :
    τ ∈ (rayStarQuotient fan ray latticeMap projection compatible kernel targetLattice).cones ↔
      ∃ σ ∈ fan.cones, ray.toCone.val ≤ σ ∧
        τ.IsFaceOf (PointedCone.map projection σ) := by
  unfold rayStarQuotient
  rw [Fan.mem_ofCones_cones]
  constructor
  · rintro ⟨δ,⟨σ,⟨hσ,contains⟩,rfl⟩,face⟩
    exact ⟨σ,hσ,contains,face⟩
  · rintro ⟨σ,hσ,contains,face⟩
    exact ⟨PointedCone.map projection σ,⟨σ,⟨hσ,contains⟩,rfl⟩,face⟩

theorem rayStarImage_mem (targetLattice : IsIntegralLattice j)
    (σ : PointedCone ℝ V) (member : σ ∈ fan.cones) (contains : ray.toCone.val ≤ σ) :
    PointedCone.map projection σ ∈
      (rayStarQuotient fan ray latticeMap projection compatible kernel targetLattice).cones :=
  (mem_rayStarQuotient_iff fan ray latticeMap projection compatible kernel targetLattice _).mpr
    ⟨σ,member,contains,PointedCone.IsFaceOf.refl _⟩

instance (targetLattice : IsIntegralLattice j) :
    Nonempty (rayStarQuotient fan ray latticeMap projection compatible kernel targetLattice).cones :=
  ⟨⟨_,rayStarImage_mem fan ray latticeMap projection compatible kernel targetLattice
    ray.toCone.val ray.toCone.property le_rfl⟩⟩

end ToricPower.FanSubdivision
end
