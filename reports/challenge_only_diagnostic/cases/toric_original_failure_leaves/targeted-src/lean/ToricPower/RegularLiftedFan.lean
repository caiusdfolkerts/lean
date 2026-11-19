module

public import ToricPower.FanLiftedConeProfiles
public import ToricPower.PrimitiveQuotientBasisLift

/-!
# A genuine regular fan above a regular quotient fan

One integral lift is fixed for each quotient ray. Every lifted cone
contains the original positive kernel ray. Arbitrary choices of the
lifts preserve regularity: a quotient basis lifts to an integral basis
after adjoining the primitive kernel vector. The fan intersection axioms
are those proved by the actual nonnegative-profile calculation.
-/

@[expose] public noncomputable section

open TauCeti TauCeti.Toric
namespace ToricPower.FanSubdivision

variable {N P V W : Type*} [AddCommGroup N] [AddCommGroup P]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  {i : N →+ V} {j : P →+ W}
  (sourceLattice : IsIntegralLattice i) (fan : Fan j) (regular : fan.IsRegular)
  (a : N) (primitive : IsPrimitive a) (latticeProjection : N →ₗ[ℤ] P)
  (kernel : latticeProjection.ker = Submodule.span ℤ {a})
  (surjective : Function.Surjective latticeProjection)
  (lifts : fan.Ray → N)
  (projects : ∀ ρ, latticeProjection (lifts ρ) = fanRayPrimitiveGenerator fan ρ)

include sourceLattice primitive kernel surjective projects regular in
/-- Every actual cone above the quotient fan is regular in the
original integral lattice. -/
theorem liftedCone_isRegular (σ : fan.cones) :
    IsRegularCone i (liftedCone fan (i a) (fun ρ => i (lifts ρ)) σ) := by
  classical
  have regularCone := Fan.isRegular_iff.mp regular σ.val σ.property
  obtain ⟨m,basis,basisExtends⟩ := regularCone.exists_basis_sum
  let integralLifts : (ToricRay σ.val ⊕ Fin m) → N := Sum.elim
    (fun ρ => lifts (Fan.Ray.ofToricRay fan σ ρ))
    (fun k => (surjective (basis (.inr k))).choose)
  have integralProjects : ∀ k, latticeProjection (integralLifts k) = basis k := by
    rintro (ρ | k)
    · change latticeProjection (lifts (Fan.Ray.ofToricRay fan σ ρ)) = basis (.inl ρ)
      rw [projects,fanRayPrimitiveGenerator_ofToricRay]
      exact (basisExtends ρ).eq_primitiveGenerator fan.lattice regularCone.toIsToricCone |>.symm
    · exact (surjective (basis (.inr k))).choose_spec
  let liftedBasis : Module.Basis (PUnit.{1} ⊕ (ToricRay σ.val ⊕ Fin m)) ℤ N :=
    liftedQuotientBasis latticeProjection a kernel basis integralLifts
    integralProjects primitive
  let active : Set (PUnit.{1} ⊕ (ToricRay σ.val ⊕ Fin m)) :=
    Set.range Sum.inl ∪ Set.range (fun ρ : ToricRay σ.val => Sum.inr (Sum.inl ρ))
  have generatorSet : liftedBasis '' active =
      {a} ∪ lifts '' {ρ : fan.Ray | ρ.toCone ≤ σ} := by
    ext n
    constructor
    · rintro ⟨k,(⟨u,rfl⟩ | ⟨ρ,rfl⟩),rfl⟩
      · exact Or.inl (liftedQuotientBasis_inl latticeProjection a kernel basis integralLifts
          integralProjects primitive u)
      · apply Or.inr
        refine ⟨Fan.Ray.ofToricRay fan σ ρ,Fan.Ray.toCone_ofToricRay_le fan σ ρ,?_⟩
        exact (liftedQuotientBasis_inr latticeProjection a kernel basis integralLifts
          integralProjects primitive (.inl ρ)).symm
    · rintro (same | ⟨ρ,below,rfl⟩)
      · exact ⟨.inl PUnit.unit,Or.inl ⟨PUnit.unit,rfl⟩,
          (liftedQuotientBasis_inl latticeProjection a kernel basis integralLifts
            integralProjects primitive PUnit.unit).trans same.symm⟩
      · let localRay := ρ.toToricRay fan σ below
        refine ⟨.inr (.inl localRay),Or.inr ⟨localRay,rfl⟩,?_⟩
        exact liftedQuotientBasis_inr latticeProjection a kernel basis integralLifts
          integralProjects primitive (.inl localRay)
  have coneEq : PointedCone.hull ℝ (i '' (liftedBasis '' active)) =
      liftedCone fan (i a) (fun ρ => i (lifts ρ)) σ := by
    rw [generatorSet,Set.image_union,Set.image_singleton,Set.image_image]
    exact Submodule.span_union _ _
  rw [← coneEq]
  exact isRegularCone_hull_image_basis sourceLattice liftedBasis active

variable (projection : V →ₗ[ℝ] W)
  (compatible : ∀ n, projection (i n) = j (latticeProjection n))

include kernel compatible in
theorem liftedFan_kernelVector : projection (i a) = 0 := by
  rw [compatible,primitiveKernel_generator_eq_zero latticeProjection a kernel,map_zero]

include projects compatible in
theorem liftedFan_ray_projects (ρ : fan.Ray) :
    projection (i (lifts ρ)) = fanRayRealVector fan ρ := by
  rw [compatible,projects]
  rfl

/-- The fan consists of every face of every actual lifted cone. -/
def regularLiftedFan : Fan i :=
  Fan.ofCones sourceLattice
    (Set.range (liftedCone fan (i a) (fun ρ => i (lifts ρ)))) (Set.finite_range _)
    (by
      rintro _ ⟨σ,rfl⟩
      exact (liftedCone_isRegular sourceLattice fan regular a primitive latticeProjection
        kernel surjective lifts projects σ).toIsToricCone)
    (by
      rintro _ _ ⟨σ,rfl⟩ ⟨τ,rfl⟩
      exact liftedCone_inf_isFaceOf fan (i a) (fun ρ => i (lifts ρ)) projection
        (liftedFan_kernelVector a latticeProjection kernel projection compatible)
        (liftedFan_ray_projects fan latticeProjection lifts projects projection compatible) σ τ)

theorem mem_regularLiftedFan_iff (δ : PointedCone ℝ V) :
    δ ∈ (regularLiftedFan sourceLattice fan regular a primitive latticeProjection kernel
      surjective lifts projects projection compatible).cones ↔
      ∃ σ : fan.cones, δ.IsFaceOf (liftedCone fan (i a) (fun ρ => i (lifts ρ)) σ) := by
  unfold regularLiftedFan
  rw [Fan.mem_ofCones_cones]
  constructor
  · rintro ⟨_,⟨σ,rfl⟩,face⟩
    exact ⟨σ,face⟩
  · rintro ⟨σ,face⟩
    exact ⟨_,⟨σ,rfl⟩,face⟩

theorem regularLiftedFan_isRegular :
    (regularLiftedFan sourceLattice fan regular a primitive latticeProjection kernel
      surjective lifts projects projection compatible).IsRegular := by
  rw [Fan.isRegular_iff]
  intro δ member
  obtain ⟨σ,face⟩ := (mem_regularLiftedFan_iff sourceLattice fan regular a primitive latticeProjection
    kernel surjective lifts projects projection compatible δ).mp member
  exact (liftedCone_isRegular sourceLattice fan regular a primitive latticeProjection
    kernel surjective lifts projects σ).of_isFaceOf face

end ToricPower.FanSubdivision
end
