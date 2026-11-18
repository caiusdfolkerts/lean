module

public import ToricPower.FanRayCoordinates
public import ToricPower.IntegralPiecewiseFanRefinement

/-!
# Integral piecewise projection onto a selected set of fan rays

On each regular cone, the selected primitive rays are fixed and all other
primitive rays are killed. The extending integral basis supplies the map
on the entire lattice. Although those ambient extensions need not agree,
their real extensions agree on every actual cone intersection.
-/

@[expose] public noncomputable section
open TauCeti.Toric Set
open scoped BigOperators Classical

namespace ToricPower.FanSubdivision

variable {N V P : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup P] {i : N →+ V}

theorem regularCone_exists_addHom_ray_values (lattice : IsIntegralLattice i)
    {σ : PointedCone ℝ V} (regular : IsRegularCone i σ) (values : ToricRay σ → P) :
    ∃ mapping : N →+ P, ∀ ρ : ToricRay σ,
      mapping (primitiveGenerator lattice regular.toIsToricCone ρ) = values ρ := by
  obtain ⟨l,basis,primitive⟩ := regular.exists_basis_sum
  refine ⟨(basis.constr ℤ (Sum.elim values (fun _ : Fin l => 0))).toAddMonoidHom,?_⟩
  intro ρ
  rw [← (primitive ρ).eq_primitiveGenerator lattice regular.toIsToricCone]
  simp

variable (fan : Fan i) (regular : fan.IsRegular) (keep : fan.Ray → Prop)

def raySelectionLatticeMap (σ : fan.cones) : N →+ N := by
  classical
  exact (regularCone_exists_addHom_ray_values fan.lattice
    (Fan.isRegular_iff.mp regular σ.val σ.property)
    (fun ρ => if keep (Fan.Ray.ofToricRay fan σ ρ)
      then primitiveGenerator fan.lattice (fan.isToricCone σ.property) ρ else 0)).choose

theorem raySelectionLatticeMap_local (σ : fan.cones) (ρ : ToricRay σ.val) :
    raySelectionLatticeMap fan regular keep σ
        (primitiveGenerator fan.lattice (fan.isToricCone σ.property) ρ) =
      if keep (Fan.Ray.ofToricRay fan σ ρ)
        then primitiveGenerator fan.lattice (fan.isToricCone σ.property) ρ else 0 := by
  classical
  exact (regularCone_exists_addHom_ray_values fan.lattice
    (Fan.isRegular_iff.mp regular σ.val σ.property)
    (fun ρ => if keep (Fan.Ray.ofToricRay fan σ ρ)
      then primitiveGenerator fan.lattice (fan.isToricCone σ.property) ρ else 0)).choose_spec ρ

theorem raySelectionLatticeMap_ray (σ : fan.cones) (ρ : fan.Ray) (below : ρ.toCone ≤ σ) :
    raySelectionLatticeMap fan regular keep σ (fanRayPrimitiveGenerator fan ρ) =
      if keep ρ then fanRayPrimitiveGenerator fan ρ else 0 := by
  classical
  have localValue := raySelectionLatticeMap_local fan regular keep σ (ρ.toToricRay fan σ below)
  rw [← fanRayPrimitiveGenerator_ofToricRay] at localValue
  exact localValue

def raySelectionRealMap (σ : fan.cones) : V →ₗ[ℝ] V :=
  fan.lattice.extend i (raySelectionLatticeMap fan regular keep σ)

theorem raySelectionRealMap_ray (σ : fan.cones) (ρ : fan.Ray) (below : ρ.toCone ≤ σ) :
    raySelectionRealMap fan regular keep σ (fanRayRealVector fan ρ) =
      if keep ρ then fanRayRealVector fan ρ else 0 := by
  classical
  change fan.lattice.extend i (raySelectionLatticeMap fan regular keep σ)
    (i (fanRayPrimitiveGenerator fan ρ)) = _
  rw [fan.lattice.extend_apply,raySelectionLatticeMap_ray fan regular keep σ ρ below]
  split_ifs <;> simp [fanRayRealVector]

theorem linearMaps_agree_on_fanCone (σ : fan.cones) (first second : V →ₗ[ℝ] V)
    (rays : ∀ ρ : fan.Ray, ρ.toCone ≤ σ →
      first (fanRayRealVector fan ρ) = second (fanRayRealVector fan ρ))
    {x : V} (member : x ∈ σ.val) : first x = second x := by
  have contained : σ.val ≤ PointedCone.ofSubmodule (first-second).ker := by
    rw [← localRay_hull fan σ]
    apply Submodule.span_le.mpr
    rintro _ ⟨ρ,rfl⟩
    exact sub_eq_zero.mpr (rays (Fan.Ray.ofToricRay fan σ ρ)
      (Fan.Ray.toCone_ofToricRay_le fan σ ρ))
  exact sub_eq_zero.mp (contained member)

theorem raySelectionRealMap_compatible (σ τ : fan.cones) (x : V)
    (member : x ∈ σ.val ⊓ τ.val) :
    raySelectionRealMap fan regular keep σ x = raySelectionRealMap fan regular keep τ x := by
  apply linearMaps_agree_on_fanCone fan (σ ⊓ τ) _ _ ?_ member
  intro ρ below
  rw [raySelectionRealMap_ray fan regular keep σ ρ (below.trans inf_le_left),
    raySelectionRealMap_ray fan regular keep τ ρ (below.trans inf_le_right)]

theorem raySelectionRealMap_zero (σ : fan.cones)
    (discard : ∀ ρ : fan.Ray, ρ.toCone ≤ σ → ¬ keep ρ)
    {x : V} (member : x ∈ σ.val) : raySelectionRealMap fan regular keep σ x = 0 := by
  change raySelectionRealMap fan regular keep σ x = (0 : V →ₗ[ℝ] V) x
  apply linearMaps_agree_on_fanCone fan σ _ _ ?_ member
  intro ρ below
  rw [raySelectionRealMap_ray fan regular keep σ ρ below,if_neg (discard ρ below)]
  rfl

/-- Vanishing discarded ray coefficients is exactly the condition needed
for a point to be fixed; no assertion about a neighbourhood is assumed. -/
theorem raySelectionRealMap_fixed_of_coordinates (σ : fan.cones) {x : V}
    (member : x ∈ σ.val)
    (discardedZero : ∀ ρ : fan.Ray, ¬ keep ρ → localFanRayCoordinates fan σ x ρ = 0) :
    raySelectionRealMap fan regular keep σ x = x := by
  classical
  let c := localFanRayCoordinates fan σ x
  have evaluate : fanRayCombination fan c = x :=
    (localFanRayCoordinates_profile fan regular σ member).2.choose_spec.2
  have support := localFanRayCoordinates_supported fan σ x
  rw [← evaluate,fanRayCombination,Finsupp.linearCombination_apply,Finsupp.sum,map_sum]
  apply Finset.sum_congr rfl
  intro ρ supported
  rw [map_smul,raySelectionRealMap_ray fan regular keep σ ρ (support ρ supported)]
  by_cases selected : keep ρ
  · rw [if_pos selected]
  · rw [if_neg selected,show c ρ = 0 from discardedZero ρ selected,zero_smul,zero_smul]

theorem linearMap_maps_fanCone (σ : fan.cones) (mapping : V →ₗ[ℝ] V)
    (rays : ∀ ρ : fan.Ray, ρ.toCone ≤ σ → mapping (fanRayRealVector fan ρ) ∈ σ.val)
    {x : V} (member : x ∈ σ.val) : mapping x ∈ σ.val := by
  have contained : σ.val ≤ PointedCone.comap mapping σ.val := by
    conv_lhs => rw [← localRay_hull fan σ]
    apply Submodule.span_le.mpr
    rintro _ ⟨ρ,rfl⟩
    apply PointedCone.mem_comap.mpr
    exact rays (Fan.Ray.ofToricRay fan σ ρ) (Fan.Ray.toCone_ofToricRay_le fan σ ρ)
  exact PointedCone.mem_comap.mp (contained member)

theorem kernel_inter_cone_isFaceOf (cone : PointedCone ℝ V) (salient : cone.toConvexCone.Salient)
    (mapping : V →ₗ[ℝ] V) (preserves : ∀ x ∈ cone, mapping x ∈ cone) :
    (cone ⊓ PointedCone.ofSubmodule mapping.ker).IsFaceOf cone := by
  refine ⟨inf_le_left,?_⟩
  intro x y r hx hy positive combined
  refine ⟨hx,?_⟩
  change mapping x = 0
  by_contra nonzero
  have total : r • mapping x + mapping y = 0 := by
    have zero : mapping (r • x+y) = 0 := combined.2
    rw [map_add,map_smul] at zero
    exact zero
  have value : mapping y = -(r • mapping x) := by
    apply eq_neg_iff_add_eq_zero.mpr
    simpa only [add_comm] using total
  have negativeMember := cone.smul_mem (inv_nonneg.mpr positive.le) (preserves y hy)
  rw [value,smul_neg,smul_smul,inv_mul_cancel₀ positive.ne',one_smul] at negativeMember
  exact salient (mapping x) (preserves x hx) nonzero negativeMember

/-- The points fixed by ray selection form an actual face of each cone. -/
theorem raySelectionRealMap_fixedFace (σ : fan.cones) :
    (σ.val ⊓ PointedCone.ofSubmodule
      (LinearMap.id-raySelectionRealMap fan regular keep σ).ker).IsFaceOf σ.val := by
  apply kernel_inter_cone_isFaceOf σ.val (fan.isToricCone σ.property).salient
  intro x member
  apply linearMap_maps_fanCone fan σ _ ?_ member
  intro ρ below
  simp only [LinearMap.sub_apply,LinearMap.id_apply,
    raySelectionRealMap_ray fan regular keep σ ρ below]
  split_ifs
  · simpa only [sub_self] using σ.val.zero_mem
  · simpa only [sub_zero] using below (fanRayRealVector_mem fan ρ)

end ToricPower.FanSubdivision
end
